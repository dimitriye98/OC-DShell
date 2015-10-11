local component = require("component")
local computer = require("computer")
local event = require("event")
local fs = require("filesystem")
local process = require("process")
local shell = require("shell")
local term = require("term")
local text = require("text")
local unicode = require("unicode")

-------------------------------------------------------------------------------

local memoryStream = {}

function memoryStream:close()
	self.closed = true
end

function memoryStream:seek()
	return nil, "bad file descriptor"
end

function memoryStream:read(n)
	if self.closed then
		if self.buffer == "" and self.redirect.read then
			return self.redirect.read:read(n)
		else
			return nil -- eof
		end
	end
	if self.buffer == "" then
		self.args = table.pack(coroutine.yield(table.unpack(self.result)))
	end
	local result = string.sub(self.buffer, 1, n)
	self.buffer = string.sub(self.buffer, n + 1)
	return result
end

function memoryStream:write(value)
	if not self.redirect.write and self.closed then
		-- if next is dead, ignore all writes
		if coroutine.status(self.next) ~= "dead" then
			error("attempt to use a closed stream")
		end
		return true
	end
	if self.redirect.write then
		self.redirect.write:write(value)
	end
	if not self.closed then
		self.buffer = self.buffer .. value
		self.result = table.pack(coroutine.resume(self.next, table.unpack(self.args)))
		if coroutine.status(self.next) == "dead" then
			self:close()
		end
		if not self.result[1] then
			error(self.result[2], 0)
		end
		table.remove(self.result, 1)
	end
	return true
end

function memoryStream.new()
	local stream = {closed = false, buffer = "",
	                redirect = {}, result = {}, args = {}}
	local metatable = {__index = memoryStream,
	                   __gc = memoryStream.close,
	                   __metatable = "memorystream"}
	return setmetatable(stream, metatable)
end

-------------------------------------------------------------------------------

local function clone(tbl, deep)
	local out = {}
	for k, v in pairs(tbl) do
		if deep and type(v) == "table" then
			out[k] = clone(v, true)
		else
			out[k] = v
		end
	end
	return out
end

local function contains(tbl, elem)
	for _, v in pairs(tbl) do
		if elem == v then
			return true
		end
	end
	return false
end

-- Takes a string and escapes it so that it can serve as a pattern literal
local function litPattern(str)
	return str:gsub("%W", "%%%0")
end

local operators = {"&&", "||", ";", "\n", "|"} -- must be ordered from long to short

local quotes = {
	"${", "$(", '"', "'", "`"; -- array part must be ordered from long to short
	['"']   = '"',
	["'"]   = "'",
	["${"]  = "}",
	["$("]  = ")",
	["`"]   = "`",
--	["$(("] = "))"
}

local function tokenize(value)
	checkArg(1, value, "string")

	local i = 0
	local len = unicode.len(value)

	local function consume(n)
		if type(n) == "string" then -- try to consume a predefined token
			local begin = i + 1
			local final = i + unicode.len(n)
			local sub = unicode.sub(value, begin, final)

			if sub == n then
				i = final
				return sub
			else
				return nil
			end
		elseif type(n) ~= "number" then -- for for loop iteration
			n = 1
		end
		if len - i <= 0 then
			return nil
		end
		n = math.min(n, len - i)
		local begin = i + 1
		i = i + n
		return unicode.sub(value, begin, i)
	end

	local function lookahead(n)
		if type(n) ~= "number" then
			n = 1
		end
		n = math.min(n, len - i)
		local begin = i + 1
		local final = i + n
		if final - i <= 0 then
			return nil
		end
		return unicode.sub(value, begin, final)
	end

	local tokens, token = {}, {}
	local start, quoted
	local lastOp
	while lookahead() do
		local char = lookahead()
		local closed
		if quoted then
			closed = consume(quotes[quoted])
		end
		if closed then
			table.insert(token, closed)
			quoted = nil
		elseif quoted == "'" then
			table.insert(token, consume(char))
		elseif char == "\\" then
			table.insert(token, consume(2)) -- backslashes will be removed later
		elseif not quoted then
			local opened
			for _, quote in ipairs(quotes) do
				opened = consume(quote)
				if opened then
					table.insert(token, opened)
					quoted = opened
					start = i + 1
					break
				end
			end
			if not opened then
				local isOp
				for _, op in ipairs(operators) do
					isOp = consume(op)
					if isOp then
						local tokenOut = table.concat(token)
						if tokenOut == "" then
							if tokens[#tokens] == lastOp then
								return nil, "parse error near '"..isOp.."'"
							end
						else
							table.insert(tokens, tokenOut)
						end
						table.insert(tokens, isOp)
						token = {}
						lastOp = isOp
						break
					end
				end
				if not isOp then
					if char == "#" then -- comment
						while lookahead() ~= "\n" do
							consume()
						end
					elseif char:match("%s") then
						local tokenOut = table.concat(token)
						if tokenOut ~= "" then
							table.insert(tokens, table.concat(token))
							token = {}
						end
						consume(char)
					else
						table.insert(token, consume(char))
					end
				end
			end
		else
			table.insert(token, consume(char))
		end
	end
	if quoted then
		return nil, "unclosed quote at index " .. start, quoted
	end
	token = table.concat(token)
	if token ~= "" then -- insert trailing token
		table.insert(tokens, token)
	end
	return tokens
end

local function nilify(word)
	if word == "" then
		return nil
	else
		return word
	end
end

local paramOps = {
	[":-"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if nilify(value) then
			return value
		else
			return word
		end
	end,
	["-"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if value then
			return nilify(value)
		else
			return word
		end
	end,
	[":="] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if nilify(value) then
			return value
		else
			os.setenv(param, word)
			return word
		end
	end,
	["="] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if value then
			return nilify(value)
		else
			return word
		end
	end,
	[":?"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if nilify(value) then
			return value
		else
			error(word)
		end
	end,
	["?"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if value then
			return nilify(value)
		else
			error(word)
		end
	end,
	[":+"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if nilify(value) then
			return word
		else
			return nil
		end
	end,
	["+"] = function(param, word)
		nilify(word)
		local value = os.getenv(param)
		if value then
			return word
		else
			return nil
		end
	end
}

local function paramOpPatt(op)
	return "(.-)"..op:gsub("%W", "%%%0").."(.*)"
end

local expand -- forward declaration for mutual recursion
local function paramExpand(contents)
	for op, handler in pairs(paramOps) do
		local param, word = contents:match(paramOpPatt(op))
		if param then
			if not param:match("%w+") then
				error("bad substitution")
			end
			return handler(param, expand(word))
		end
	end
	return os.getenv(contents)
end

expand = function(value)
	local result = value:gsub("%$(%w+)", os.getenv):gsub("%$%b{}",
		function(match)
			local contents = unicode.sub(match, 3, -2)
			if unicode.sub(contents, 1, 1) == "#" then
				return tostring(unicode.len(paramExpand(unicode.sub(contents, 2)) or ""))
			else
				return paramExpand(contents) or match
			end
		end)
	return result
end

local function glob(value)
	if not value:match("[^\\]%*") and not value:match("[^\\]%?") then
		-- Nothing to do here.
		return {expand(value)}
	end
	local segments = fs.segments(value)
	local paths = {value:sub(1, 1) == "/" and "/" or shell.getWorkingDirectory()}
	for i, segment in ipairs(segments) do
		local nextPaths = {}
		local pattern = segment:gsub("([^\\])%*", "%1.*")
		                       :gsub("^%*", ".*")
		                       :gsub("([^\\])%?", "%1.")
		                       :gsub("^%?", ".")
		if pattern == segment then
			-- Nothing to do, concatenate as-is.
			for _, path in ipairs(paths) do
				table.insert(nextPaths, fs.concat(path, segment))
			end
		else
			pattern = "^(" .. pattern .. ")/?$"
			for _, path in ipairs(paths) do
				for file in fs.list(path) do
					if file:match(pattern) then
						table.insert(nextPaths, fs.concat(path, file))
					end
				end
			end
			if #nextPaths == 0 then
				error("no matches found: " .. segment)
			end
		end
		paths = nextPaths
	end
	for i, path in ipairs(paths) do
		paths[i] = expand(path)
	end
	return paths
end

local function consumeQuote(str, open, close)
	checkArg(1, str, "string")
	checkArg(2, open, "string")
	checkArg(3, close, "string")
	if str:sub(1, #open) ~= open then
		return nil, str
	else
		local quoted, rest = str:sub(#open + 1):match("(.-[^\\]"..close:gsub("%W", "%%%0")..")(.*)")
		if not quoted then
			return nil, str
		end
		return open..quoted, rest
	end
end

local function evaluate(value)
	local results, remaining = {""}, value
	while remaining ~= "" do
		local match, rest = consumeQuote(remaining, "'", "'")
		if match then -- single quotes; no nested expansion
			match = match:sub(2, -2)
			remaining = rest
			for i,v in ipairs(results) do
				results[i] = v..match
			end
		else
			match, rest = consumeQuote(remaining, '"', '"')
			if match then
				match = match:sub(2, -2)
				remaining = rest
			else
				match, rest = rest:match("(.-[^\\])([\"'].*)")
				if match then -- consume until quote
					remaining = rest
				else -- if there's no opening quote consume the rest
					match = remaining
					remaining = ""
				end
			end
			local newResults = {}
			for _, globbed in ipairs(glob(match)) do
				for i, result in ipairs(results) do
					table.insert(newResults, result..globbed)
				end
			end
			results = newResults
		end
	end

	-- finally strip the backslashes
	for i,v in ipairs(results) do
		results[i] = v:gsub("\\(.)", "%1")
	end
	return results
end

local function parseParams(...)
	local params = table.pack(...)
	local disables
	if type(params[1]) == "table" then
		disables = table.remove(params, 1)
	end
	local args = {}
	local options = {}
	local doneWithOptions = false
	for i = 1, params.n do
		local param = params[i]
		if not doneWithOptions and type(param) == "string" then
			if param == "--" then
				doneWithOptions = true -- stop processing options at `--`
			elseif unicode.sub(param, 1, 2) == "--" then
				if param:match("%-%-(.-)=") ~= nil then
					options[param:match("%-%-(.-)=")] = param:match("=(.*)")
				else
					options[unicode.sub(param, 3)] = true
					if disables then
						local disable = disables[unicode.sub(param, 3)]
						if disable then
							if type(disable) == "string" then
								options[disable] = nil
							elseif type(disable) == "table" then
								for _,flag in disable do
									options[flag] = nil
								end
							end
						end
					end
				end
			elseif unicode.sub(param, 1, 1) == "-" and param ~= "-" then
				for j = 2, unicode.len(param) do
					options[unicode.sub(param, j, j)] = true
					if disables then
						local disable = disables[unicode.sub(param, j, j)]
						if disable then
							if type(disable) == "string" then
								options[disable] = nil
							elseif type(disable) == "table" then
								for _,flag in disable do
									options[flag] = nil
								end
							end
						end
					end
				end
			else
				table.insert(args, param)
			end
		else
			table.insert(args, param)
		end
	end
	return args, options
end

local esc = string.char(0x1B)
local builtIns = {
	[":"] = function() --[[ Do nothing ]] end;
	["source"] = function(_, output, env, fName, ...)
		local ret = {eval(io.open(fName), output, env, table.concat({...}, " ") )}
		file:close()
		return table.unpack(ret)
	end;
	["eval"] = function(input, output, env, ...)
		return eval(input, output, env, table.concat({...}, " "))
	end;
	["exec"] = function(input, output, env, ...)
		-- Unfortunately the flag options seem impossible to implement given
		-- the way the process library currently works
		local success, code = eval(input, output, env, table.concat({...}, " "))
		if success then
			os.exit(code)
		else
			error(code)
		end
	end;
	["echo"] = function(input, output, env, ...)
		local args = parseParams({e="E", E="e"}, ...)
		local defaultEscapes = os.getenv("echoEscapes")
		if defaultEscapes == "false" then
			defaultEscapes = false
		else
			defaultEscapes = true
		end
		local str = table.concat(args, " ")
		if defaultEscapes and (not args.E) or args.e then
			local out, escaped, i = {}, false, 0
			while i < unicode.len(str) do
				i = i + 1
				local char = unicode.sub(str, i, i)
				if escaped then
					if char == "b" then
						table.remove(out)
					elseif char == "c" then
						break
					elseif char == "e" or char == "E" then
						table.insert(out, esc)
					elseif char == "f" then
						table.insert(out, "\f")
					elseif char == "n" then
						table.insert(out, "\n")
					elseif char == "r" then
						table.insert(out, "\r")
					elseif char == "t" then
						table.insert(out, "\t")
					elseif char == "v" then
						table.insert(out, "\v")
					elseif char == "\\" then
						table.insert(out, "\\")
					elseif char == "0" then
						local code = tonumber(unicode.sub(str, i+1, i+3), 8)
						if code then
							table.insert(out, unicode.char(code))
							i = i + 3
						else
							table.insert(out, "\\")
							table.insert(out, "0")
						end
					elseif char == "x" then
						local code = tonumber(unicode.sub(str, i+1, i+2), 16)
						if code then
							table.insert(out, unicode.char(code))
							i = i + 2
						else
							table.insert(out, "\\")
							table.insert(out, "x")
						end
					elseif char == "u" then
						local code = str:match("%x%x%x%x") -- 4 hexdecimal digits
						if code then
							i = i + 4
							code = tonumber(code, 16)
							table.insert(out, unicode.char(code))
						else
							table.insert(out, "\\")
							table.insert(out, "u")
						end
					elseif char == "U" then
						local code = str:match("%x%x%x%x%x%x%x%x") -- 8 hexdecimal digits
						if code then
							i = i + 8
							code = tonumber(code, 16)
							table.insert(out, unicode.char(code))
						else
							table.insert(out, "\\")
							table.insert(out, "u")
						end
					else
						table.insert(out, "\\")
						table.insert(out, char)
					end
					escaped = false
				else
					if char == "\\" then
						escaped = true
					else
						table.insert(out, char)
					end
				end
			end
			str = table.concat(out)
		end
		output:write(str)
		if not args.n then
			output:write("\n")
		end
	end,
	["exit"] = true -- Exit needs special processing
}

local function parseCommand(tokens, ...)
	if #tokens == 0 then
		return
	end

	local name = tokens[1]
	local program, args = shell.resolveAlias(name, table.pack(select(2, table.unpack(tokens))))

	local eargs = {}
	program = evaluate(program)
	for i = 2, #program do
		table.insert(eargs, program[i])
	end
	local reason
	if builtIns[program[1]] then
		program = program[1]
	else
		program, reason = shell.resolve(program[1], "lua")
		if not program then
			return nil, reason
		end
	end
	for i = 1, #args do
		for _, arg in ipairs(evaluate(args[i])) do
			table.insert(eargs, arg)
		end
	end
	args = eargs

	-- Find redirects.
	local input, output, mode = nil, nil, "write"
	tokens = args
	args = {}
	local function smt(call) -- state metatable factory
		local function index(_, token)
			if token == "<" or token == ">" or token == ">>" then
				return "parse error near " .. token
			end
			call(token)
			return "args" -- default, return to normal arg parsing
		end
		return {__index=index}
	end
	local sm = { -- state machine for redirect parsing
		args   = setmetatable({["<"]="input", [">"]="output", [">>"]="append"},
		                          smt(function(token)
		                                table.insert(args, token)
		                              end)),
		input  = setmetatable({}, smt(function(token)
		                                input = token
		                              end)),
		output = setmetatable({}, smt(function(token)
		                                output = token
		                                mode = "write"
		                              end)),
		append = setmetatable({}, smt(function(token)
		                                output = token
		                                mode = "append"
		                              end))
	}
	-- Run state machine over tokens.
	local state = "args"
	for i = 1, #tokens do
		local token = tokens[i]
		state = sm[state][token]
		if not sm[state] then
			return nil, state
		end
	end
	return {
		program = program,
		args    = args,
		input   = input,
		output  = output,
		mode    = mode,
		name    = name
	}
end

local function parseCommands(command)
	local tokens, reason, quote = tokenize(command)
	if not tokens then
		return nil, reason, quote
	elseif #tokens == 0 then
		return true
	end

	local commands, command = {}, {}
	local joinOps = {
		["|"]  = "pipe",
		["&&"] = "and",
		["||"] = "or",
		[";"]  = "delim",
		["\n"] = "delim"
	}
	local lastJoin = "pipe" -- First element is treated as if preceded by a
	                        -- pipe, makes pipeline construction easier
	for _, token in ipairs(tokens) do
		local join = joinOps[token]
		if join then
			if #command == 0 then
				return nil, "parse error near '"..token.."'"
			end
			table.insert(commands, {op = lastJoin, command = command})
			lastJoin = join
			command = {}
		else
			table.insert(command, token)
		end
	end
	if #command > 0 then -- push tail command
		table.insert(commands, {op = lastJoin, command = command})
	end

	for i, joinCell in pairs(commands) do
		local reason
		joinCell.command, reason = parseCommand(joinCell.command)
		if not joinCell.command then
			return nil, reason
		end
		if joinCell.command.program == nil then
			return nil, joinCell.command[2]
		end
	end

	return commands
end

-------------------------------------------------------------------------------

local function runPipeline(input, output, env, pipeline, ...)
	if pipeline[1].program == "exit" then
		-- If the first command exits further
		-- processing is unnecessary.
		local code = pipeline[1].args[1]
		os.exit(tonumber(code) or code)
	end

	input  = input or io.input()
	output = output or io.output()

	-- Piping data between programs works like so:
	-- program1 gets its output replaced with our custom stream.
	-- program2 gets its input replaced with our custom stream.
	-- repeat for all programs
	-- custom stream triggers execution of 'next' program after write.
	-- custom stream triggers yield before read if buffer is empty.
	-- custom stream may have 'redirect' entries for fallback/duplication.
	local threads, pipes, inputs, outputs = {}, {}, {}, {}
	for i = 1, #pipeline do
		local command = pipeline[i]
		if command.program == "exit" then
			threads[i] = {"exit", tonumber(command.args[1]) or command.args[1]}
			break
		end
		local builtIn = builtIns[command.program]
		if builtIn then
			threads[i] = coroutine.create(function(...)
				local input, output = input, output
				if command.input then
					local file, reason = io.open(shell.resolve(command.input))
					if not file then
						error("could not open '" .. command.input .. "': " .. reason, 0)
					end
					table.insert(inputs, file)
					if i > 1 and pipes[i - 1] then
						pipes[i - 1].stream.redirect.read = file
						input = pipes[i - 1]
					else
						input = file
					end
				elseif pipes[i - 1] then
					input = pipes[i - 1]
				end
				if command.output then
					local file, reason = io.open(shell.resolve(command.output), command.mode == "append" and "a" or "w")
					if not file then
						error("could not open '" .. command.output .. "': " .. reason, 0)
					end
					if command.mode == "append" then
						io.write("\n")
					end
					table.insert(outputs, file)
					if i < #pipeline and pipes[i] then
						pipes[i].stream.redirect.write = file
						output = pipes[i]
					else
						output = file
					end
				elseif pipes[i] then
					output = pipes[i]
				end
				output.write("")
				return builtIn(input, output, env, ...)
			end)
		else
			local reason
			threads[i], reason = process.load(command.program, env, function()
				os.setenv("_", command.program)
				if command.input then
					local file, reason = io.open(shell.resolve(command.input))
					if not file then
						error("could not open '" .. command.input .. "': " .. reason, 0)
					end
					table.insert(inputs, file)
					if i > 1 and pipes[i - 1] then
						pipes[i - 1].stream.redirect.read = file
						io.input(pipes[i - 1])
					else
						io.input(file)
					end
				elseif pipes[i - 1] then
					io.input(pipes[i - 1])
				end
				if command.output then
					local file, reason = io.open(shell.resolve(command.output), command.mode == "append" and "a" or "w")
					if not file then
						error("could not open '" .. command.output .. "': " .. reason, 0)
					end
					if command.mode == "append" then
						io.write("\n")
					end
					table.insert(outputs, file)
					if i < #pipeline and pipes[i] then
						pipes[i].stream.redirect.write = file
						io.output(pipes[i])
					else
						io.output(file)
					end
				elseif pipes[i] then
					io.output(pipes[i])
				end
				io.write('')
			end, command.name)
		end
		if not threads[i] then
			return false, reason
		end

		if i < #pipeline and pipeline[i + 1].program ~= "exit" then
			pipes[i] = require("buffer").new("rw", memoryStream.new())
			pipes[i]:setvbuf("no")
		else
			pipes[i] = output
		end
		if i > 1 then
			pipes[i - 1].stream.next = threads[i]
			pipes[i - 1].stream.args = command.args
		else
			pipes[i - 1] = input
		end
	end

	local args = pipeline[1].args
	for _, arg in ipairs(table.pack(...)) do
		table.insert(args, arg)
	end
	table.insert(args, 1, true)
	args.n = #args
	local result = nil
	for i = 1, #threads do
		if type(threads[i]) == "table" and threads[i][1] == "exit" then -- Exit logic
			os.exit(threads[i][2])
		end

		-- Emulate CC behavior by making yields a filtered event.pull()
		while args[1] and coroutine.status(threads[i]) ~= "dead" do
			result = table.pack(coroutine.resume(threads[i], table.unpack(args, 2, args.n)))
			if coroutine.status(threads[i]) ~= "dead" then
				args = table.pack(pcall(event.pull, table.unpack(result, 2, result.n)))
			end
		end

		if pipes[i] then
			pcall(pipes[i].close, pipes[i])
		end

		if not result[1] then
			if type(result[2]) == "table" and result[2].reason == "terminated" then
				result[1] = true
				result[2] = result[2].code
				result.n = 2
			elseif type(result[2]) == "string" then
				result[2] = debug.traceback(threads[i], result[2])
				break
			end
		end
	end

	-- copy env vars from last process; mostly to ensure stuff like cd.lua works
	local lastVars = rawget(process.info(threads[#threads]).data, "vars")
	if lastVars then
		local localVars = process.info().data.vars
		for k,v in pairs(lastVars) do
			localVars[k] = v
		end
	end

	for _, input in ipairs(inputs) do
		input:close()
	end
	for _, output in ipairs(outputs) do
		output:close()
	end

	if not args[1] then
		return false, args[2]
	end
	return table.unpack(result, 1, result.n)
end

local function eval(input, output, env, command, ...)
	checkArg(4, command, "string")
	local commands, reason, quote = parseCommands(command)
	if not commands then
		return false, reason, quote
	end
	if #commands == 0 then
		return true
	end

	-- Build pipelines
	local pipelines, pipeline = {}, {}
	local count = 0
	for i, joinCell in ipairs(commands) do
		if joinCell.op ~= "pipe" then
			table.insert(pipelines, {op = joinCell.op, pipeline = pipeline})
			pipeline = {}
			count = count + 1
		end
		table.insert(pipeline, joinCell.command)
	end

	if #pipeline > 0 then -- add tail pipeline
		table.insert(pipelines, {op = "delim", pipeline = pipeline})
	end

	local out
	-- Run pipelines
	for i, pipeCell in ipairs(pipelines) do
		local op, pipeline = pipeCell.op, pipeCell.pipeline
		local results = {runPipeline(input, output, env, pipeline, ...)}
		local success = results[1] and (results[2] == true or results[2] == 0)
		if success and op == "or" then
			return table.unpack(results)
		elseif op == "and" then
			return table.unpack(results)
		end
		out = results
	end
	return table.unpack(out)
end

local function execute(env, command, ...)
	checkArg(2, command, "string")
	return eval(nil, nil, env, command, ...)
end

local args, options = shell.parse(...)
local history = {}

local function escapeMagic(text)
	return text:gsub('[%(%)%.%%%+%-%*%?%[%^%$]', '%%%1')
end

local function getMatchingPrograms(baseName)
	local result = {}
	-- TODO only matching files with .lua extension for now, might want to
	--      extend this to other extensions at some point? env var? file attrs?
	if not baseName or #baseName == 0 then
		baseName = "^(.*)%.lua$"
	else
		baseName = "^(" .. escapeMagic(baseName) .. ".*)%.lua$"
	end
	for basePath in string.gmatch(os.getenv("PATH"), "[^:]+") do
		for file in fs.list(basePath) do
			local match = file:match(baseName)
			if match then
				table.insert(result, match)
			end
		end
	end
	return result
end

local function getMatchingFiles(basePath, name)
	local resolvedPath = shell.resolve(basePath)
	local result, baseName = {}

	-- note: we strip the trailing / to make it easier to navigate through
	-- directories using tab completion (since entering the / will then serve
	-- as the intention to go into the currently hinted one).
	-- if we have a directory but no trailing slash there may be alternatives
	-- on the same level, so don't look inside that directory... (cont.)
	if fs.isDirectory(resolvedPath) and name:len() == 0 then
		baseName = "^(.-)/?$"
	else
		baseName = "^(" .. escapeMagic(name) .. ".-)/?$"
	end

	for file in fs.list(resolvedPath) do
		local match = file:match(baseName)
		if match then
			table.insert(result, basePath ..  match)
		end
	end
	-- (cont.) but if there's only one match and it's a directory, *then* we
	-- do want to add the trailing slash here.
	if #result == 1 and fs.isDirectory(result[1]) then
		result[1] = result[1] .. "/"
	end
	return result
end

local function hintHandler(line, cursor)
	local line = unicode.sub(line, 1, cursor - 1)
	if not line or #line < 1 then
		return nil
	end
	local result
	local prefix, partial = string.match(line, "^(.+%s)(.+)$")
	local searchInPath = not prefix and not line:find("/")
	if searchInPath then
		-- first part and no path, look for programs in the $PATH
		result = getMatchingPrograms(line)
	else -- just look normal files
		local partialPrefix = (partial or line)
		local name = partialPrefix:gsub("/+", "/")
		name = name:sub(-1) == '/' and '' or fs.name(name)
		partialPrefix = partialPrefix:sub(1, -name:len() - 1)
		result = getMatchingFiles(partialPrefix, name)
	end
	local resultSuffix = ""
	if searchInPath then
		resultSuffix  = " "
	elseif #result == 1 and result[1]:sub(-1) ~= '/' then
		resultSuffix = " "
	end
	prefix = prefix or ""
	for i = 1, #result do
		result[i] = prefix .. result[i] .. resultSuffix
	end
	table.sort(result)
	return result
end

if args.version then
	return print("OpenComputers dsh 0.1.0")
end

local quotePrefixes = {["'"] = "quote> ", ["\""] = "dquote> ", ["`"] = "bquote> "}
if options.c then
	-- noninteractive from commandline
	local result = table.pack(execute(nil, args[1])) --TODO capture parameters into numbered params
	if not result[1] then
		io.stderr:write(result[2], 0)
	end
	return table.unpack(result, 2)
elseif (io.input() == io.stdin or options.i) then
	-- interactive shell.
	while true do
		if not term.isAvailable() then -- don't clear unless we lost the term
			while not term.isAvailable() do
				event.pull("term_available")
			end
			term.clear()
		end
		local accumulator = ""
		local unmatchedQuote
		while term.isAvailable() do
			local foreground = component.gpu.setForeground(0xFF0000)
			if unmatchedQuote then
				term.write(quotePrefixes[unmatchedQuote] or "> ")
			else
				term.write(expand(os.getenv("PS1") or "$ "))
			end
			component.gpu.setForeground(foreground)
			accumulator = accumulator..term.read(history, nil, hintHandler)
			if not accumulator then
				term.write("exit\n")
				return -- eof
			end
			while #history > (tonumber(os.getenv("HISTSIZE")) or 10) do
				table.remove(history, 1)
			end
			accumulator = text.trim(accumulator)
			if accumulator == "exit" then
				return
			elseif accumulator ~= "" then
				local result, reason, quote = execute(nil, accumulator)
				local exit
				if result == "exit" then
					result = reason
					reason = quote
					quote  = nil
					exit   = true
				end
				if term.getCursor() > 1 then
					term.write("\n")
				end
				if result then
					accumulator = ""
						unmatchedQuote = nil
				else
					if reason:match("unclosed quote") then
						unmatchedQuote = quote
						accumulator = accumulator.."\n"
					else
						io.stderr:write((reason and tostring(reason) or "unknown error") .. "\n")
						accumulator = ""
						unmatchedQuote = nil
					end
				end
				if exit then
					return
				end
			end
		end
	end
elseif #args == 0 and (io.input() ~= io.stdin) then
	local accumulator = ""
	while true do
		io.write(expand(os.getenv("PS1") or "$ "))
		local command = io.read("*l")
		if not command then
			io.write("exit\n")
		end
		accumulator = accumulator..text.trim(command)
		if accumulator == "exit" then
			return
		elseif accumulator ~= "" then
			local result, reason, quote = execute(nil, accumulator)
			local exit
			if result == "exit" then
				result = reason
				reason = quote
				quote  = nil
				exit   = true
			end
			if result then
				accumulator = ""
			else
				if reason:match("unclosed quote") then
					accumulator = accumulator.."\n"
				else
					io.stderr:write((reason and tostring(reason) or "unknown error") .. "\n")
					accumulator = ""
				end
			end
			if exit then
				return
			end
		end
	end
else
	-- execute command.
	local result = table.pack(execute(...))
	if result[1] == "exit" then
		table.remove(result, 1)
	end
	if not result[1] then
		error(result[2], 0)
	end
	return table.unpack(result, 2)
end
