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
do
	local function formatPattern(p)
		return "^"..p.."(.*)"
	end

	local function format(f)
		local out = {}
		for i,v in ipairs(f) do
			out[i] = formatPattern(v)
		end
		return out
	end

	function readRaw(param, n)
		if self.closed then
			if self.buffer == "" and self.redirect.read then
				return self.redirect.read:read(param)
			else
				return nil -- eof
			end
		end
		if type(param) == "number" then
			while #self.buffer < param do
				self.args = table.pack(coroutine.yield(table.unpack(self.result)))
			end
			local result = string.sub(self.buffer, 1, param)
			self.buffer = string.sub(self.buffer, param + 1)
			return result
		elseif param == "*n" then
			local formats = {
				format{"[+-]?", "0x", "%x+"},
				format{"[+-]?", "0x", "%x*", "%.", "%x+"},
				format{"[+-]?", "0x", "%x+", "%.", "%x*"},
				format{"[+-]?", "0x", "%x*", "[pP]", "[+-]?", "%x+"},
				format{"[+-]?", "0x", "%x*", "%.", "%x+", "[pP]", "[+-]?", "%x+"},
				format{"[+-]?", "0x", "%x+", "%.", "%x*", "[pP]", "[+-]?", "%x+"},
				format{"[+-]?", "%d+"},
				format{"[+-]?", "%d*", "%.", "%d+"},
				format{"[+-]?", "%d+", "%.", "%d*"},
				format{"[+-]?", "%d*", "[eE]", "[+-]?", "%d+"},
				format{"[+-]?", "%d*", "%.", "%d+", "[eE]", "[+-]?", "%d+"},
				format{"[+-]?", "%d+", "%.", "%d*", "[eE]", "[+-]?", "%d+"}
			}
			local accumulator = ""
			while #formats > 0 do
				accumulator = accumulator..self:read(1)
				local newFormats = {}
				for i, format in ipairs(formats) do
					local verify = accumulator
					for _, pattern in ipairs(format) do
						verify = verify:match(pattern)
						if verify == "" or not verify then
							break
						end
					end
					if verify then
						table.insert(newFormats, format)
					end
				end
			end
			return tostring(accumulator)
		elseif param == "*a" then
			local eot = string.char(0x04)
			while not buffer.find("\n"..eot) do
				self.args = table.pack(coroutine.yield(table.unpack(self.result)))
			end
			local ret
			ret, buffer = buffer:match("(.-\n)"..eot.."(.*)")
			return ret
		elseif param == "*L" then
			while not buffer.find("\n") do
				self.args = table.pack(coroutine.yield(table.unpack(self.result)))
			end
			local ret
			ret, buffer = buffer:match("(.-\n)(.*)")
			return ret
		elseif param == "*l" or param == nil then
			while not buffer.find("\n") do
				self.args = table.pack(coroutine.yield(table.unpack(self.result)))
			end
			local ret
			ret, buffer = buffer:match("(.-)\n(.*)")
			return ret
		else
			error("bad argument #"..n.." to 'read' (invalid option)", 3)
		end
	end

	function memoryStream:read(...)
		local modes = table.pack(...)
		local out = {}
		for i=1, modes.n do
			out[i] = rawRead(modes[i], i)
		end
		out.n = modes.n
		return table.unpack(out)
	end
end

function memoryStream:write(...)
	local params = table.pack(...)
	for i=1, params.n do
		if type(params[i]) == "number" then -- coerce type
			params[i] = tostring(params[i])
		end
		checkArg(i, params[i], "string")
		if not self.redirect.write and self.closed then
			error("attempt to use a closed stream", 2)
		end
		if self.redirect.write then
			self.redirect.write:write(params[i])
		end
		if not self.closed then
			self.buffer = self.buffer .. params[i]
			self.result = table.pack(coroutine.resume(self.next, table.unpack(self.args)))
			if coroutine.status(self.next) == "dead" then
				self:close()
			end
			if not self.result[1] then
				error(self.result[2], 0)
			end
			table.remove(self.result, 1)
		end
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

local operators = {"&&", "||", ";", "|"} -- must be ordered from long to short

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
							return nil, "parse error near '"..isOp.."'"
						end
						table.insert(tokens, tokenOut)
						table.insert(tokens, isOp)
						token = {}
						break
					end
				end
				if not isOp then
					if char:match("%s") then
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

local function evaluate(value)
	local init, results = 1, {""}
	repeat
		local match = value:match("^%b''", init)
		if match then -- single quoted string. no variable expansion.
			match = match:sub(2, -2)
			init = init + 2
			for i, result in ipairs(results) do
				results[i] = result .. match
			end
		else
			match = value:match('^%b""', init)
			if match then -- double quoted string.
				match = match:sub(2, -2)
				init = init + 2
			else
				-- plaintext?
				-- NOTE: backticks will be treated as plaintext
				-- and evaluated in a separate pass
				match = value:match("^([^']+)%b''", init)
				if not match then -- unmatched single quote.
					match = value:match('^([^"]+)%b""', init)
					if not match then -- unmatched double quote.
						match = value:sub(init)
					end
				end
			end
			local newResults = {}
			for _, globbed in ipairs(glob(match)) do
				for i, result in ipairs(results) do
					newResults[i] = result..globbed
				end
			end
			results = newResults
		end
		init = init + #match
	until init > #value

	-- TODO Evaluate backticks, need to modularize
	--      code more to make this possible

	return results
end

local function parseCommand(tokens, ...)
	if #tokens == 0 then
		return
	end

	if tokens[1] == "exit" then
		return "exit"
	end

	local program, args = shell.resolveAlias(tokens[1], table.pack(select(2, table.unpack(tokens))))

	local eargs = {}
	program = evaluate(program)
	for i = 2, #program do
		table.insert(eargs, program[i])
	end
	local program, reason = shell.resolve(program[1], "lua")
	if not program then
		return nil, reason
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
	return program, args, input, output, mode
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
		[";"]  = "delim"
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
		joinCell.command = table.pack(parseCommand(joinCell.command))
		if joinCell.command[1] == nil then
			return nil, joinCell.command[2]
		end
	end

	return commands
end

-------------------------------------------------------------------------------

local function runPipeline(env, pipeline, ...)
	if pipeline[1][1] == "exit" then
		return "exit", true
	end

	-- Piping data between programs works like so:
	-- program1 gets its output replaced with our custom stream.
	-- program2 gets its input replaced with our custom stream.
	-- repeat for all programs
	-- custom stream triggers execution of 'next' program after write.
	-- custom stream triggers yield before read if buffer is empty.
	-- custom stream may have 'redirect' entries for fallback/duplication.
	local threads, pipes, inputs, outputs = {}, {}, {}, {}
	for i = 1, #pipeline do
		local program, args, input, output, mode = table.unpack(pipeline[i])
		if program == "exit" then
			threads[i] = "exit"
			break
		end
		local reason
		threads[i], reason = process.load(program, env, function()
			os.setenv("_", program)
			if input then
				local file, reason = io.open(shell.resolve(input))
				if not file then
					error("could not open '" .. input .. "': " .. reason, 0)
				end
				table.insert(inputs, file)
				if pipes[i - 1] then
					pipes[i - 1].stream.redirect.read = file
					io.input(pipes[i - 1])
				else
					io.input(file)
				end
			elseif pipes[i - 1] then
				io.input(pipes[i - 1])
			end
			if output then
				local file, reason = io.open(shell.resolve(output), mode == "append" and "a" or "w")
				if not file then
					error("could not open '" .. output .. "': " .. reason, 0)
				end
				if mode == "append" then
					io.write("\n")
				end
				table.insert(outputs, file)
				if pipes[i] then
					pipes[i].stream.redirect.write = file
					io.output(pipes[i])
				else
					io.output(file)
				end
			elseif pipes[i] then
				io.output(pipes[i])
			end
		io.write('')
		end, command)
		if not threads[i] then
			return false, reason
		end

		if i < #pipeline then
			pipes[i] = require("buffer").new("rw", memoryStream.new())
			pipes[i]:setvbuf("no")
		end
		if i > 1 then
			pipes[i - 1].stream.next = threads[i]
			pipes[i - 1].stream.args = args
		end
	end

	local args = pipeline[1][2]
	for _, arg in ipairs(table.pack(...)) do
		table.insert(args, arg)
	end
	table.insert(args, 1, true)
	args.n = #args
	local result = nil
	for i = 1, #threads do
		if threads[i] == "exit" then
			result = {"exit", table.unpack(result)}
			break
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
				if result[2].code then
					result[1] = true
					result.n = 1
				else
					result[2] = "terminated"
				end
			elseif type(result[2]) == "string" then
				result[2] = debug.traceback(threads[i], result[2])
			end
			break
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

local function execute(env, command, ...)
	checkArg(1, command, "string")
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
		local results = {runPipeline(env, pipeline, ...)}
		if results[1] == "exit" then
			out = results
			break
		end
		if results[1] then
			if op == "or" then
				return table.unpack(results)
			end
		else
			if op == "and" or op == "pipe" then
				return table.unpack(results)
			end
		end
		out = results
	end
	return table.unpack(out)
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
