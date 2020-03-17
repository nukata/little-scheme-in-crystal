#!/usr/bin/env crystal
# -*- coding: utf-8 -*-
# A little Scheme in Crystal 0.33, v0.1 R02.03.17 by SUZUKI Hisao
# cf. https://github.com/nukata/little-scheme-in-ruby
#     https://github.com/nukata/little-scheme-in-java
#     https://github.com/nukata/little-scheme-in-php

require "big"

module LittleScheme
  LS = LittleScheme

  # Convert an Int64 into an Int32 or a BigInt.
  def self.normalize(x : Int64): (Int32 | BigInt)
    i = x.to_i32!
    return (i == x) ? i : x.to_big_i
  end

  # Convert a BigInt into an Int32 if possible.
  def self.normalize(x : BigInt): (Int32 | BigInt)
    i = x.to_i32!
    return (i == x) ? i : x
  end

  # x + y
  def self.add(x : Number, y : Number): Number
    if x.is_a?(Int32) && y.is_a?(Int32)
      return normalize(x.to_i64 + y.to_i64)
    elsif x.is_a?(Float64) || y.is_a?(Float64)
      return x.to_f64 + y.to_f64
    else
      return normalize(x.to_big_i + y.to_big_i)
    end
  end

  # x - y
  def self.subtract(x : Number, y : Number): Number
    if x.is_a?(Int32) && y.is_a?(Int32)
      return normalize(x.to_i64 - y.to_i64)
    elsif x.is_a?(Float64) || y.is_a?(Float64)
      return x.to_f64 - y.to_f64
    else
      return normalize(x.to_big_i - y.to_big_i)
    end
  end

  # x * y
  def self.multiply(x : Number, y : Number): Number
    if x.is_a?(Int32) && y.is_a?(Int32)
      return normalize(x.to_i64 * y.to_i64)
    elsif x.is_a?(Float64) || y.is_a?(Float64)
      return x.to_f64 * y.to_f64
    else
      return normalize(x.to_big_i * y.to_big_i)
    end
  end

  # x <=> y
  def self.compare(x : Number, y : Number): Int32
    if x.is_a?(Int32) && y.is_a?(Int32)
      return x.to_i64 <=> y.to_i64
    elsif x.is_a?(Float64) || y.is_a?(Float64)
      a = (x.to_f64 <=> y.to_f64)
      raise "not comparable: #{x} and #{y}" if a.nil?
      return a
    else
      return x.to_big_i <=> y.to_big_i
    end
  end

  # ----------------------------------------------------------------------

  class Obj
  end

  # Value operated by Scheme
  alias Val = Nil | Obj | Bool | String | Int32 | Float64 | BigInt

  # Object with its name
  class NamedObj < Obj
    private getter name : String

    def initialize(@name)
    end

    def to_s
      return @name
    end
  end # NamedObj

  # A unique value which means the expression has no value
  NONE = NamedObj.new("#<VOID>")

  # A unique value which means the End Of File
  EOF = NamedObj.new("#<EOF>")

  # Scheme's symbol
  class Sym < NamedObj
    private SYMBOLS = {} of String => Sym

    def initialize(name)
      super name
    end

    def self.interned(name)
      return SYMBOLS.fetch(name) {
        SYMBOLS[name] = s = Sym.new(name)
        return s
      }
    end
  end # Sym

  S_QUOTE = Sym.interned("quote")
  S_IF = Sym.interned("if")
  S_BEGIN = Sym.interned("begin")
  S_LAMBDA = Sym.interned("lambda")
  S_DEFINE = Sym.interned("define")
  S_SETQ = Sym.interned("set!")
  S_APPLY = Sym.interned("apply")
  S_CALLCC = Sym.interned("call/cc")

  # ----------------------------------------------------------------------

  # Cons cell
  class Cell < Obj
    include Enumerable(Val)

    getter car : Val            # Head part of the cell
    property cdr : Val          # Tail part of the cell

    def initialize(@car : Val, @cdr : Val)
    end

    # Yield car, cadr, caddr and so on, à la for-each in Scheme.
    def each
      j = self
      loop {
        yield j.as(Cell).car
        j = j.as(Cell).cdr
        break unless Cell === j
      }
      raise ImproperListException.new(j) unless j.nil?
    end
  end # Cell

  # The last tail of the list is not null.
  class ImproperListException < Exception
    getter tail : Val           # The last tail of the list

    def initialize(@tail)
    end
  end # ImproperListException

  # ----------------------------------------------------------------------

  # Linked list of bindings which map symbols to values
  class Environment < Obj
    include Enumerable(Environment)

    getter symbol           # Bound symbol
    property value          # Value mapped from the bound symbol
    property succ           # Successor of the present binding, or nil

    # Construct a binding on the top of succ.
    def initialize(@symbol : Sym?, @value : Val, @succ : Environment?)
    end

    # Yield each binding.
    def each
      env = self
      loop {
        yield env
        env = env.succ
        break if env.nil?
      }
    end

    # Search the binding for a symbol.
    def look_for(symbol : Sym)
      env = self.find {|e| symbol.same? e.symbol}
      return env unless env.nil?
      raise KeyError.new("#{symbol.to_s} not found")
    end

    # Build a new environment by prepending the bindings of symbols and data
    # to the present environment.
    def prepend_defs(symbols : Cell?, data : Cell?)
      if symbols.nil?
        return self if data.nil?
        raise ArgumentError.new(
                "surplus arg: #{LS.stringify data}")
      else
        raise ArgumentError.new(
                "surplus param: #{LS.stringify symbols}") if data.nil?
        rest = prepend_defs(symbols.cdr.as(Cell?), data.cdr.as(Cell?))
        return Environment.new(symbols.car.as(Sym), data.car, rest)
      end
    end
  end # Environment

  # ----------------------------------------------------------------------

  # NB: Scheme's continuations have the following operations:
  #  :Then, :Begin, :Define, :SetQ, :Apply, :ApplyFun, :EvalArg, :ConsArgs,
  #  :RestoreEnv

  alias Step = Tuple(Symbol, Val)

  # Scheme's continuation as a stack of steps
  class Continuation < Obj
    # Construct a copy of another continuation, or an empty continuation.
    def initialize(other=nil)
      @stack = other.nil? ? [] of Step : other.copy_stack
    end

    # Copy steps from another continuation.
    def copy_from(other)
      @stack = other.copy_stack
    end

    # Return a shallow copy of the inner stack.
    def copy_stack
      return @stack.dup
    end

    # Return true if the continuation is empty.
    def empty?
      return @stack.empty?
    end

    # Length of the continuation
    def size
      return @stack.size
    end

    # Return a quasi-stack trace.
    def inspect
      ss = @stack.map {|step| "#{step[0]} #{LS.stringify step[1]}"}
      return "#<#{ss.join "\n\t"}>"
    end

    # Push a step to the top of the continuation.
    def push(operation : Symbol, value : Val)
      @stack.push({operation, value})
    end

    # Pop a step from the top of the continuation.
    def pop
      return @stack.pop
    end

    # Push :RestoreEnv unless on a tail call.
    def push_RestoreEnv(env)
      top = @stack.last?
      push(:RestoreEnv, env) unless (top && :RestoreEnv == top[0])
    end
  end # Continuation

  # ----------------------------------------------------------------------

  # Lambda expression with its environment
  class Closure < Obj
    getter params               # List of symbols as formal parameters
    getter body                 # List of expressions as a body
    getter env                  # Environment of the body

    def initialize(@params : Cell?, @body : Cell, @env : Environment)
    end
  end # Closure

  # Built-in function
  class Intrinsic < Obj
    getter name : String           # Function's name
    getter arity : Int32           # Function's arity, -1 if it is variadic
    getter func : Proc(Cell?, Val) # Function's body

    def initialize(@name : String, @arity : Int32, @func : Proc(Cell?, Val))
    end

    def inspect
      return "#<#{@name}:#{@arity}>"
    end
  end # Intrinsic

  # ----------------------------------------------------------------------

  # Exception thrown by the error procedure of SRFI-23
  class ErrorException < Exception
    def initialize(reason, arg)
      if NONE == arg
        super "Error: #{LS.stringify(reason, false)}"
      else
        super "Error: #{LS.stringify(reason, false)}: #{LS.stringify arg}"
      end
    end
  end # ErrorException

  # ----------------------------------------------------------------------

  # Convert an expression to a string.
  def self.stringify(exp, quote=true)
i    case exp
    when nil
      return "()"
    when false
      return "#f"
    when true
      return "#t"
    when NamedObj
      return exp.to_s
    when String
      return quote ? exp.inspect : exp
    when Cell
      ss = [] of String
      begin
        exp.each {|e|
          ss << stringify(e, quote)
        }
      rescue ex: ImproperListException
        ss << "."
        ss << stringify(ex.tail, quote)
      end
      return "(#{ss.join " "})"
    when Environment
      ss = [] of String
      exp.each {|e|
        if e.same? GLOBAL_ENV
          ss << "GlobalEnv"
          break
        elsif e.symbol.nil?     # frame marker
          ss << "|"
        else
          ss << e.symbol.to_s
        end
      }
      return "#<#{ss.join " "}>"
    when Closure
      return "#<" + stringify(exp.params) +
             ":" + stringify(exp.body) +
             ":" + stringify(exp.env) + ">"
    else
      return exp.inspect
    end
  end

  # ----------------------------------------------------------------------

  private macro c(name, arity, body, succ)
    Environment.new(Sym.interned({{name}}),
                    Intrinsic.new({{name}}, {{arity}}, ->(x : Cell?) {{body}}),
                    {{succ}})
  end

  private macro fst(x)
    {{x}}.as(Cell).car
  end

  private macro snd(x)
    {{x}}.as(Cell).cdr.as(Cell).car
  end

  private macro val(x)
    ({{x}}).as(Val)
  end

  # Return a list of symbols of the global environment.
  private def self.globals
    j = nil
    env = GLOBAL_ENV.succ       # Skip the frame marker.
    unless env.nil?
      env.each {|e|
        j = Cell.new(e.symbol, j)
      }
    end
    return j
  end

  private def self.display(exp)
    begin
      print stringify(exp, false)
    rescue ex: Errno
      raise ErrorException.new(ex.message, NONE) if ex.errno == Errno::EPIPE
      raise ex
    end
    return NONE
  end

  private def self.newline
    begin
      puts
    rescue ex: Errno
      raise ErrorException.new(ex.message, NONE) if ex.errno == Errno::EPIPE
      raise ex
    end
    return NONE
  end

  private def self.eq?(x : Val, y : Val): Bool
    if x.class != y.class
      return false
    elsif x.is_a?(Reference) && y.is_a?(Reference)
      return x.same? y
    else
      return x == y
    end
  end

  private G1 =
          c("+" , 2,
            { val add(fst(x).as(Number), snd(x).as(Number)) },
            c("-" , 2,
              { val subtract(fst(x).as(Number), snd(x).as(Number)) },
              c("*" , 2,
                { val multiply(fst(x).as(Number), snd(x).as(Number)) },
                c("<" , 2,
                  { val(compare(fst(x).as(Number), snd(x).as(Number)) < 0) },
                  c("=" , 2,
                    { val(compare(fst(x).as(Number), snd(x).as(Number)) == 0)
                    },
                    c("error", 2, { raise ErrorException.new(fst(x), snd(x)) },
                      c("globals", 0, { val globals },
                        Environment.new(S_CALLCC, S_CALLCC,
                                        Environment.new(S_APPLY, S_APPLY,
                                                        nil)))))))))
  # The global environment
  GLOBAL_ENV = Environment.new(
    nil,                        # frame marker
    nil,
    c("car", 1, { fst(x).as(Cell).car },
      c("cdr", 1, { fst(x).as(Cell).cdr },
        c("cons", 2, { val Cell.new(fst(x), snd(x)) },
          c("eq?", 2, { val eq?(fst(x), snd(x)) },
            c("eqv?", 2, { val(fst(x) == snd(x)) },
              c("pair?", 1, { val(Cell === fst(x)) },
                c("null?", 1, { val fst(x).nil? },
                  c("not", 1, { val(false == fst(x)) },
                    c("list", -1, { val x },
                      c("display", 1, { val display(fst(x)) },
                        c("newline", 0, { val newline },
                          c("read", 0, {read_expression },
                            c("eof-object?", 1, { val(EOF == fst(x)) },
                              c("symbol?", 1, { val(Sym === fst(x)) },
                                G1)))))))))))))))

  # ----------------------------------------------------------------------

  # Evaluate an expression in an environment.
  def self.evaluate(exp : Val, env : Environment)
    k = Continuation.new
    begin
      loop {
        loop {
          case exp
          when Cell
            kar = exp.car
            kdr = exp.cdr.as(Cell?)
            if kdr.nil?
              exp = kar
              k.push(:Apply, nil)
            else
              case kar
              when S_QUOTE      # (quote e)
                exp = kdr.car
                break
              when S_IF         # (if e1 e2 [e3])
                exp = kdr.car
                k.push(:Then, kdr.cdr)
              when S_BEGIN      # (begin e...)
                exp = kdr.car
                k.push(:Begin, kdr.cdr) unless kdr.cdr.nil?
              when S_LAMBDA     # (lambda (v...) e...)
                exp = Closure.new(kdr.car.as(Cell?), kdr.cdr.as(Cell), env)
                break
              when S_DEFINE     # (define v e)
                exp = kdr.cdr.as(Cell).car
                k.push(:Define, kdr.car)
              when S_SETQ       # (set! v e)
                exp = kdr.cdr.as(Cell).car
                k.push(:SetQ, env.look_for(kdr.car.as(Sym)))
              else              # (fun arg...)
                exp = kar
                k.push(:Apply, kdr)
              end
            end
          when Sym
            exp = env.look_for(exp).value
            break
          else                  # a number, #t, #f etc.
            break
          end
        }
        loop {
          # print "_#{k.size}"
          return exp if k.empty?
          op, x = k.pop
          case op
          when :Then            # x is (e2 [e3]).
            j = x.as(Cell)
            if false == exp
              if j.cdr.nil?
                exp = NONE
              else
                exp = j.cdr.as(Cell).car # e3
                break
              end
            else
              exp = j.car       # e2
              break
            end
          when :Begin           # x is (e...).
            j = x.as(Cell)
            k.push(:Begin, j.cdr) unless j.cdr.nil?
            exp = j.car
            break
          when :Define          # x is a variable name.
            # env.symbol should be nil i.e. a frame marker.
            env.succ = Environment.new(x.as(Sym), exp, env.succ)
            exp = NONE
          when :SetQ            # x is an Environment.
            x.as(Environment).value = exp
            exp = NONE
          when :Apply           # x is a list of args; exp is a function.
            if x.nil?
              exp, env = apply_function(exp, nil, k, env)
            else
              k.push(:ApplyFun, exp)
              j = x.as(Cell)
              until j.cdr.nil?
                k.push(:EvalArg, j.car)
                j = j.cdr.as(Cell)
              end
              exp = j.car
              k.push(:ConsArgs, nil)
              break
            end
          when :ConsArgs
            # x is a list of evaluated args (to be a cdr);
            # exp is a newly evaluated arg (to be a car).
            args = Cell.new(exp, x)
            op, exp = k.pop
            case op
            when :EvalArg       # exp is the next arg.
              k.push(:ConsArgs, args)
              break
            when :ApplyFun      # exp is a function
              exp, env = apply_function(exp, args, k, env)
            else
              raise "invalid operation: #{op} #{exp}"
            end
          when :RestoreEnv      # x is an Environment.
            env = x.as(Environment)
          else
            raise "invalid operation: #{op}, #{x}"
          end
        }
      }
    rescue eex: ErrorException
      raise eex
    rescue ex
      s =  "#{ex.class}: #{ex.message}"
      s += "\n\t#{stringify k}" unless k.empty?
      raise Exception.new(s, ex)
    end
  end

  # ----------------------------------------------------------------------

  # Apply a function to arguments with a continuation and an environment.
  private def self.apply_function(func, arg : Cell?, k, env : Environment) \
             : Tuple(Val, Environment)
    loop {
      case func
      when S_CALLCC
        k.push_RestoreEnv(env)
        func = arg.as(Cell).car
        arg = Cell.new(Continuation.new(k), nil)
      when S_APPLY
        func = arg.as(Cell).car
        arg = arg.as(Cell).cdr.as(Cell).car.as(Cell?)
      else
        break
      end
    }
    case func
    when Intrinsic
      if func.arity >= 0
        if arg.nil? ? func.arity > 0 : arg.size != func.arity
          raise ArgumentError.new(
                  "arity not matched: #{stringify func} and #{stringify arg}")
        end
      end
      result = func.func.call(arg)
      return {result, env}
    when Closure
      k.push_RestoreEnv(env)
      k.push(:Begin, func.body)
      return {NONE,
              Environment.new(nil, # frame marker
                              nil,
                              func.env.prepend_defs(func.params, arg))}
    when Continuation
      k.copy_from(func)
      return {arg.as(Cell).car, env}
    else
      raise ArgumentError.new(
              "not a funcction: #{stringify func} with #{stringify arg}")
    end
  end

  # ----------------------------------------------------------------------

  # Split a string into an abstract sequence of tokens.
  # For "(a 1)" it yields "(", "a", "1" and ")".
  private def self.split_string_into_tokens(source)
    source.each_line {|line|
      ss = [] of String         # to store string literals
      x = [] of String
      i = true
      line.split('"') {|e|
        if i
          x << e
        else
          ss << '"' + e         # Store a string literal.
          x << "#s"
        end
        i = ! i
      }
      s = x.join(" ").split(";")[0] # Ignore "; ...".
      s = s.gsub("'", " ' ").gsub("(", " ( ").gsub(")", " ) ")
      s.split {|e|
        if e == "#s"
          yield ss.shift
        else
          yield e
        end
      }
    }
  end

  # Read an expression from tokens.
  # Tokens will be left with the rest of the token strings if any.
  private def self.read_from_tokens(tokens) : Val
    token = tokens.shift
    case token
    when "("
      z = Cell.new(nil, nil)
      y = z
      until tokens.first == ")"
        if tokens.first == "."
          tokens.shift
          y.cdr = read_from_tokens tokens
          unless tokens.first == ")"
            raise ") is expected: #{tokens.first}"
          end
          break
        end
        e = read_from_tokens tokens
        x = Cell.new(e, nil)
        y.cdr = x
        y = x
      end
      tokens.shift
      return z.cdr
    when ")"
      raise "unexpected )"
    when "'"
      e = read_from_tokens tokens
      return Cell.new(S_QUOTE, Cell.new(e, nil)) # (quote e)
    when "#f"
      return false
    when "#t"
      return true
    else
      return token[1..-1] if token[0] == '"'
      return (token.to_i32 rescue token.to_big_i rescue token.to_f64 \
             rescue Sym.interned(token))
    end
  end

  # ----------------------------------------------------------------------

  # Tokens from the standard-in
  private STDIN_TOKENS = [] of String

  # Read an expression from the console.
  def self.read_expression(prompt1="", prompt2="")
    loop {
      old = STDIN_TOKENS.dup
      begin
        return read_from_tokens STDIN_TOKENS
      rescue IndexError
        print old.empty? ? prompt1 : prompt2
        STDOUT.flush
        line = STDIN.gets
        return EOF if line.nil?
        STDIN_TOKENS.replace old
        split_string_into_tokens(line) {|token|
          STDIN_TOKENS << token
        }
      rescue ex
        STDIN_TOKENS.clear
        raise ex
      end
    }
  end

  # Repeat Read-Eval-Print until End-Of-File.
  def self.read_eval_print_loop
    loop {
      begin
        exp = read_expression("> ", "| ")
        if EOF == exp
          puts "Goodbye"
          return
        end
        result = evaluate(exp, GLOBAL_ENV)
      rescue ex
        puts ex
        # raise
      else
        puts stringify result unless NONE == result
      end
    }
  end

  # Load a source code from a file.
  def self.load(file_name)
    source = File.read(file_name)
    tokens = [] of String
    split_string_into_tokens(source) {|token|
      tokens << token
    }
    until tokens.empty?
      exp = read_from_tokens(tokens)
      evaluate(exp, GLOBAL_ENV)
    end
  end
end # LittleScheme

# ----------------------------------------------------------------------

# The main routine
begin
  unless ARGV.empty?
    LittleScheme.load ARGV[0]
    exit 0 if ARGV[1]? != "-"
  end
  LittleScheme.read_eval_print_loop
rescue ex
  STDERR.puts ex
  cause = ex.cause
  if cause
    backtrace = cause.backtrace?
    if backtrace
      STDERR.puts backtrace
    end
  end
  exit 1
end
