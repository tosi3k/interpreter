# JPP language interpreter

## Introduction

This is a Haskell implementation of JPP (Just Programming Paralanguage) interpreter. This language is based on Latte language further described [here](https://www.mimuw.edu.pl/~ben/Zajecia/Mrj2013/Latte/description.html).

The whole project is a coursework for *Programming languages and paradigms* course at the [University of Warsaw](https://www.mimuw.edu.pl/en).

## Language description

A program in JPP language is a sequence of statements. Statement can be of either form:
* expression,
* `print` instruction (which prints expressions to *stdout*),
* variable definition,
* assignment to a variable,
* function definition,
* `return` instruction,
* `if` and `if-else` instructions,
* `while` loop,
* `break` and `continue` instructions,
* empty instruction (just a plain semicolon `;`),
* block instruction.

### Expressions

Each expression has a type equal to *int*, *bool* or *string* corresponding to integer, boolean and string types in other programming languages. Apart from simple literals for the listed types (`42`, `false`, `"Hello World!"`) and variables used as values in expressions, JPP handles the basic arithmetic on integers (summation, subtraction, multiplication, division) with natural syntax (*+*, *-*, *\**, */*), basic  as well as the concatenation of strings (with *+* being the infix concatenation operator). There are also relative operators defined for all of the types (`==`, `>`, `<`, `<=`, `>=`, `!=`) corresponding to the natural linear order for integers, natural linear order for booleans and natural lexicographical order for strings. Applications of the functions serve as the expressions as well.

### `print`

One could also print expressions to `stdout` with the following syntax: `print [expr];`.

### Variable definition

Variables definition syntax is almost the same as in other *C-like* languages, for example
```
int x = 5, y, z = 2 + x;
```
would result in defining integer variables `x`, `y` and `z` equal to `5`, `0` and `7`, respectively. Observe the default value for integers being `0` - the analogous stuff happens in case of `bool` and `string` types where the default values are respectively `false` and `""` (empty string).

### Value assignment to variables

Variable wouldn't be called a variable if one couldn't assing different values to it. The syntax is self-explanatory:
```
int x = 42;
print x; // prints 42 to standard output
```

### Function definition

JPP language handles function declarations and applications as well. Example:
```
int factorial(int n) {
	if (n <= 0) {
		return 1;
	} else {
		return n * factorial(n - 1);
	}
}
print factorial(4); // prints 24 to standard output
```

Every function has an identifier (`factorial` in the example above), a type it returns (here it's `int`) and a nonnegative number of arguments (here it is `int n`). Every function declaration must contain a `return [expr]` statement where `[expr]` is an expression that evaluates to a value of the declared function return type.
As one can see, recursion is handled in JPP. We also permit passing values to the function by reference, just like in *C* or *C++* but with a slightly different syntax:

```
int swap(int ref a, int ref b) {
	int tmp = a;
	a = b;
	b = tmp;
	return 0;
}
int x = 42, y = 666;
swap(x, y);
print x; // prints 666 to standard output
print y; // prints 42 to standard output
```

### `return` statement

Explained in the subpoint above. Lack of executing such statement during function application in the runtime results in an error terminating the program execution. Presence of such statement outside of the function declaration is considered as an error as well which is detected during static program analysis, prior program execution.

### `if` and `if-else` conditional statements

Syntax analogous to *C* conditional statements. One thing that differentiates JPP from *C* is stronger typing system here. The following code would parse:
```
int a = 2, b = 2;
if (a - b) {
	print "Hello world!";
}
```
but it won't be accepted by the type checker during static program analysis.

### `while` loop

TODO

### `break` and `continue` statements

TODO

### empty statement

TODO

### Block instruction

TODO

### Other details

TODO

## Project scheme

The project consists of the following files:
* `Interpreter.hs` - the backbone of the whole project,
* `InterpreterUtils.hs` - utilities for `Interpreter.hs` (types & auxiliary functions),
* `TypeChecker.hs` - static program analyser,
* `TypeCheckerUtils.hs` - utilities for `TypeChecker.hs`,
* `Main.hs` - module with the *main* function, executes the parser, type checker and the interpreter,
* `grammar.cf` - JPP language grammar defined in LBNF notation,
* `good/` - directory with examples of good programs written in JPP,
* `bad/` - directory with examples of bad programs in JPP,
* `docs/antoni_zawodny.tex` - description of the JPP language concept written in LaTeX,
* other files (`AbsGrammar.hs`, `Makefile`, etc.) - files generated by the BNFC converter based on `grammar.cf` (including parser, abstract grammar, pretty-printer, etc.).

## Technical aspects of the project

The solution can be described in the following events taking place after each other:
1. pass the input source file in JPP language to the *interpreter* executable either as a CLI argument or by *stdin*,
2. pass the contents of the JPP source file to the BNFC-generated parser,
3. if the parsing was successful, pass the abstract syntax tree to the type checker,
4. if type checking was successful, pass the tree to the interpreter.

Each of the steps 2., 3. or 4. could result in an error and an appropriate error would be printed to *stderr*.