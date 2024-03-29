# JPP language interpreter

## Introduction

This is a Haskell implementation of JPP (Just Programming Paralanguage) interpreter. This language is based on Latte language further described [here](https://www.mimuw.edu.pl/~ben/Zajecia/Mrj2018/Latte/).

The whole project is a coursework for *Programming languages and paradigms* course at the [University of Warsaw](https://www.mimuw.edu.pl/en).

## Requirements

The project requires `ghc` compiler, `mtl` and `containers` packages installed to build. You can download the packages through *cabal*.

## Technical aspects of the project

The solution can be described in the following events taking place after each other:
1. pass the input source file in JPP language to the *interpreter* executable either as a CLI argument or by *stdin*,
2. pass the contents of the JPP source file to the parser,
3. if the parsing was successful, pass the abstract syntax tree to the type checker,
4. if type checking was successful, pass the tree to the interpreter.

Each of the steps 2., 3. or 4. could result in an error and an appropriate error message would be printed to *stderr*. Main contribution was put in the development of steps 3. and 4. with heavy monad transformers usage (with 1. and 2. generated by the BNFC converter and 1. slightly modified by myself). Further details are described in the source code in comments.

## Project scheme

The project consists of the following files:
* `Interpreter.hs` - the backbone of the whole project,
* `InterpreterUtils.hs` - utilities for `Interpreter.hs` (types & auxiliary functions),
* `TypeChecker.hs` - static program analyser,
* `TypeCheckerUtils.hs` - utilities for `TypeChecker.hs`,
* `Main.hs` - module with the `main` function, executes the parser, type checker and the interpreter,
* `grammar.cf` - JPP language grammar defined in LBNF notation,
* `good/`, `bad/` - directories with examples of good and bad programs written in JPP (served as unit tests during TDD of the interpreter),
* `docs/antoni_zawodny.tex` - description of the JPP language concept written in LaTeX,
* other files (`AbsGrammar.hs`, `Makefile`, etc.) - files generated by the BNFC converter based on `grammar.cf` (including parser, abstract grammar, pretty-printer, etc.).

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
*C-like* comments are handled in JPP (both block comments (*/\* \*/*) and single line comments (*//*)).

### Expressions

Each expression can have a type equal to `int`, `bool` or `string` corresponding to integer, boolean and string types in other programming languages. Apart from simple literals for the listed types (`42`, `false`, `"Hello World!"`) and variables used as values in expressions, JPP handles the basic arithmetic on integers (summation, subtraction, multiplication, division) with natural syntax (*+*, *-*, *\**, */*), basic  as well as the concatenation of strings (with *+* being the infix concatenation operator). Logical operators for boolean expressions are handled as well (`&&`, `||` and `!` - prefix negation; the logical conjunction and disjunctions are evaluated in a lazy way). There are also relative operators defined for all of the types (`==`, `>`, `<`, `<=`, `>=`, `!=`) corresponding to the natural linear order for integers, natural linear order for booleans and natural lexicographical order for strings. Applications of the functions serve as the expressions as well.
Tuples and lists are supported as well and they are described further on.
Any type mismatch would result in an error detected during static program analysis step

### `print`

One could also print expressions to `stdout` with the following syntax: `print [expr];`.

### Variable definition

Variables definition syntax is almost the same as in other *C-like* languages, for example
```
int x = 5, y, z = 2 + x;
```
would result in defining integer variables `x`, `y` and `z` equal to `5`, `0` and `7`, respectively. Observe the default value for integers being `0` - the analogous stuff happens in case of `bool` and `string` types where the default values are respectively `false` and `""` (empty string). In case of tuples we support the following syntax for variable definitions and default values:
```
tuple<int, string> coords1, coords2 = (3, "hello");
print coords1; // prints (0, "") to standard output
print coords2; // prints (3, "hello") to standard output
```
In case of lists we support the following syntax for variable definitions and default values:
```
list<int> list1, list2 = [1, 2, 3];
print list1; // prints [] to stdout
print list2; // prints [1, 2, 3] to stdout
```
You can mix lists and tuples however you want (meaning you can have lists of tuples of tuples of lists etc., _ad infinitum_), e.g.:
```
list<tuple<int, list<int>>> a = [(3, [3, 2, 1, 0]),
                                 (2, [2, 1, 0]),
                                 (1, [1, 0]),
                                 (0, [0])];
print get(fetch(a, 2), 1);
// prints out [1, 0]; take a look at lists' `fetch` and tuples' `get` instructions for further details
```

### Value assignment to variables

Variable wouldn't be called a variable if one couldn't assing different values to it. The syntax is self-explanatory:
```
int x;
x = 42;
print x; // prints 42 to standard output

tuple<int, string> y;
y = (x, "Hello world");
print y; // prints (42, "Hello world") to standard output

list<int> z;
print z; // prints [] to standard output
z = [1, 2, 3];
print z; // prints [1, 2, 3] to standard output
z = emptyList<int>;
print z; // prints [] to standard output
```
You *cannot* use ```[]``` as a notation for an empty list in JPP language - the brackets ought to contain at least one value. Instead, we denote an empty list of a concrete type ```T``` by ```emptyList<T>``` which is an expression in JPP language you can bind to a variable or use in comparisons 

### Accessing tuple member values

We can access individual member values of a tuple using `get` instruction. `get` behaves like a function working on tuples where the first argument is a tuple value and a second one is the index of the requested tuple member. The index *must* be a nonnegative constant integer less than the number of members of a tuple. Syntax:
```
tuple<int, tuple<int, int>> xyz = (1, (2, 3));

print get(xyz, 0);         // prints out 1
print get(xyz, 1);         // prints out (2, 3)
print get(get(xyz, 1), 0); // prints out 2
print get(get(xyz, 1), 1); // prints out 3
print get((3, 4), 1);      // prints out 4
```

### Lists concatenation

Just put a `+` between lists of the same type (if types aren't the same, you will end up with a static check error):
```
list<int> l1 = [1, 2, 3];
list<int> l2 = [4, 5, 6];

print l1 + l2; // prints out [1, 2, 3, 4, 5, 6] to stdout
```

### Accessing list member values

We can access individual list values of a tuple using `fetch` instruction. `fetch` behaves like a function working on lists where the first argument is a tuple value and a second one is the index of the requested tuple member. The index must be an expression evaluating to a nonnegative integer less than the number of members of a tuple (otherwise you would end up with a runtime error). Syntax:
```
list<int> l1 = [1, 2, 3];
list<int> l2 = [4, 5, 6];

print fetch(l1, 0); // prints out 1 to stdout
print fetch(l1, 1); // prints out 2 to stdout
print fetch(l1, 2); // prints out 3 to stdout

print fetch(l1 + l2, 3); // prints out 4 to stdout
print fetch(l1 + l2, 4); // prints out 5 to stdout
print fetch(l1 + l2, 5); // prints out 6 to stdout
```

### List length

Syntax:
```
list<int> l1 = [1, 2, 3];
list<int> l2 = [4, 5, 6];

print length(l1); // prints out 3 to stdout
print length(l1 + l2); // prints out 6 to stdout
```
You can bind list length to an integer variable:
```
list<int> l = [1,2,3,4,5];
int len = length(l);
print len; // prints out 5 to stdout
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
As one can see, recursion is handled in JPP. We also permit passing values to the function by reference, just like in *C* or *C++* but with a slightly different syntax (we use `ref` keyword instead of an ampersand `&`):
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
Reference arguments must be passed as a variable (otherwise static program analysis would cry). Function application with a wrong number of arguments is considered an error as well (detected at the moment of static program analysis).

### `return` statement

Explained in the subpoint above. Lack of executing such statement during function application in the runtime results in an error terminating the program execution. Presence of such statement outside of the function declaration is considered as an error as well which is detected during static program analysis, prior program execution.

### `if` and `if-else` conditional statements

Syntax analogous to *C* conditional statements. One thing that differentiates JPP from *C* is stronger typing system here. The following code would parse:
```
int a = 2, b = 1;
if (a - b) {
    print "Hello world!";
}
```
but it won't be accepted by the type checker during static program analysis due to the type mismatch.

### `while` loop

Syntax analogous to *C* `while` loop but, once again, we require the expression to evaluate to `bool` type (otherwise the type checker would not allow the program to be interpreted).

### `break` and `continue` statements

Syntax and semantics analogous to *C* `break` and `continue` statements. Such statements can be placed only inside a `while` loop (otherwise it won't be accepted by the type checker).

### empty statement - `;`

Self-explanatory - syntax (just a semicolon) and semantics are the same as in *C*.

### Block instruction

Syntax and semantics analogous to the ones in *C*. JPP language has a static name binding with identifier shadowing, however. This means the following code is correct and would print *True* several times to *stdout*:
```
int x = 5;
{
    x = 4;
    print x == 4;
    {
        int x = 3;
        print x == 3;
    }
    print x == 4;
    int x() {
        return 7;
    }
    print x() == 7;
    int f() {
        return 0;
    }
}
print x == 4;
```
In addition, we won't be able to access `f` function from the outside of the outer block. Generally, any reference to a name out of the scope would result in a static program analysis error.
