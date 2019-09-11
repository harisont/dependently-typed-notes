% Strongly typed notes 
% Arianna Masciolini

# Introduction
Key idea of the course: __Curry-Howard isomorphism__ (or _correspondence_), i.e.

> Programming = Mathematics, or Computer Science = Logic

And more precisely:

> _Terminating_ Functional Programming = _Constructive_ Mathematics

(where mathematical constructionism asserts that it is necessary to find a mathematical object to prove its existence).

Object of the course: __dependently typed programming__.
**_Dependent types_** come from predicate logic (in the sense that we can express pretty much any logical formula through types, thanks to the above isomorphism). More precisely, they are __types that depend on *elements* of other types__, e.g. vectors $[ A ]^n$ ($\ne$ parametrised types, e.g. lists $[ A ]$, which just depend on other types). They are implemented in:

- Coq(uand) (the one used to prove the planar map theorem) -> algorithms correct by constructions (not under absolute terms)
- __Agda__, a pure functional languages implemented in Haskell, which we will be using for this course
- (Haskell with `GADTs`)
- ...

Coq and Agda are two examples of _verified_ programming languages (or _proof assistants_, depending if we put the emphasis on programming or on theorem proving), i.e. languages that allow to prove theorems within the same language (the proofs are checked by the type checker), thus enabling program verification. 

They are also examples of _total languages_: a program in`e` of type `T` will always terminate with a value in `T`. No runtime error can occur and no nonterminating programs can be written (unless explicitly requested by the programmer). This is implemented via an (incomplete) _termination checker_ that (only) works with _**primitive recursion**_ (a _primitive recursive function_ is a function that can be computed by a computer program whose loops are all `for` loops, i.e. an upper bound of the number of iterations of every loop can be determined _before_ entering the loop. __Primitive recursive functions form a strict subset of those general recursive functions that are also total functions__). Pragmas for disabling the termination checker:

```agda
{-# TERMINATING #-} -- asserts that a function is terminating
{-# NON-TERMINATING #-} -- allow non-terminating functions
```



## Types for software reliability
Software reliability (correctness) is hard to achieve because of:

- scale & complexity of modern systems
- number of people involved
- demands placed on them

Ways to achieve it:

- management strategies
- library design philosophy
- use of certain programming languages languages
- mathematical techniques
- validations tools
- testing
- __types__:
  - program behavior specification
  - simplification of bug hunting (cf. type checking)
  - optimisation (e.g. in terms of space)
- …

## Basic Agda

`Set` is the only native type in Agda (it’s the _type of **data types** and **small types**_. In particular, __types of types are called large types__, while __the elements of a large types are called small types__). Starting from `Set`, one can then construct function types.

```agda
-- module name = file name (mandatory)
module Bool where
	data Bool : Set where 
		true : Bool 
		false : Bool 
```

In the code above, we introduce a new data type `Bool` with two constructors (note that they are not capitalised). The Haskell equivalent would be:

```haskell
data Bool = True | False
```

An aside: is `Set` the type of itself, as it is the type of types? It can’t, because if that was the case, the language would become nonterminating. The trick is using an infinite hierarchy of types (`Set 0, 1, 2...`); see VFL chapter 1 for the whole story.

Here we define a simple function:

```agda
-- see? Pattern matching!*
not : Bool -> Bool
not true = false
not false = true
```

### Partial refinement

Pattern matching allows _partial programming_, i.e. writing programs by __gradual refinement of partial expressions__ (by _partial expressions_ we simply mean expressions with “holes”, denoted by `?`).

Example: to define double negation we can first write

```agda
binot : Bool -> Bool
binot b = ?
```

When we load the file, Agda replaces the `?` with a “hole”:

```agda
binot : Bool -> Bool
binot b =  { }0 
```

At this point, we can either fill in the gap completely writing inside the curly brackets and run “give” (see below) or use partial refinement, for example by writing

```agda
binot : Bool -> Bool
binot b =  { }0 
```

and run “refine” (again, see the cheatsheet below), thus obtaining

```agda
binot : Bool -> Bool
binot b =  not { }1 
```

…and so on.

Also, here is an example of infix function (notice the underscores):

```agda
_&&_ : Bool -> Bool -> Bool
b && true = b
b && false = false
```

More generally, one can write function symbols such as `if_then_else` using underscores to mark the argument position (__*mixfix* syntax__). Then if we need to refer to an infix function without passing it arguments, we have to include the underscores.

For infix functions such as `&&` it is also possible to specify the precedence level and associativity, e.g.

```agda
infixl 50 _&&_ -- left associative and with prec. 50
```

If we wanted to define `&&` by gradual refinement, there is a special command call “case split” for generating the clauses for pattern matching. Example:

1.  ```agda
   _&&_ : Bool → Bool → Bool
   b && c = ?
   ```

2.  load, which gives

   ```agda
    _&&_ : Bool → Bool → Bool
     b && c = { }0
   ```

3.  ```agda
    _&&_ : Bool → Bool → Bool
     b && c = {c}0
    ```

4.  “case split” on c, which gives

   ```agda
    _&&_ : Bool → Bool → Bool
     b && true = { }0
     b && false = { }1
   ```

5.  fill the holes:

   ``` agda
   _&&_ : Bool → Bool → Bool
     b && true = {b}0
     b && false = {false}1
   
   ```

6.  run “give”

### Defining unary natural numbers

We mentioned that `Set` is the only primitive type in Agda, so natural numbers need to be defined. Let’s define unary (caveman) __Peano natural numbers__, i.e. the numbers generated by the two constructors `zero` for the number 0 and `succ` for the successor function which adds 1 to a number.

```agda
data Nat : Set where
	zero : Nat
	succ : Nat -> Nat
	
-- {- examples of definition of arbitrary natural numbers -}
one = succ zero
two = succ one
```

Let’s define (by recursion & pattern matching) some basic arithmetic:

```agda
_+_ ∶ Nat -> Nat -> Nat
m + zero = m
m + succ n = succ (m + n)

_∗_ ∶ Nat -> Nat -> Nat
m ∗ zero = zero
m ∗ succ n = m + (m ∗ n)

{-- associativity & priorities 
	(aka syntax declarations) --}
infixl 60 _+_
infixl 70 _*_

```

Actually, to have efficient natural numbers and to be able to use decimal notation without having to abuse `succ` we need to specify that they must be compiled as built-in machine integers via the `{−# BUILTIN NATURAL Nat #−}` pragma (similar pragmas exist for binary arithmetic). There are also many other built-in types.

An aside: all comments enclosed in `{-# ... #-}` are compiler directives.

### Importing modules

If we want to access a module `A`‘s functions from a module `B`, we have to tell Agda explicitly to import and open it:

```agda
module B where
	open import A
```

### Agda & Emacs

The best way to interact with Agda is via Emacs. Here is a basic cheatsheet:

- `C-c - C-l` (“load”) triggers type checking & loading (which, if it succeeds, triggers syntax highlighting!)
- `C-c - C-n`, where `n` stands for “normalise” or “evaluate to normal form” triggers expression evaluation (note that an Agda-program is a well-typed expression, so expression evaluation = program execution)
- `C-c - C-Space` (“give”) replaces a hole with his content and type checks it
- `C-c - C-r` (“refine”) refines a hole
- `C-c C-c` (“case split”) generates the clauses for pattern matching
- `C-c C-d` is the equivalent of GHCi’s `:t`
- `C-c C-x C-c` triggers compilation
- `C+c - C+c` somehow expands the patterns…? 
- `C+c - C+Space` does something else that is related, I guess

You can even use Unicode symbols (wherever in the code, even as function names). They are written as in LaTeX, so for instance `\to` is $\to$.

---
