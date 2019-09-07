% Strongly typed notes 
% Arianna Masciolini

# Introduction
Key idea of the course = __Curry-Howard isomorphism__,i.e.

> Programming = Mathematics, or Computer Science = Logic

And more precisely:

> _Terminating_ Functional Programming = _Constructive_ Mathematics

Object of the course: __dependently typed programming__.
_Dependent types_ come from predicate logic and are implemented in:

- Coq(uand) (the one used to prove the planar map theorem) -> algorithms correct by constructions (not under absolute terms)
- __Agda__
- (Haskell with `GADTs`)
- ...

## Types for software reliability
Software realiability (correctness) is hard to achieve because of:

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

`Set` is the only native type in Agda (it’s the _type of **data types** and **small types**_). Starting from `Set`, one can then construct function types.

```agda
-- module name = file name (mandatory)
module Bool where
	data Bool : Set where 
		true : Bool 
		false : Bool 
```

In the code above, we introduce a new data type `Bool` with two constructors (note that they are not capitalized). The Haskell equivalent would be:

```haskell
data Bool = True | False
```

Here we define a simple function:

```agda
-- see? Pattern matching!*
not : Bool -> Bool
not true = false
not false = true
```

Pattern matching allows _partial programming_ (programming with holes, question marks, partial refinement).

Here is an example of infix function (notice the underscores):

```agda
_&&_ : Bool -> Bool -> Bool
b && true = b
b && false = false
```

### Agda & Emacs
The best way to interact with Agda is via Emacs. Here is a basic cheatsheet:

- `ctrl+C - ctrl+L` triggers type checking & loading (which, if it succeeds, triggers syntax highlighting!)
- `ctrl+C - ctrl+C` somehow expands the patterns…? 
- `ctrl+C - ctrl+Space` does something else that is related, I guess

You can even use Unicode symbols (wherever in the code, even as function names). They are written as in LaTeX, so for instance `\to` is $\to$.

---
