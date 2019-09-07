% STM % Arianna Masciolini

# Lecture 1

## Intro

Key idea of the course = __Curry-Howard isomorphism__

> Programming = Mathematics
> _Terminating_ Functional Programming = _Constructive_ Mathematics ($\neq$ computation)
> Computer Science = Logic

Object: __dependently typed programming__ (see below).

Interesting talk: “Is Computer Science bad Mathematics?“

Predicates in predicate logic -> __dependent types__, implemented in:

- Coq(uand) (the one used to prove the planar map theorem) -> algorithms correct by constructions (not under absolute terms)
- __Agda__
- (Haskell with `GADTs`)

Related projects: Compcert (_verified compiler_ for a large subset of C. A verified compiler checks if the source and the target code have the same “meaning”).

Software realiability (correctness) is hard to achieve because:

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
- __types__
- …

## Reliability via types

“Invented” with high level languages.

Purposes:

- program behavior specification
- simplification of bug hunting (cf. type checking)
- optimisation

## Basic Agda stuff

`Set` is the only native type in Agda (it’s the _type of **data types** and **small types**_). You can then construct function types.

```agda
module Bool where -- same name as the file name
	data Bool : Set where -- introduction of a new data type, Bool
		true : Bool -- first constructor (not capitalized!)
		false : Bool -- first constructor (not capitalized!)

```

Haskell equivalent:

```haskell
data Bool = True | False

```

Emacs: `ctrl+C - ctrl+L` triggers type checking & loading (which, if it succeeds, triggers syntax highlighting!).

Now define a function:

```agda
-- see? Pattern matching!*
not : Bool -> Bool
not true = false
not false = true

```

* Pattern matching allows partial programming (programming with holes, question marks, partial refinement). Also, `ctrl+C - ctrl+C` somehow expands the patterns…? And `ctrl+C - ctrl+Space` does something else that is related, I guess

h and you can eve use Unicode symbols, t.e. `\to` is $\to$ (just like in LaTeX! and even as function names, for instance you could call `not` $\neg$ instead).

```agda
_&&_ : Bool -> Bool -> Bool -- infix function
b && true = b
b && false = false

if_then_else_ : Bool -> Bool -> Bool -> Bool

```



---

### Bookshelf

