/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
--import Mathlib.Tactic
import VersoManual
import DemoTextbook.Exts.Exercises

open Verso.Genre Manual
open DemoTextbook.Exts (lean)

set_option pp.rawOnError true
set_option maxRecDepth 1000

#doc (Manual) "Normalization by Evaluation in Lean4" =>

%%%
authors := ["Jeremy Sorkin"]
%%%

# Introduction

For this project, I chose to formalize Peter Dybjer's [Normalization-by-Evaluation](https://www.cs.le.ac.uk/events/mgs2009/courses/courses.html#anchorPeter) slides into Lean4.
My motivation for doing this was for 2 primary reasons:
- It's an interesting normalization-strategy for rewriting systems that leverages on the interplay between the "Object" and "Meta"-levels in a nontrivial manner.
- It also provides a nice oppurtunity for me to further sharpen and apply my Lean4 skills

The goal of this document is to walk the reader through both Dybjer's slides and their Lean4 formalization in a step-by-step manner.
# Motivation

Normalization by Evaluation is a technique whereby we can normalize terms of a given rewrite-system by "evaluating" them into the Meta-level (where normalization occurs)
followed by "reifying" our normalized term back into the Object-level. In this way, we will be translating our "reduction-based" rewriting-relation into a "reduction-free" equality check
that will let us show, among other results, decidability of rewriting.
As a normalization technique, has a history of application to different type systems:

  - [Berger and Schwichtenberg (1991)](https://www.mathematik.uni-muenchen.de/~schwicht/papers/lics91/paper.pdf) utilize Nbe to give a normalization-procedure for Simple Type Theory with βη-rewriting.
  - [MINLOG proof-assistant](https://www.mathematik.uni-muenchen.de/~logik/minlog/) utilizes Nbe as a normalization procedure for minimal first order logic.
  - [Coquand and Dybjer 1993](https://www.cse.chalmers.se/~peterd/papers/GlueingTypes93.pdf) utilize Nbe to give a decision algorithm for Combinatory logic as well as implement its
    formal correctness-proof in the ALF proof-assistant.
  - [Filinski and Rohde 2005](https://tidsskrift.dk/brics/article/view/21870) extended NbE to the Untyped Lambda-Calculus using an infinitary-variant of normal-forms, Bohm Trees.
  - [Abel, Dybjer, Coquand 2007](https://www.cse.chalmers.se/~peterd/papers/NbeMLTTEqualityJudgements.pdf) have extended the technique to Martin-Loff Type Theory.


For our purposes, we will focus on the simpler-examples of rewriting in Monoids and a Combinatory-version of Godel's System T.

# Monoid-Rewriting

## Monoid Expressions and rewriting

Let’s start with the simple case where we are rewriting in a Monoid.
Our Monoid-Expressions are:

```lean
inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α
infix : 100 " ⬝ " => Exp.app
```

That is, an expression is either:
  - Applying two expressions together: `e₁ ⬝ e₂`
  - The identity element `id`
  - An element of `α`


We know that a Monoid has an identity element and is associative, so we naturally get
the following rewrite-relation `~`:

```lean
inductive convr : (Exp α) → (Exp α) → Prop
| assoc         : convr ((e ⬝ e') ⬝ e'') (e ⬝ (e' ⬝ e''))
| id_left       : convr ((Exp.id) ⬝ e) (e)
| id_right      : convr (e ⬝ Exp.id) (e)
| refl          : convr (e) (e)
| sym           : convr (e) (e') → convr (e') (e)
| trans         : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
| app           : convr (a) (b) → convr (c) (d) → convr (a ⬝ c) (b ⬝ d)
infix : 100 " ~ " => convr
```

The first 3 constructors are the normal Monoid-laws, the next 3 ensure `~` is an equivalence-relation, and the final ensures it is congruent wrt `app`.
This gives us the normal Monoid-behavior we expect as the following examples show:

```lean
def zero := (Exp.id : Exp Nat)
def one  := Exp.elem 1
def two  := Exp.elem 2
def three := Exp.elem 3

-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example1
        : ((one ⬝  two) ⬝ ((zero ⬝  zero) ⬝  three))
        ~ (one ⬝  (two ⬝  (three ⬝  zero))) :=
  by
  -- Hint:
  -- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ (1 ⬝ 2) ⬝ (0 ⬝ 3)
  -- (1 ⬝ 2) ⬝ (0 ⬝ 3) ~ (1 ⬝ 2) ⬝ 3
  -- (1 ⬝ 2) ⬝ 3 ~ (1 ⬝ 2) ⬝ (3 ⬝ 0)
  -- (1 ⬝ 2) ⬝ (3 ⬝ 0) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/Rs4AACWoGBREApteBHDsBx7KcBxrIdm3HTtx14XtB0glD2zQ7tMKQu0cNg8c61sIDoNQxCiMo3C4MnPsrzgCiYLwicEKImDeDHbsGLgadfzyKAoEkIA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/YRglQS1xF4U8T39Pc7V9KCExhH45iBGBAKQYCWzA8CoMg9J9x4Ms3yHPgIJOAi4VEIMEJOEC3SgHBAWBVDgLHTD716Xc8MPbCPygziyK/X9rxglo2Pw7NOKw49SNfOQ4go2itTxeigRBVA01sIC2FQSdWKod92PE58SPYmSBKEm89lEuAOPPS94KUk4EIYkFeAQ2YFhgK84E07yABYojvPSd0M6S7ME69b0C/SxLPB8yJwvc5MohzeiclS+DcmgZiuW4YBwJEQDiJitIAVgCqybLimSErM8zbysx9s2feKeNw795Ko3J8l/QhXCQSIaLU39f0bZtx07cceynAcayI3gRw7AdeF7Qdfw6dBJAUikqRpVAxxGpt5vGpaVtm4SFom9s61sdbNoQ7bqW8664FGo720u2tzuOybJz7Lzbq2ylHtQXyDrG96lt+uB+xghbeDHbsoenNbVA2wGdu8krf0XIh4DS4EgA)

```lean
-- (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example2
  : ((zero ⬝ (one ⬝ zero))  ⬝  ((zero ⬝ two) ⬝ (three ⬝ zero)))
  ~ (one ⬝ (two ⬝ (three ⬝ zero))) :=
  by
  -- Hint:
  -- (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ (1 ⬝ 0) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0))
  -- (1 ⬝ 0) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0))
  -- 1 ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/YRglQS1xF4U8T39Pc7V9KCExhH45iBGBAKQYCWzA8CoMg9J9x4Ms3yHPgIJOAi4VEIMEJOEC3SgHBAWBMhG2bcdO3HHspwHGsiN4EcOwHXhe0HVDgLHTD716Xc8MPbCPyg6SyK/X9rxgloJPw7NpKw49SNfOQ4go2itTxeigRBVA02Y3jWIEoTuNUvi2PbOtbCAthUEncSqHfSTNOfEjJL0pSVJvPZ1LgKTz0veCTJOBCGJBXgENmBYYHkKzHK4hybPYyc+yvOA3MKgAWKI728nc/N06LlOvW9yp8jSzwfMicL3AzKNi3p4rMvhkpoGYrluGAcCREA4iYptrPbJyJ04mC+N4MduzyuBpxE9yAFYyvCyKWr0trgpC29wsfbNn1auTcO/QyqNyfJf0IVwkEiGiLN/Dp0EkIyKSpGlUDHD7VC+n7KWpQqXOUYHvoQ37wdQYqgbAEHYbB/7Nt/RciHgHrGMmvghOmtbv27QTx343LOKIxblrm/KZzcecKiXFcWGLLZtIgZ9ws/LTOcq5rehfctDoKk6Kpa879pFq72o639/1/ZiAAlqBgUQlamwm+OndiyfbCmVqp7L8r1oTDbp4mCoy+bSfN2beFW3XhzN8mHado7mMW/XbHd42XdHSn6d/PIoCgSQgA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/YRglQS1xF4U8T39Pc7V9KCExhH45iBGBAKQYCWzA8CoMg9J9x4Ms3yHPgIJOAi4VEIMEJOEC3SgHBAWBMhG2bcdO3HHspwHGsiN4EcOwHXhe0HVDgLHTD716Xc8MPbCPyg6SyK/X9rxgloJPw7NpKw49SNfOQ4go2itTxeigRBVA02Y3jWIEoTuNUvi2PbOtbCAthUEncSqHfSTNOfEjJL0pSVJvPZ1LgKTz0veCTJOBCGJBXgENmBYYHkKzHK4hybPYyc+yvOA3MKgAWKI728nc/N06LlOvW9yp8jSzwfMicL3AzKNi3p4rMvhkpoGYrluGAcCREA4iYptrPbJyJ04mC+N4MduzyuBpxE9yAFYyvCyKWr0trgpC29wsfbNn1auTcO/QyqNyfJf0IVwkEiGiLN/Dp0EkIyKSpGlUDHD7VC+n7KWpQqXOUYHvoQ37wdQYqgbAEHYbB/7Nt/RciHgHrGMmvghOmtbv27QTx343LOKIxblrm/KZzcecKiXFcWGLLZtIgZ9ws/LTOcq5rehfctDoKk6Kpa879pFq72o639/w2wrQOI2ShZ5+S+YCpqtMu3pedqjdxca2DcOffnSKqoW9Z4XmYqaZ9+qQxY4lx9AlYsqINbNh8Ld8wWRht032sN1F7VOv2dYug7ZZuzqHYfJ2hruV2TISj2xNjCWhcjiKrcDmP9c10PQXD7PA6l63C9tzX7YiYyHYSvqup4J3UqMhKCqswm+OndiyfbCmVqp7L8v7oSh7p4mCs+mGTLh/6zV/DL5tJifZt4Va++HcfyY3rejtn0G/sKtNbGYxaB9sfeR530dKfppGUfntHCvZ5nsY7sygA)

```lean
-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0))
theorem example3
  : ((one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three))
  ~ ((zero ⬝ (one ⬝ zero)) ⬝ ((zero ⬝ two) ⬝ (three ⬝ zero))) :=
  by
  -- Hint: Use examples 1 and 2!
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/YRglQS1xF4U8T39Pc7V9KCExhH45iBGBAKQYCWzA8CoMg9J9x4Ms3yHPgIJOAi4VEIMEJOEC3SgHBAWBMhG2bcdO3HHspwHGsiN4EcOwHXhe0HVDgLHTD716Xc8MPbCPyg6SyK/X9rxgloJPw7NpKw49SNfOQ4go2itTxeigRBVA02Y3jWIEoTuNUvi2PbOtbCAthUEncSqHfSTNOfEjJL0pSVJvPZ1LgKTz0veCTJOBCGJBXgENmBYYHkKzHK4hybPYyc+yvOA3MKgAWKI728nc/N06LlOvW9yp8jSzwfMicL3AzKNi3p4rMvhkpoGYrluGAcCREA4iYptrPbJyJ04mC+N4MduzyuBpxE9yAFYyvCyKWr0trgpC29wsfbNn1auTcO/QyqNyfJf0IVwkEiGiLN/Dp0EkIyKSpGlUDHD7VC+n7KWpQqXOUYHvoQ37wdQYqgbAEHYbB/7Nt/RciHgHrGMmvghOmtbv27QTx343LOKIxblrm/KZzcecKiXFcWGLLZtIgZ9ws/LTOcq5rehfctDoKk6Kpa879pFq72o639/w2wrQOI2ShZ5+S+YCpqtMu3pedqjdxca2DcOffnSKqoW9Z4XmYqaZ9+qQxY4lx9AlYsqINbNh8Ld8wWRht032sN1F7VOv2dYug7ZZuzqHYfJ2hruV2TISj2xNjCWhcjiKrcDmP9c10PQXD7PA6l63C9tzX7YiYyHYSvqup4J3UqMhKCqswm+OndiyfbCmVqp7L8v7oSh7p4mCs+mGTLh/6zV/DL5tJifZt4Va++HcfyY3rejtn0G/sKtNbGYxaB9sfeR530dKfppGUfntHCvZ5nsY7syGymzLd7H5yPEe4jzXnvASB8GZzgXCzZGLBIZgV2vnWwLRtbBwUkFX8t5UENVFubVBe0q4yyLtdH8thFbnybAACWoDAcQABVbIJQYGuBpC2KkNhCwAEJfx5CgFASQQA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgzgA7AEwFdjgA3AUzgFEAPMOACiXRhUSOAC44eAJ5gWASjIAfOEjA9xXHgKEjASYQduywcLh6Nh7YrjAacMfs1GklluhYg7W46YOenlWgwkrHCEEFRMUHa8Zr6yJnwxjnF6AApQEGCWSADO2RCEcADebCwA5HBl5eo+jgC+dqHhkby8LDgqPGWy7aoVpaVxrT08raXDfQPyStYA+q4AZvDFttUO2vW2KyFhEXzR3DjW3R0Vg3KWs1DAAOaoS2yr5sIbm+KNu0MnGoc0Z1NwUBY83Qm1sy0evheW3ezTkfHOSmykncoKKJSq9ieSA2bx2sLOA3iMPhhNa/xgUCQVGyaL6EzsiXWDTx8IJyW2TRJBMJemJZJJAyyvUKIiwITgNghdVBuM5/EGWHZfMIg1+RJZ/HGKr4uBOv3882AnDsAEYAAxmuAAIjgAD9rXAALwAPg5EQoZBoQLgAC8WOkxI6EgdrAyDIBUQnkXvmcDCbED9hwLjccBNnu9MAA7hAVkHvsn3AAmdMxtCAh55g4FuAAZgoAFp63wTXBALjUcELcXbLUt7bNXdrcXtLe7hbbfBr4/78lcIBAIhYnCQ4FcLbIqNefDj4yzEGOvT2fvS4yPe53qHL8g3tntvG3J14u/Gj4vLDaJ1Psi/gfXcCwkl/YRglQS1xF4U8T39Pc7V9KCExhH45iBGBAKQYCWzA8CoMg9J9x4Ms3yHPgIJOAi4VEIMEJOEC3SgHBAWBMhG2bcdO3HHspwHGsiN4EcOwHXhe0HVDgLHTD716Xc8MPbCPyg6SyK/X9rxgloJPw7NpKw49SNfOQ4go2itTxeigRBVA02Y3jWIEoTuNUvi2PbOtbCAthUEncSqHfSTNOfEjJL0pSVJvPZ1LgKTz0veCTJOBCGJBXgENmBYYHkKzHK4hybPYyc+yvOA3MKgAWKI728nc/N06LlOvW9yp8jSzwfMicL3AzKNi3p4rMvhkpoGYrluGAcCREA4iYptrPbJyJ04mC+N4MduzyuBpxE9yAFYyvCyKWr0trgpC29wsfbNn1auTcO/QyqNyfJf0IVwkEiGiLN/Dp0EkIyKSpGlUDHD7VC+n7KWpQqXOUYHvoQ37wdQYqgbAEHYbB/7Nt/RciHgHrGMmvghOmtbv27QTx343LOKIxblrm/KZzcecKiXFcWGLLZtIgZ9ws/LTOcq5rehfctDoKk6Kpa879pFq72o639/w2wrQOI2ShZ5+S+YCpqtMu3pedqjdxca2DcOffnSKqoW9Z4XmYqaZ9+qQxY4lx9AlYsqINbNh8Ld8wWRht032sN1F7VOv2dYug7ZZuzqHYfJ2hruV2TISj2xNjCWhcjiKrcDmP9c10PQXD7PA6l63C9tzX7YiYyHYSvqup4J3UqMhKCqswm+OndiyfbCmVqp7L8v7oSh7p4mCs+mGTLh/6zV/DL5tJifZt4Va++HcfyY3rejtn0G/sKtNbGYxaB9sfeR530dKfppGUfntHCvZ5nsY7syGymzLd7H5yPEe4jzXnvASB8GZzgXCzZGLBIZgV2vnWwLRtbBwUkFX8t5UENVFubVBe0q4yyLtdH8thFbn1/jlUBADBwLXYrTTeI8n5zwdgvD+rMz5wAvvQh+09VLAPpv/a+4CqbMOPuDLGrNCyjWRJjJcxAv7AiAA)

## Normalization of Monoid-Expressions

From the examples above, we can see that showing `a ~ b` step-by-step can be rather tedious.
When checking this in practice, we simply preform all these steps simultaneously by:

"removing all the `id`'s, shuffling parentheses to the right, then checking for equality"

Can we implement this normalization strategy by interpreting our Monoid-Expressions in a clever way?

## Evaluation

This is exactly what evaluation does, it interprets our expressions such that normalization happens automatically at the Meta-level.
We will do this by interpreting Monoid-Expressions as functions, the "intended"-meaning:
  - `app` will be function-composition
  - `id` will be the Identity-function
  - `x` will be `λ e ↦ x ⬝ e`: Applying `x` to the left

This gives us our evaluation function:

```lean
def eval : (Exp α) → (Exp α → Exp α)
  --               (eval a) ∘ (eval b)
  | Exp.app a b => (λ e => eval a (eval b e))
  --               Identity function
  | Exp.id      => id
  --               λ e ↦ x ⬝ e`
  | Exp.elem x  => (λ e => (Exp.elem x) ⬝ e)
```

Now, by interpreting Monoid-expressions as function-compositions at the Meta-level,
Lean will automatically normalize these compositions as the following shows:

```lean
-- fun e => Exp.elem 1 ⬝ (Exp.elem 2 ⬝ (Exp.elem 3 ⬝ e))
#reduce eval $ (one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three)

-- fun e => Exp.elem 1 ⬝ (Exp.elem 2 ⬝ (Exp.elem 3 ⬝ e))
#reduce eval $ (zero ⬝ (one ⬝ zero)) ⬝ ((zero ⬝ two) ⬝ (three ⬝ zero))

-- fun e => Exp.elem 1 ⬝ (Exp.elem 2 ⬝ (Exp.elem 3 ⬝ e))
#reduce eval $ (one ⬝ (two ⬝ (three ⬝ zero)))
```

From the above examples, we see that the evaluations of

`(1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ (0 ⬝ (1 ~ 0)) ⬝ ((0 ⬝ 2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))`

are all equal to: `λ e ↦ 1 ⬝ (2 ⬝ (3 ⬝ e))`.

That is, rewritable-terms give us equal evaluations:

```lean
-- a ~ b  → eval a = eval b
theorem convr_eval_eq {a b : Exp α} (h : a ~ b) : ∀ c, (eval a) c  = (eval b) c :=
    by
    -- Hint: Induction on h
    sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTKBWBaKBfyBCCrCgVY6ACjqEBWGmBxiEc2FkaBhAYiEGJYqJt5NnMoH1GYyYQM2NlwFheDas4VhOViUBQPJRkmTUGhCmIIrYdZzp2QwDZOS5bnAB5zpeT5FD1MZtgBQK2p6vARGzE5EUOWRzoxUEcXoJ50BJX5aUOoRL55aY9lRUVNCuSV8XSolvkpf5/rtJZSAZQKjbAKgYXSsV7llQlFVdUC/nJqmBlNgN1GNlgg2iSNAw1KgChjfUE2leV3mzalpm5Etol1AKcA3Ug60jUCgWPftQKtPpABUznZA9bGEM9qD1Y1YhOX4c4QOgdQEdFNAABJ2SwADCFX7DA6BaLc9yPCQKCmb92SmHU/0Co9x1JUAA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrAUPUjxaAKOoQFYnCgfUZjJhAnAANzZGIWLLKBhAYiEN5MaJdQCnATlIFgArAGxhAaO5bFzHpQKtEccAAFRwDQrk+UC3kef5BkMES/mcCkhDAFYwAAF4hF5kViIlyWpZgmXZG5HkKgRzYwhqzqcKAUQgugWhwAA2gRAC6/lQNIzXZR57XOp1zURb1QA)

In addition, we will need the following lemma relating `eval` to `app`:

```lean
-- ∀ b, a ⬝ b ~ (eval a b)
theorem app_eval (a : Exp α) : ∀ b, (a ⬝ b) ~ (eval a b) :=
    by
    -- Hint: Induction on a
    sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBF+VhAAS+kNAAwtADjEPVtz3I8JAoJlEWPHUz0JZD8nXbYNR1L5zpYXg2rOFY6NQFAmP1FZ2PIe0RGvfjNCE0E+Wk+TQA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrQA)

## Reification

Now that we can evaluate our Monoid-expressions such that they're normalized at the Meta-level, how do we bring them back down to the object-level such that we don't change the "behavior" (wrt `~`)?
Well, for a given `e : Exp α`, we intuitively know that `eval e : Exp α → Exp α` will have the form:

`λ e' ↦ elem x₁ ⬝ (elem x₂ ⬝ ... ⬝ (elem xₙ ⬝ e'))`

So to reify it back down while retaining its `~`-behavior, simply apply `Exp.id` to the end:

```lean
def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id
```

## Nbe

With our two main functions in place, we are finally ready to define our `nbe`-algorithm:

```lean
def nbe (e : Exp α) : Exp α := reify (eval e)
```

What `nbe` does is first evaluate `e` so it gets normalized through function-composition, and then reify's it back into a canonical element of `[e]~`.
Thus, we can translate `a ~ b` into the decidable-problem `nbe a = nbe b` which we state as our main correctness-theorem:

`(e ~ e') ↔ (nbe e = nbe e')`

Before we move onto the proof of correctness, we introduce an additional key lemma showing nbe really does return a element of `[e]~`:

```lean
theorem convr_nbe (e : Exp α) : e ~ (nbe e) :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYfNVECqX5fMYU60hGurfPnnoFyaBWEABL6SwXfPpMNyD2FZ1wH4TuLQD9RYlAUBaEAA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYfNVECqX5fMYU60hGurfPnnoFyaBSMo2jz5TfSAHDnnMSk/67Sk1qupsBzWs09P9N62mgtG5ZAVm0ooHR/Ai0NxPQA)

We are now ready to prove our algorithm correct:

```lean
theorem correctness {e e' : Exp α} : (e ~ e') ↔ (nbe e = nbe e') :=
    by sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYfNVECqX5fMYU60hGurfPnnoFyaBSMo2jz5TfSAHDnnMSk/67Sk1qupsBzWs09P9N62mgtG5ZAVm0ooHR/Ai0NxPw1wGcqAQLIzZAxoLnAJgMANRAu5dyGZCnNAKHAlADjEDTmJOQhnbuUbOb9GRwEACmEMQe4ITgLAmMfcB71CWPVOAABJTwnghDvQYKBAA7bcD6ds3ZnX+MIS6JDpRqQ0lpdAOkgymXMn5R2IRwDyyiLee62QBTUUbI9aiDknIvj8g7XewVQo8L4UCXhAoNCiNCjQAAEvpFgABVJ2XolpWHogorEv95IEKIXFc20osIqPeuop2gtHgPUjC3MuCVoBQC0EAA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYfNVECqX5fMYU60hGurfPnnoFyaBSMo2jz5TfSAHDnnMSk/67Sk1qupsBzWs09P9N62mgtG5ZAVm0ooHR/Ai0NxPw1wGcqAQLIzZAxoLnAJgMANRAu5dyGZCnNAKHAlADjEDTmJOQhnbuUbOb9GRwEACmEMQe4ITgLAmMfcB71CWPVOAABJTwnghDvQYKBAA7bcD6ds3ZnX+MIS6JDpRqQ0lpdAOkgymXMn5R2IRwDyyiLee62QBTUUbI9aiDknIvj8g7XewVQo8L4UCXhAoNCiNYPzbIAiBRYBbJ2DkE4ppTnKrLUmN5ZH8NkfIxhh9m60TEAxIghi6iF3kQQohcVzbSiHgLAYDQ36wL0ZGFuZd4p9SptrNeSsN6sHcdvZ0XMebuMptIbUMAQiNVRr1L2VsY6KzBL4/ErIcCzyAA)

With `correctness` in place, Lean can now instantly decide any `a ~ b` problem through reflexivity, i.e.:

```lean
-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example1'
        : (one.app two).app  ((zero.app zero).app three)
        ~ (one.app (two.app (three.app zero))) :=
  by
  exact (correctness).mpr rfl

-- (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example2'
  : (zero.app (one.app zero)).app ((zero.app two).app (three.app zero))
  ~ (one.app (two.app (three.app zero))) :=
  by
  exact (correctness).mpr rfl

-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0))
theorem example3'
  : (one.app two).app  ((zero.app zero).app three)
  ~ (zero.app (one.app zero)).app ((zero.app two).app (three.app zero)) :=
  by
  exact (correctness).mpr rfl
```
# GodelT-Rewriting

## GodelT Expressions and rewriting
We now move on to a Combinatory-version of Godel's System T and implement NbE for it as well.
Here we will be using an Intrinsic encoding (aka "typing ala Church") meaning all Expressions will be well-typed and we won't need an additional "Derivation" type.
First, we define our Simple-Types:
```lean
inductive Ty : Type
| Nat : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow
```
Here our base-type is the Natural Numbers while `arrow` lets us form functions between Simple Types.
Our Expressions are:
```lean
inductive ExpT : Ty → Type
| K {a b : Ty}     :  ExpT (a ⇒' b ⇒' a)
| S {a b c : Ty}   :  ExpT ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))
| App {a b : Ty}   :  ExpT (a ⇒' b) → ExpT a → ExpT b
| zero             :  ExpT .Nat
| succ             :  ExpT (.Nat ⇒' .Nat)
| recN {a : Ty}    :  ExpT (a ⇒' (.Nat ⇒' a ⇒' a) ⇒' .Nat ⇒' a)
open ExpT
infixl : 100 " ⬝ " => App
```
That is, our Expressions are either:
  - Combinators `K` and `S`
  - Applying two expressions together: `e₁ ⬝ e₂`
  - The Natural number `zero`
  - The successor function `succ`
  - The recursor for Natural numbers: `recN`

From this, we get the following rewriting relation for `~`:
```lean
inductive convrT : (ExpT α) → (ExpT α) → Prop
| refl  : convrT (e) (e)
| sym   : convrT (e) (e') → convrT (e') (e)
| trans : convrT (e) (e') → convrT (e') (e'') → convrT (e) (e'')
| K     : convrT (K ⬝ x ⬝ y) (x)
| S     : convrT (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app   : convrT (a) (b) → convrT (c) (d) → convrT (a ⬝ c) (b ⬝ d)
| recN_zero : convrT (recN ⬝ e ⬝ f ⬝ .zero) (e)
| recN_succ : convrT (recN ⬝ e ⬝ f ⬝ (.succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))
infix : 100 " ~ " => convrT
```
Some rewriting examples are:

```lean
-- Identity Combinator
def I {β : Ty} : ExpT (α ⇒' α) := (@ExpT.S α (β ⇒' α) α) ⬝ .K ⬝ .K

example {x : ExpT α}
        : ((@I α β) ⬝ x)  ~  x :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbwQFAABJbgVQ8FBwgAYTgfhpFscxDFqvSqs2fcNIYl0QoiXoLgAAR+IgXhdRjjJBL1cKIO9QEW7xKBqcRTHkLS/lGnqPxBe8QVAErQD/XoJ34NJDkqgAJaQUHgCdKp6+8nrAPpQEw0AlqWmo3sOE7ftw29cJff7jtOidMHMSBeCAA)
[Solution](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbwQFAABJbgVQ8FBwgAYTgfhpFscxDFqvSqs2fcNIYl0QoiXoLgAAR+IgXhdRjjJBL1cKIO9QEW7xKBqcRTHkLS/lGnqPxBe8QVAErQD/XoJ34NJDko9B5HCZsiE7btewel4AH4lInG67oi21Hq7HtfsgRbQA+ic1rcSwHtDeQgA)

```lean
-- B Combinator
def B {a b c : Ty} : ExpT ((b ⇒' c) ⇒' (a ⇒' b) ⇒' a ⇒' c) := .S ⬝ (.K ⬝ .S) ⬝ .K


example {x : ExpT (b ⇒' c)}
        {y : ExpT (a ⇒' b)}
        {z : ExpT a}
        : (B ⬝ x ⬝ y ⬝ z)  ~  (x ⬝ (y ⬝ z)) :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbwQFAAAhUAAGE4H4aRbHMQxuEoPSaro69PgYmSAREqFJXxGV+pBeBelATCLjvSaQX1VZTUoGpxFMeQQl/fS+qBUKk3Azahp29kNgQ/9xC46lEHOGqsJwsiQVAEqLgfC5SLwlKIl6Cd+DSQ5KoACWkFB4AnSrrtAZ7XrJEGwAmqbb1wp45tAGaIcI6GHumhGkee+H7yRyH0ZKuGUfxtHfrAErcfBwikZImnCep4jIceQ5MHMSBeCAA)
[Solution](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbwQFAAAhUAAGE4H4aRbHMQxuEoPSaro69PgYmSAREqFJXxGV+pBeBelATCLjvSaQX1VZTUoGpxFMeQQl/fS+qBUKk3Azahp29kNgQ/9xC46lEHOGqsJwsiQVAEqLgfC5SLwlKIl6Cd+DSQ4/CkfRoHkdiqonSj0HkcJmyITtu17AB+JTQARiclrcSxb1wp45tAZ6MfvbHXrJCcAHaMiRCGIttIgwaRxGodDeQwrBimoZphHKcgIgGbC1H3A5ognhJsnwchhdoa7Htadpnnlr5qa8ZxgnCLC0nmdF1Nqao9n6faxnaTV/m2bpsXuf18n1apo3+dNmlecsKGFupVXzf5mHJfZ5HaTt6bcOe/DcJIwjHlpUnvahwWQ+FlmxatnWwzC6kw7F1YgA)


```lean
def add (m : ExpT .Nat) := .recN ⬝ m ⬝ (.K ⬝ .succ)

-- m + 0 ~ m
example : (add m ⬝ .zero)  ~  m :=
  by
  sorry

-- m + (succ n) ~ succ (m + n)
example : (add m ⬝ (.succ ⬝ n))  ~  (.succ ⬝ (add m ⬝ n)) :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbxuEoPTxG4djzjzLzbBBeBegFSghVwvNiLvUAEseQwQFAPMAGpQEKkrYEMSganEUx5C0y5aqGwi7MOErlpaid+DSQ5BoACWkFBEAAIXCa0QmgPToD8eoLKK1Q/HmzAJ0wcxIDSAawBG+LWVAZLQBKhKLm+5KppmuaFpq9iup+lzcOSkEAcOc4geIqHlqSlKIl6LadtAfbDsQCdBvRmGUd+zHibAVrMrJnq+tw8m4cp3awBK29cIZpLGdpxn6dZEEWfx6mLn5lzBb+xnSfhx5WaR1GcSWmHQcOV6sl4IA)
[Solution](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbxuEoPTxG4djzjzLzbBBeBegFSghVwvNiLvUAEseQwQFAPMAGpQEKkrYEMSganEUx5C0y5aqGwi7MOErlpaid+DSQ5prcSxmyIRzVOgU1BpG+LWVAZLQBKhKLgu5KppmuaFpq9iusulzcOSkFbsOc57uI97lqSlKIl6LadtAPwpH0aB5HY96J0o9B5HCQ7O27XsAH4lNAPGJz29wLh6vqftw85Ms+29cPJsGJwAduLGaScOxyEqZjIkXRiLbSIVGCfx9mqvkMLiYOhciFWIA)

```lean
def mult (m : ExpT .Nat) := .recN ⬝ .zero ⬝ (.K ⬝ (add m))

-- m * 0 ~ 0
example : (mult m ⬝ .zero) ~ .zero :=
  by
  sorry

-- m * (succ n) ~ m + (m * n)
example : (mult m ⬝ (.succ ⬝ n)) ~ ((add m) ⬝ (mult m ⬝ n)) :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbxuEoPTxG4djzjzLzbBBeBelAIhMrzYi71ABLHkMSq9NgPx5Eser9L5CJWsy1SqS63DLlq0BYFywwQCW0AACpQEKkrWEMSganEUx5C0+rhssTq8Ls0ASpmyaJ34NJDjWgAJaQUEQAAhcJrRCaA9OgPx6gsorVGGyhMAnTBzEgNJVrAPMtvOBLQGSm71oAaguRHUceA6jvQE6UjOkb1uIlGkpS9G/hq9jlvmobScu5Lmt6B6ntAV73sQCc1sZi75op3HebAKbKCFQjKXm7qFrpqnydZXDkpF6mZdppb5dR+bpqlubiPV5aQUplXWtveaDc19LsfOsnheesAStljWGZt5nHkOaGsl4IA)
[Solution](https://live.lean-lang.org/#codez=LTAEDECcHsFsC5QAsAuKAOBneB6HBjTAOgEtp8iBTSnSgd00JwCYAGVgThwBMBPAIwBWlSDlgBDEgDsACuIA2sTJWCRKANxLLuRdNwBmAKBKx00SClABZcSiTyS/IgBVx+FCXyHjU7gFd3EnVKUGdeUEQw9EpDAB9QADlbCNDeONBxSBg6FLDQQCTCVILUw2hoqRLpfRIAD0gUgEZ2UAAiUEAlwgByVtAAXgA+DKzoOm9pf0Dg0ABRGvRc8MKomPiAaVAAb3FQfgWAX1BDw8QZudAACm2unY7u8QBKdIBlTe3d/H2jk9n588vbm7XfD3AH/a78EHXMHdYGPeIAQXQ8y2N0ivAOx0OPwuV26EOK2O2hWx/HSAC8RNAjtSaSlTvMkih0pgAh9abTvmdzoyAYy4aA1PgEq9Pl8sVzcRceddJQ9eckZY8ypQKj8fNUavJGs02oBcah6A1AiPQ3h8Ew8U3w0Ck6nqiEABcCbQCNwPsADQXbFOkGFc6e72gGQwE3xNT6LUbF1ovYbEKIT17QzslJWm31c6UEHp/mYXiwI4R/Yx0CUbpxs5OhNJxAp20XDN1zr+mtpkuZjPpFCQcRSTDOwshEvFzql+mgCuJ9nV621rMNpvTluNhtLwrNutt4f89bUguAJuBCzUUvHNuEy/Nd5XJ6A1+d1vrD/reJmavyXjuXfvAM3AUY2h7PF0/AF92uL0Dg2U9R3OQDrl3e4wLJI8zk/S8OWvBcLhee9QEfbDQDJZ9cIQ/VznCfV8P5cQkXzD9PhRXZ/3OYDulAzYPm4RDzxQmkp1THFM3xVd0POYELm4edeP+fURPOXZ9TE9JBQSAB9CkYD7KNNljUcK02fQOKlBVmIBUCJ1Qm9FNwkJ9T0sjKTbflFKUll8A+AsNI2Cp/0ZMCtOPDY9IY6UjJAuDTO4tCJIs/UrNAGyLmcj59Ske5MziipiKi4tcLSlL1VqbVWB6AA/A1BmbbxuEoPTxG4djzjzLzbBBeBelAIhMrzYi71ABLHkMSq9NgPx5Eser9L5CJWsy1SqS63DLlq0BYFywwQCW0AACpQEKkrWEMSganEUx5C0+rhssTq8Ls0ASpmyaJ34NJDgOtxLGbdrKCFFTKW8Na8y284EtAZKbvWgBqC5/uBx4XuO06hpG9biKBpKUtBv4avY5b5oRi7cOS5regep7QD8KR9GgeQsfOidKPQeRwneztu17AB+JTQHZicXvcC5uoWrG0aS+bpspeb+cxpahehicAHbi0O3n3schK5YyJEGYi20iDpzmOeVqr5DCnm3oXIhViAA)

```lean
def power (m : ExpT .Nat) := .recN ⬝ (.succ ⬝ .zero) ⬝ (.K ⬝ (mult m))

-- m ^ 0 ~ 1
example : (power m ⬝ .zero) ~ (.succ ⬝ .zero) :=
  by
  sorry

-- m ^ (succ n) ~ m * (m ^ n)
example : (power m ⬝ (.succ ⬝ n)) ~ ((mult m) ⬝ (power m ⬝ n)) :=
  by
  sorry

-- m ^ 3 ~ m * (m * m)
example : (power m ⬝ (.succ ⬝ (.succ ⬝  (.succ ⬝ .zero))))  ~  (mult m ⬝ (mult m ⬝ m)) :=
  by
  sorry
```

## Normalizing Godel-T Expressions
In this instance, implementing Evaluation and Reification will be trickier than the previous case because
we will need to evaluate Types and Terms and Term-Evaluation will depend on reification.
So, we will implement it in the following order:
  - Evaluate Simple Types to Meta-Level Types
  - Reify Meta-level Expressions to Godel-T Expressions
  - Evaluate Godel-T Expressions to Meta-Level Expressions

So now for our first question in implementing NbE: how will we evaluate Simple Types to the Meta-level?

## Evaluating Simple Types
To do this, we will make use of Tait's reducibility method and a constructive proof of Weak Normalization to
extract our NbE algorithm.

With the Reducibility method, we define "Reducibility" in such a way that strengthens our Inductive Hypothesis
and allows us to prove Weak Normalization. The main idea is: functions will be considered reducible if they map
reducible inputs to reducible outputs while base terms will be considered reducible if they are Weakly-Normalizing.

From this, we get the following definition for Reducibility:

`Red_{Nat}(e)           = WN_{Nat}(e)`

`Red_{alpha -> beta}(f) = WN_{alpha -> beta}(f) & Forall x : alpha, Red_{alpha}(x) -> Red_{beta}(f x)`

Now, to get our constructive NbE algorithm, we are going to remove all intermediate proof terms (witnessing Weak-Normalization)
from our `Red` relation and only keep the returned Expressions.

Doing this gives us our Evaluation Function for Simple Types:
```lean
def Ty_inter : Ty → Type
| Ty.Nat => Nat

| Ty.arrow a b => ExpT (a ⇒' b) × (Ty_inter a → Ty_inter b)
```
Here:
  - For `Ty.Nat`: we give it the standard interpretation of Lean's Natural Numbers
  - For `a ⇒' b`: given a `f : ExpT (a ⇒' b)`, we "glue" onto it a function `F : (Ty_inter a → Ty_inter b)`
    describing how `f` behaves when applied to normalized-arguments. This will be more clear when we evaluate Godel-T Expressions.

## Reification and Semantic-Application
In order to Evaluate Godel-T terms, we must first describe how to reify Meta-level terms back to Godel-T terms.
This is because, when defining the glued-on semantic function `F : (Ty_inter a → Ty_inter b)` we will need reification to be able
to apply `f : ExpT (a ⇒' b)` to reified semantic arguments.

Defining reification in this instance is simple because of how we evaluate types:
  - For `n : Ty_inter Ty.Nat = ℕ`: Return the standard numeral `succ ⬝ succ ⬝ ... ⬝ zero  :  ExpT Ty.Nat`

  - For `(f, F) : Ty_inter (a ⇒' b) = ExpT (a ⇒' b) × (Ty_inter a → Ty_inter b)`: Return `f : ExpT (a ⇒' b)`

This give us the following reification function:
```lean
def numeral : Nat → ExpT Ty.Nat
| 0 => .zero
| n+1 => .succ ⬝ (numeral n)


def reifyT (a : Ty) (e : Ty_inter a) : ExpT a :=
/-
| Ty.Nat, e            => numeral e

| Ty.arrow a b, (c, f) => c
-/
by
  cases a
  case Nat        => exact numeral e
  case arrow a b  => exact e.fst
```
In addition, we will need to define application on the Meta-level where our glued-on function `F : (Ty_inter a → Ty_inter b)`
comes into play:
  - For `(f, F) : Ty_inter (a ⇒' b) = ExpT (a ⇒' b) × (Ty_inter a → Ty_inter b)` and `e' : Ty_inter a`:  Return `F e' : Ty_inter b`

which gives us:
```lean
def appsem {a b : Ty} (t : Ty_inter (a ⇒' b)) (e' : Ty_inter a) : Ty_inter b := (t.snd e')
```

## Evaluating Godel-T Expressions
With all of the constituents in place, we are finally able to Evaluate Godel-T Expressions to Meta-level terms.
Before giving the formal definition, we first describe how the Evaluation works on an example to give some intuition.

For `zero : ExpT Ty.Nat` and `succ : ExpT (Ty.Nat ⇒' Ty.Nat)`, these will get their standard translations of `0 : ℕ` and `λ n : ℕ ↦ n+1`.

For a generic function `f : ExpT (α =>' β)`, we are going to keep applying `f` to reified semantic-arguments until
`f ⬝ (reify x1) ⬝ ... ⬝ (reify xn)` is fully-applied, then we will use `f`'s standard-translation on `x1, ..., xn`. This will in-effect
capture all of `f`'s `~`-behavior into one big tuple which is how `F : Ty_inter a → Ty_inter b` works.

We illustrate this with the example `S :  ExpT ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))`.

The first step is to evalute `S`'s type to the Meta-level, for readibility let:

`τ := (a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c)`

`τ' := (a ⇒' b) ⇒' (a ⇒' c)`

`τ'' := a ⇒' c`

and

`⟦ ⬝ ⟧ := Ty_inter`

Then we get:

`⟦τ⟧ = ExpT τ × (⟦a ⇒' b ⇒' c⟧ → ⟦τ'⟧)`

`   = ExpT τ × (⟦a ⇒' b ⇒' c⟧ → (ExpT τ' × (⟦a ⇒' b⟧ → ⟦τ''⟧)))`

`   = ExpT τ × (⟦a ⇒' b ⇒' c⟧ → (ExpT τ' × (⟦a ⇒' b⟧ → (ExpT τ'' × (⟦a⟧ → ⟦c⟧)))))`

Now for describing each of the components: let `x : ⟦a ⇒' b ⇒' c⟧, y : ⟦a ⇒' b⟧, z : ⟦a⟧`

- `ExpT τ`: This is `S` applied to no arguments, so `S : ExpT τ`

- `ExpT τ'`: This is `S` applied to 1 reified-argument, so `S ⬝ (reify x) : ExpT τ'`

- `ExpT τ''`: This is `S` applied to 2 reified-arguments, so `S ⬝ (reify x) ⬝ (reify y) : ExpT τ''`

- `⟦a⟧ → ⟦c⟧`: This is `S` fully-applied to 3 reified-arguments, so `S ⬝ (reify x) ⬝ (reify y) ⬝ (reify z) : ⟦c⟧`.
  However, since `S` is fully-applied, we may "semantically-unfold" this one-step to get: `appsem (appsem x z) (appsem y z) : ⟦c⟧`

Putting this all together, we get the semantic-evaluation for `S`:

`ExpT_inter S`
`=`

  `(S,`

   `(λ x ↦ (S ⬝ (reify (a⇒'b⇒'c) x),`

   `(λ y ↦ (S ⬝ (reify (a⇒'b⇒'c) x) ⬝ (reify (a⇒'b) y),`

   `(λ z ↦ appsem (appsem x z) (appsem y z)))))))`

Through this, we can see that our evaluation of GodelT expressions is to keep applying them to reified-arguments
until we can reduce it at the Meta-level.

Repeating this for our other constructors finally gives us Term-evaluation:
```lean
def ExpT_inter (a : Ty) : (e : ExpT a) → Ty_inter a
| @ExpT.K a b => (.K,
            (λ p ↦ (.K ⬝ (reifyT a p),
            (λ q ↦ p))))

| @ExpT.S a b c => (.S,
              (λ x ↦ (.S ⬝ (reifyT (a⇒'b⇒'c) x),
              (λ y ↦ (.S ⬝ (reifyT (a⇒'b⇒'c) x) ⬝ (reifyT (a⇒'b) y),
              (λ z ↦ appsem (appsem x z) (appsem y z)))))))
| @ExpT.App a b f e  => appsem (ExpT_inter (a ⇒' b) f) (ExpT_inter a e)

| ExpT.zero          => (0 : Nat)

| ExpT.succ          => (.succ,
                   (λ n : Nat ↦ n+1) )
| @ExpT.recN a       => (.recN,
                   (λ p ↦ (.recN ⬝ (reifyT a p),
                   (λ q ↦ (.recN ⬝ (reifyT a p) ⬝ (reifyT (.Nat⇒'a⇒'a) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))
```

As before with Monoid-Rewriting, we have that rewritable-terms give us equal evaluations:
```lean
theorem convrT_eval_eq {a : Ty} {e e' : ExpT a} : e ~ e' → ((ExpT_inter a e) = (ExpT_inter a e')) :=
  by
  -- Hint: Induction on convrT
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=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)
[Solution](https://live.lean-lang.org/#codez=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)


## Nbe
We now define NbE as before, we first evaluate the Term to the Meta-level before reifying the
normalized term back down to the Object-level:

```lean
def nbeT (a : Ty) (e : ExpT a) : (ExpT a) := reifyT a (ExpT_inter a e)
```

Note that from `convrT_eval_eq` we immediately get soundness for our NbE algorithm:

```lean
theorem soundness {e e' : ExpT α} : e ~ e' → nbeT α e = nbeT α e' :=
  by
  -- Hint: Immediate from convrT_eval_eq
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=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)
[Solution](https://live.lean-lang.org/#codez=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)

## Correctness
We again want to show correctness for our `nbeT` algorithm, that is:

`e ~ e' ↔ nbeT e = nbeT e'`

While Soundness follows just like the Monoid-rewriting case (utilizing `convr_eval_eq`), Completeness (and more specifically `convr_nbe`)
requires more to push-through.
To show

`e ~ nbeT e`

we will utilize the method of Reducibility-candidates that we discussed earlier:
```lean
-- Tait-reducibility relation
def R : (a : Ty) → (e : ExpT a) → Prop
| Ty.Nat, e       => e ~ (nbeT Ty.Nat e)

| Ty.arrow α β, e => e ~ (nbeT (α ⇒' β) e)  ∧  ∀ e', R α e' → R β (e ⬝ e')
```
Note that from this definition of Reducibility we get 3 trivial lemmas:
```lean
-- R a e  implies  e ~ nbeT a e
theorem R_convr_nbe (h : R α e)  : e ~ (nbeT α e) :=
  by
  -- Hint: By cases on α
  --  and def of R
  sorry

-- e ~ e' implies  R α e ↔ R α e'
theorem convr_R_iff : ∀ e e' : ExpT α, e ~ e' → (R α e ↔ R α e') :=
  by
  -- Hint: Induction on α
  --  and soundness
  sorry

theorem R_numeral : R Ty.Nat (numeral n) :=
  by
  -- Hint: Induction on n
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=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)
[Solution](https://live.lean-lang.org/#codez=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)

With these results in place, we are now ready to prove our main lemma, that all Godel-T terms are reducible:

`∀ e : ExpT α, R α e`

Since this is such an intergral lemma to our correctness proof, we will walk through this proof for the case where `e = recN`
(since all other cases are similar to this one).

```lean
example (α : Ty) :  R (α ⇒' (Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) .recN :=
by
-- By def of `R` we must prove two things:
apply And.intro

-- `recN ~ (nbeT (α ⇒' (Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) recN):`
-- Since `nbeT recN = recN`, this follows by `convrT.refl`.
· exact convrT.refl

-- `∀ e', R α e' → R ((Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) (recN ⬝ e'):`
-- Suppose we have `R α e'`, by def of `R` we must prove two things:
· intro e' Re'
  apply And.intro

  -- `recN ⬝ e' ~ nbeT ((Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) (recN ⬝ e'):`
  -- Since `nbeT (recN ⬝ e') = recN ⬝ (nbeT e')`, this follows by `R α e'`.
  · have eq : nbeT ((Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) (.recN ⬝ e') = .recN ⬝ nbeT α e' := rfl; rewrite [eq]; clear eq
    apply convrT.app convrT.refl
    exact R_convr_nbe Re'

  -- `∀ e'', R (Ty.Nat ⇒' α ⇒' α) e'' → R (Ty.Nat ⇒' α) (recN ⬝ e' ⬝ e''):`
  -- Suppose we have `R (Ty.Nat ⇒' α ⇒' α) e''`, by def of `R` we must prove two things:
  · intro e'' Re''
    apply And.intro

    --`(recN ⬝ e' ⬝ e'') ~ nbeT (Ty.Nat ⇒' α) (recN ⬝ e' ⬝ e''):`
    -- Since `nbeT (recN ⬝ e' ⬝ e'') = recN ⬝ (nbeT e') ⬝ (nbeT e'')`, this follows by `R α e'` and `R (Ty.Nat ⇒' α ⇒' α) e''`.
    · have eq : nbeT (Ty.Nat ⇒' α) (.recN ⬝ e' ⬝ e'') = .recN ⬝ nbeT α e' ⬝ nbeT (Ty.Nat ⇒' α ⇒' α) e'' := rfl; rewrite [eq]; clear eq
      replace Re' := R_convr_nbe Re'; replace Re'' := R_convr_nbe Re''
      have h0 : convrT (.recN ⬝ e') (.recN ⬝ nbeT α e') := (convrT.refl).app Re'
      exact h0.app Re''

    -- `∀ n, R (Ty.Nat) n → R α (recN ⬝ e' ⬝ e'' ⬝ n):`
    -- Suppose we have `R (Ty.Nat) n`, by def of `R` we have `n ~ nbeT n` so by `convr_R_iff` suffices to show:
    --      `R α (recN ⬝ e' ⬝ e'' ⬝ (nbeT n)):`
    -- Since `nbeT n = numeral [[n]]`, we may perform induction on `[[n]] : ℕ`:
    · intro n Rn
      have convr_n := Rn
      unfold R at convr_n
      apply (convr_R_iff (.recN ⬝ e' ⬝ e'' ⬝ n) (.recN ⬝ e' ⬝ e'' ⬝ (nbeT Ty.Nat n)) (convrT.refl.app Rn)).mpr
      unfold nbeT; simp [reifyT]
      induction ((ExpT_inter Ty.Nat n))

      -- `R α (recN ⬝ e' ⬝ e'' ⬝ (numeral 0)):`
      -- By `convr_R_iff` and `R α e'` we are done.
      · unfold numeral
        exact (convr_R_iff (.recN ⬝ e' ⬝ e'' ⬝ .zero) e' convrT.recN_zero).mpr Re'

      -- `R α (recN ⬝ e' ⬝ e'' ⬝ (numeral (n'+1))):` By def of `numeral` and `convr_R_iff`, suffices to show:
      --     ` R α (e'' ⬝ numeral n' ⬝ (recN ⬝ e' ⬝ e'' ⬝ numeral n')):`
      -- By `R (Ty.Nat ⇒' α ⇒' α) e''`, `R_numeral`, and `IH` we are done.
      · rename_i n' IH
        apply (convr_R_iff (.recN ⬝ e' ⬝ e'' ⬝ (.succ ⬝ numeral n')) (e'' ⬝ (numeral n') ⬝ (.recN ⬝ e' ⬝ e'' ⬝ (numeral n'))) convrT.recN_succ).mpr
        have R_numeral_n' : R Ty.Nat (numeral n') := by exact R_numeral
        rcases Re'' with ⟨_, h0⟩
        specialize h0 (numeral n') R_numeral_n'
        rcases h0 with ⟨_, h0⟩
        exact h0 (.recN ⬝ e' ⬝ e'' ⬝ numeral n') IH
```
[Example on Lean4 web server](https://live.lean-lang.org/#codez=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)

With similar reasoning for the other cases, we get our Reducibility proof:

```lean
-- for all e, R a e
theorem all_R {e : ExpT α} : R α e :=
  by
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=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)
[Solution](https://live.lean-lang.org/#codez=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)

With our main lemma out of the way, we immediately get `e ~ (nbeT α e)` and `completeness`:

```lean
-- e ~ nbeT α e
theorem convrT_nbe {e : ExpT α} : e ~ (nbeT α e) :=
  by
  -- Hint: Use `all_R` and `R_convr_nbe`
  sorry

-- nbeT α e = nbeT α e' implies e ~ e'
theorem completeness {e e' : ExpT α} : nbeT α e = nbeT α e' → e ~ e' :=
  by
  -- Hint: Use convrT_nbe
  -- just like in Monoid-rewriting case.
  sorry
```
[Try it!](https://live.lean-lang.org/#codez=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)
[Solution](https://live.lean-lang.org/#codez=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)


Finally, we have our main correctness theorem:
```lean
-- e ~ e' ↔ nbeT a e = nbeT a e'
theorem correctnessT {e e' : ExpT a} : e ~ e' ↔ nbeT a e = nbeT a e' := ⟨soundness, completeness⟩
```
Like last time, Lean can now instantly decide any `a ~ b` problem through reflexivity:
```lean
-- I ⬝ x ~ x
example {x : ExpT α}
        : ((@I α β) ⬝ x)  ~  x := correctnessT.mpr rfl

-- (B ⬝ x ⬝ y ⬝ z)  ~  (x ⬝ (y ⬝ z))
example {x : ExpT (b ⇒' c)}
        {y : ExpT (a ⇒' b)}
        {z : ExpT a}
        : (B ⬝ x ⬝ y ⬝ z)  ~  (x ⬝ (y ⬝ z)) := correctnessT.mpr rfl

-- m + 0 ~ m
example : (add m ⬝ .zero)  ~  m := correctnessT.mpr rfl

-- m + (succ n) ~ succ (m + n)
example : (add m ⬝ (.succ ⬝ n))  ~  (.succ ⬝ (add m ⬝ n)) := correctnessT.mpr rfl

-- m * 0 ~ 0
example : (mult m ⬝ .zero) ~ .zero := correctnessT.mpr rfl

-- m * (succ n) ~ m + (m * n)
example : (mult m ⬝ (.succ ⬝ n)) ~ ((add m) ⬝ (mult m ⬝ n)) := correctnessT.mpr rfl

-- m ^ 0 ~ 1
example : (power m ⬝ .zero) ~ (.succ ⬝ .zero) := correctnessT.mpr rfl

-- m ^ (succ n) ~ m * (m ^ n)
example : (power m ⬝ (.succ ⬝ n)) ~ ((mult m) ⬝ (power m ⬝ n)) := correctnessT.mpr rfl

-- m ^ 3 ~ m * (m * m)
example : (power m ⬝ (.succ ⬝ (.succ ⬝  (.succ ⬝ .zero))))  ~  (mult m ⬝ (mult m ⬝ m)) := correctnessT.mpr rfl
```



{index}[index]

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
