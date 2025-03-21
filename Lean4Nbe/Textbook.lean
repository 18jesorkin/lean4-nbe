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

Now that we can evaluate out Monoid-expressions such that they're normalized at the Meta-level, how do we bring them back down to the object-level such that we don't change the "behavior" (wrt `~`)?
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

```lean
theorem correctness (e e' : Exp α) : (e ~ e') ↔ (nbe e = nbe e') :=
    by sorry
```
[Try it!](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYVhZyoBAsjNkDGgucAmAwA1EC7iEa4EmQpzQChwJQA4xA05inIhsxhTZ4PIYwoAKYQxKX+IzHAm8r0dcmqbk9VwAAkp4nhCO9DCgQA7bcH1227Z3/MIl2P9KakaVp6A6UGpnmX5R2IRwDyyiLee62QBTUUbI9aiDknIvj8g7AK4IQphSgQKGBGCNBINCjQAAEvpFgABVJ2XolpWHorgrEk95K3zgN9V4f0d5l0TnXN6D8lB+SwoQ96JCnaC0eHURaAMqrQCgFoIAA)
[Solution](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0AVJAYxmEICgyBaSuAMSghAC45UYYwBnJgeh8M45gEQjgCmYnmIDunATwBMABiUBOHgBMAnlgBWYqDxBJgAOwAKSdCE5jKUMQDdgtjTjAaAZhTMaArsTAjmJwAKIAHmBwABSAjcBwLHhaYGIAlGQAPnBIYFEsEVHxgEmEYZFwxaWFmXDAGnAJleXVYuhiIA0VBU1mnsDhDQCMKnAARHCAuNSjcAC8AHyVODlgFFQ0ACK1pgDk8BpihOhIDnBoIQDKYjAQtTWmnDBIpoQhntAnqC5wWpdkvgEkwTghAgpkcUAa0S6sVScBKkLK0NhcHMDGWWSQnE4IjgAG8QmItnACYT8giAL4NYGg8HRaIhSYEmEMrZbGF0iYxAkc4mpdJZWoAfVanngePqpMKFPq4qBILBMXhYCEGiZRLZaWqgqgwAA5mxcSEJeUpdKWFT5ezJgVleq+XAHJ50NL6mKjbETTLzTS0py7ZwtO1nQaiSTGu7PXLverWUivZyY3S7TAoI9OMGucSGlCKWbI774zCSnG6QmebG84n46zqktcUg4FggXA6m6PbnqTEkGysIXZR3ooQ2Sry/365NBzFG5MVb9TL1+iwhkopgA/KZzPtglZ7TxExxWCFQ3uK8pIo9kepZa21+uNjfRQDdwESZvMnAf63T907G2l0peFjcQYbrUF5wFekTiK07T9C+MRPiE97Wi0bRwOEqoahQ1DZHAa6Nkib5OvW0x7geWBkFBxiblAAoETRACOdYNlm5IxKgDT1rhMIsIAAERAgANJyX7ZDChD1MRn6kSJCTTGQWBaKBfyBCCrCgY8WgCjqEBWJwoH1GYyYQJwADc2RiFiyygYQGIhDeTGiXUApwI5SBYAKwBsYQGhuWxcy6UCrRHHAABUcA0C53lAl57l+fpDBEn5nApIQwBWMAABeISeRFYgJUlKWYBl2Sue5CoEc2MIas6nCgFEILoFocAANoEQAun5UDSE1WXuW1zodU14U9ZhNC8VgAljkxa4SYRDbpBR9ZLDRQnRPWbpcXAo0CStHI9jhgnvrN0myfJemmP4SmmNklnWdkuRNnUhARVFPmzDFpgGQ2fl+HOEDoHUBG5fs+XpSEz2fVVeWpYVj0ldNzazX5qBIICqDLiwtKidOqq7VNmMxHUkw9lxxFeosmIiO1Yi9KYIQDpGODJqmrDLgA/AKf7SgcYiBajiPIyEqMQnj0QE7NMK4xycN1ET0lUYsd109SOAOugQ7eRz9QOmYtOk4zdzM3AbMa/53PgrzzpiOERDwDDqAUPUVm2DUdS+c6sUQOD0qW9bcuCsKMD20CN3Ie0rvSu7nv1N7xByyrFA7vaYjAJ4DXRLubpngi60noiTDEbu1ogWQCemFgtOGmG61QrLDjJ6nZUYVhZyoBAsjNkDGgucAmAwA1EC7iEa4EmQpzQChwJQA4xA05inIhsxhTZ4PIYwoAKYQxKX+IzHAm8r0dcmqbk9VwAAkp4nhCO9DCgQA7bcH1227Z3/MIl2P9KakaVp6A6UGpnmX5R2IRwDyyiLee62QBTUUbI9aiDknIvj8g7AK4IQphSgQKGBGCNBINYPzbIsDMEtk7ByCcU0pzlVlqTG8GCsFwNwdHG2kYlpWHogQ2hdRC44NvnAb6rw/o7zLonOub0H5KD5ijAYDRl6WgAsOPOMRSb+naKTLUuo2DGy1jTRR9M9ZplQFIo2gCUGsAGBIgWUj0b0jkeLUqQkfRcOJrdMALCnQhC4ZTamOtdEpn1gYw27NjGm1MZTaQ2oYAhEaqjXqnMTHm2lEjFGaM7EHkZDYvaJYOSOKofTZRnZciuPno4zx2sdFKz0QbIxzouY83ERbK2MdVFeW1HqGAQA)

With `correctness` in place, Lean can now instantly decide any `a ~ b` problem through reflexivity, i.e.:

```lean
-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example1'
        : (one.app two).app  ((zero.app zero).app three)
        ~ (one.app (two.app (three.app zero))) :=
  by
  /- Try this:
    exact (correctness ((one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three)) (one ⬝ (two ⬝ (three ⬝ zero)))).mpr rfl
  -/
  exact?

-- (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0)) ~ 1 ⬝ (2 ⬝ (3 ⬝ 0))
theorem example2'
  : (zero.app (one.app zero)).app ((zero.app two).app (three.app zero))
  ~ (one.app (two.app (three.app zero))) :=
  by
  /- Try this:
    exact (correctness ((zero ⬝ (one ⬝ zero)) ⬝ ((zero ⬝ two) ⬝ (three ⬝ zero)))
      (one ⬝ (two ⬝ (three ⬝ zero)))).mpr rfl
  -/
  exact?

-- (1 ⬝ 2) ⬝ ((0 ⬝ 0) ⬝ 3) ~ (0 ⬝ (1 ⬝ 0)) ⬝ ((0 ⬝  2) ⬝ (3 ⬝ 0))
theorem example3'
  : (one.app two).app  ((zero.app zero).app three)
  ~ (zero.app (one.app zero)).app ((zero.app two).app (three.app zero)) :=
  by
  /- Try this:
    exact (correctness ((one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three))
      ((zero ⬝ (one ⬝ zero)) ⬝ ((zero ⬝ two) ⬝ (three ⬝ zero)))).mpr rfl
  -/
  exact?
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
-- TO-DO: Fix Verso so it lets me define this constructor!!
--| recN_succ : convrT (recN ⬝ e ⬝ f ⬝ (.succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))
infix : 100 " ~ " => convrT
```
Some rewriting examples are:

```lean
-- Identity Combinator
def I {β : Ty} : ExpT (α ⇒' α) := (@ExpT.S α (β ⇒' α) α) ⬝ .K ⬝ .K

example {x : ExpT α}
        : ((@I α β) ⬝ x)  ~  x :=
  by
  /-
  apply convrT.trans convrT.S ?_
  apply convrT.trans convrT.K ?_
  exact convrT.refl
  -/
  -- TO-DO: Try-it! Here
  sorry
```

```lean
-- B Combinator
def B {a b c : Ty} : ExpT ((b ⇒' c) ⇒' (a ⇒' b) ⇒' a ⇒' c) := .S ⬝ (.K ⬝ .S) ⬝ .K


example {x : ExpT (b ⇒' c)}
        {y : ExpT (a ⇒' b)}
        {z : ExpT a}
        : (B ⬝ x ⬝ y ⬝ z)  ~  (x ⬝ (y ⬝ z)) :=
  by
  /-
  unfold B
  apply convrT.trans ?_ ?_
  exact (.K ⬝ .S) ⬝ x ⬝ (.K ⬝ x) ⬝ y ⬝ z
  · apply convrT.app ?_ convrT.refl
    apply convrT.app ?_ convrT.refl
    exact convrT.S
  · apply convrT.trans ?_ ?_
    exact .S ⬝ (.K ⬝ x) ⬝ y ⬝ z
    · apply convrT.app ?_ convrT.refl
      apply convrT.app ?_ convrT.refl
      apply convrT.app ?_ convrT.refl
      exact convrT.K
    · apply convrT.trans ?_ ?_
      exact (.K ⬝ x ⬝ z) ⬝ (y ⬝ z)
      · exact convrT.S
      · apply convrT.app ?_ convrT.refl
        exact convrT.K
  -/
  -- TO-DO: Try-it! here
  sorry
```

```lean
def add (m n : ExpT .Nat) := .recN ⬝ m ⬝ (.K ⬝ .succ) ⬝ n

example : (add m .zero)  ~  m :=
  by
  /-
  exact convrT.recN_zero
  -/
  -- TO-DO: "Try-it!" here
  sorry

example : (add m (.succ ⬝ n))  ~  (.succ ⬝ (add m n)) :=
  by
  /-
  unfold add
  apply convrT.trans ?_ ?_
  exact (.K ⬝ .succ) ⬝ n ⬝ (.recN ⬝ m ⬝ (.K ⬝ .succ) ⬝ n)
  · sorry --exact convrT.recN_succ
  · apply convrT.app ?_ convrT.refl
    exact convrT.K
  -/
  -- TO-DO: "Try-it!" here
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
def reifyT (a : Ty) (e : Ty_inter a) : ExpT a :=
/-
| Ty.Nat, (0 : ℕ) => zero
| Ty.Nat, n+1     => succ ⬝ (reify Ty.Nat n)

| Ty.arrow a b, (f, F) => f
-/
by
  cases a
  case Nat =>
    induction e
    case zero           => exact .zero
    case succ n reify_n => exact (.succ ⬝ reify_n)
  case arrow a b        => exact e.fst
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

We illustrate this with the exampe ` S :  ExpT ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))`.

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

| _ => sorry

-- TO-DO: Fix Verso so I can implement the rest of this Definition!!
/-
| ExpT.zero          => (0 : Nat)

| ExpT.succ          => (.succ,
                   (λ n : Nat ↦ n+1) )
| @ExpT.recN a       => (.recN,
                   (λ p ↦ (.recN ⬝ (reifyT a p),
                   (λ q ↦ (.recN ⬝ (reifyT a p) ⬝ (reifyT (.Nat⇒'a⇒'a) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))
-/
```



{index}[index]

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
