import Mathlib.Tactic

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf


-- Monoid-expressions with atoms in a set α
-- (slide 25)
inductive Exp (α : Type)
-- e₀ ⬝ e₁  : Exp α
| app : Exp α → Exp α → Exp α
-- id : Exp α
| id  : Exp α
-- (x : α) : Exp α
| elem : α → Exp α
infix : 100 " ⬝ " => Exp.app

-- Congruence-relation that identifies when
-- 2 Monoid-expressions are "convertible" (slide 26):
inductive convr : (Exp α) → (Exp α) → Prop
-- assoc                   :  ((e ⬝ e') ⬝ e'') ~ (e ⬝ (e' ⬝ e''))
| assoc {e e' e'' : Exp α} : convr ((e ⬝ e') ⬝ e'') (e ⬝ (e' ⬝ e''))
-- id_left                 :   (id ⬝ e) ~ e
| id_left {e  : Exp α}     : convr ((Exp.id) ⬝ e) (e)
-- id_right                :   (e ⬝ id) ~ e
| id_right {e : Exp α}     : convr (e ⬝ Exp.id) (e)
-- refl                    : e ~ e
| refl     {e : Exp α}     : convr (e) (e)
-- sym                     : e ~ e'         →   e' ~ e
| sym      {e e' : Exp α}  : convr (e) (e') → convr (e') (e)
-- trans                   : e ~ e'         → e' ~ e''         → e ~ e''
| trans {e e' e'' : Exp α} : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
-- app                     : a ~ b         → c ~ d         →  (a ⬝ c) ~ (b ⬝ d)
| app {a b c d : Exp α}    : convr (a) (b) → convr (c) (d) → convr (a ⬝ c) (b ⬝ d)
infix : 100 " ~ " => convr

-- Evaluate Monoid-expressions as functions (slide 32):
def eval : (Exp α) → (Exp α → Exp α)
  -- ⟦a ⬝ b⟧    =   λ e ↦ ⟦a⟧ (⟦b⟧ e)
  | Exp.app a b => (λ e => eval a (eval b e))
  -- ⟦id⟧       =   λ e ↦ e
  | Exp.id      => id
  -- ⟦x : α⟧    =   λ e ↦ x ⬝ e
  | Exp.elem x  => (λ e => (Exp.elem x) ⬝ e)


-- a ~ b  → eval a = eval b
lemma convr_eval_eq {a b : Exp α} (h : a ~ b) : ∀ c, (eval a) c  = (eval b) c :=
by
  induction h
  any_goals
    intros; aesop

  case app a b c d _ _ ab_ih cd_ih =>
    clear * - ab_ih cd_ih
    intro e
    specialize cd_ih e
    specialize ab_ih ((eval d) e)
    simp only [eval]
    rw [cd_ih]
    rw [ab_ih]

-- ∀ b, a ⬝ b ~ (eval a b)
lemma app_eval (a : Exp α) : ∀ b, (a ⬝ b) ~ (eval a b) :=
by
  induction a
  case app c d c_ih d_ih =>
    intro b
    unfold eval
    specialize d_ih b
    specialize c_ih (eval d b)
    have h0 : ((c ⬝ d) ⬝ b) ~ (c ⬝ (d ⬝ b)) := convr.assoc
    refine (convr.trans h0 ?_)
    clear h0
    have h0 : (c ⬝ (d ⬝ b)) ~ (c ⬝ (eval d b)) := convr.app (convr.refl) (d_ih)
    refine (convr.trans h0 ?_)
    clear h0
    exact c_ih

  case id =>
    intro b
    exact convr.id_left

  case elem =>
    intro b
    exact convr.refl

-- Reify functions back into Monoid-expressions (slide 32):
def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id

-- nbe e := reify ⟦e⟧ (slide 33):
def nbe (e : Exp α) : Exp α := reify (eval e)

-- Shows decidability of e ~ e'
theorem correctness (e e' : Exp α) : (e ~ e') ↔ (nbe e = nbe e') :=
by
  apply Iff.intro
  · intro h
    induction h
    any_goals
      aesop
    case mp.app a b c d a_r_b c_r_d _ _ =>
      clear * - a_r_b c_r_d
      have ac_r_bd : (a ⬝ c) ~ (b ⬝ d) := convr.app a_r_b c_r_d
      exact convr_eval_eq ac_r_bd Exp.id

  · unfold nbe reify
    intro h0
    have h1 : e ~ (e ⬝ Exp.id) := (convr.sym convr.id_right)
    refine (convr.trans h1 ?_)
    clear h1
    have h1 : (e ⬝ Exp.id) ~ ((eval e) Exp.id) := app_eval e Exp.id
    refine (convr.trans h1 ?_)
    clear h1
    rewrite [h0]
    clear h0
    have h0 : ((eval e') Exp.id) ~ (e' ⬝ Exp.id) := convr.sym (app_eval e' Exp.id)
    refine (convr.trans h0 ?_)
    clear h0
    exact convr.id_right

-- Python code to quickly generate examples:
/-
import random

def generate_tree(L):
    # base case
    if len(L) == 1:
        return L[0]
    split = random.randint(1, len(L)-1)
    left = L[:split]
    right = L[split:]
    # recursion
    return (generate_tree(left), generate_tree(right))


for i in range(2):
  rep0 = [0] * random.randint(0,2)
  rep1 = [0] * random.randint(0,2)
  rep2 = [0] * random.randint(0,2)
  rep3 = [0] * random.randint(0,2)
  list = rep0 + [1] + rep1 + [2] + rep2 + [3] + rep3
  print(generate_tree(list))
-/

def zero := (Exp.id : Exp ℕ)
def one  := Exp.elem 1
def two  := Exp.elem 2
def three := Exp.elem 3

-- ((1, 2), ((0, 0), 3)) ~ ((0, 0), (1, (2, (0, 3))))
#reduce nbe ( (one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three) )
#reduce nbe ( (zero ⬝ zero) ⬝ (one ⬝ (two ⬝ (zero ⬝ three))))
example : ( (one ⬝ two) ⬝  ((zero ⬝ zero) ⬝ three) )
        ~ ( (zero ⬝ zero) ⬝ (one ⬝ (two ⬝ (zero ⬝ three)))) :=
  by
  have h0 : (zero ⬝ zero) ~ zero := convr.id_left
  have h1 : ((zero ⬝ zero) ⬝ three) ~ (zero ⬝ three) := convr.app h0 convr.refl
-- ((1, 2), ((0, 0), 3)) ~ ((1, 2), (0, 3))
  have h2 : ((one ⬝ two) ⬝ ((zero ⬝ zero) ⬝ three))
          ~ ((one ⬝ two) ⬝ (zero ⬝ three)) := convr.app convr.refl h1
-- ((1, 2), (0, 3)) ~ (1, (2, (0, 3))
  have h3 : ((one ⬝ two) ⬝ (zero ⬝ three))
          ~ (one ⬝ (two ⬝ (zero ⬝ three))) := convr.assoc
  have h4 : zero ~ (zero ⬝ zero) := convr.sym h0
-- (1, (2, (0, 3)) ~ (0, (1, (2, (0, 3)))
  have h5 : (one ⬝ (two ⬝ (zero ⬝ three)))
          ~ (zero ⬝ (one ⬝ (two ⬝ (zero ⬝ three)))) := convr.sym convr.id_left
-- (0, (1, (2, (0, 3))) ~ ((0, 0), (1, (2, (0, 3)))
  have h6 : (zero ⬝ (one ⬝ (two ⬝ (zero ⬝ three))))
          ~ ((zero ⬝ zero) ⬝ (one ⬝ (two ⬝ (zero ⬝ three)))) := convr.app h4 convr.refl
  clear h0 h1 h4
  apply convr.trans h2
  apply convr.trans h3
  apply convr.trans h5
  apply convr.trans h6
  exact convr.refl
