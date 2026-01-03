import Mathlib.Tactic

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Ty : Type
| nat   : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow

inductive Exp : Ty → Type
| var (α)          : Nat → Exp α
| K {α β : Ty}     : Exp (α ⇒' β ⇒' α)
| S {α β γ : Ty}   : Exp ((α ⇒' β ⇒' γ) ⇒' (α ⇒' β) ⇒' (α ⇒' γ))
| app {α β : Ty}   : Exp (α ⇒' β) → Exp α → Exp β
open Exp
infixl : 100 " ⬝ " => app

def neutral (e : Exp α) : Bool :=
  match e with
  | var (α) n => true
  | K       => false
  | S       => false
  | app f t₂ =>
    match f with
    | var (α) n => true
    | K       => false
    | S       => false
    | app f' t₁ =>
      match f' with
      | var (α) n => true
      | K       => true
      | S       => false
      | app f'' t₀ => true


lemma neutral_func {f : Exp (α ⇒' β)} : neutral f → neutral (f ⬝ x) :=
  by
  suffices neutral (f ⬝ x) = false → neutral f = false
    by
    aesop
  intro not_neutral_fx
  unfold neutral at not_neutral_fx
  simp at not_neutral_fx
  cases f
  all_goals
    aesop


inductive R : {α : Ty} → (Exp α) → (Exp α) → Prop
| K     {α β : Ty}{x : Exp α} {y : Exp β}
        : R (K ⬝ x ⬝ y) (x)
| S     {α β γ: Ty}{x : Exp (γ ⇒' β ⇒' α)} {y : Exp (γ ⇒' β)} {z : Exp γ}
        : R (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app_f   {α β : Ty} {f f' : Exp (β ⇒' α)} {x : Exp β}
        : R (f) (f') → R (f ⬝ x) (f' ⬝ x)
| app_x   {α β : Ty} {f : Exp (β ⇒' α)} {x x' : Exp β}
        : R (x) (x') → R (f ⬝ x) (f ⬝ x')
infixr : 100 " →β " => R


inductive SN : Exp α → Prop
| mk : (∀y : Exp α, R x y → SN y) → SN x

lemma SN_R : (x →β y) → SN x → SN y :=
  by
  intro x_R_y SN_x
  rcases SN_x with ⟨SN_x⟩
  exact SN_x y x_R_y

lemma SN_K : SN (@K α β) :=
  by
  constructor
  intro K' K_R_K'
  cases K_R_K'

lemma SN_Kx {x : Exp α }
  : SN (x) → SN ((@K α β) ⬝ x) :=
  by
  intro SN_x
  induction SN_x
  clear x; rename_i x SN_x x_IH
  constructor
  intro Kx' Kx_R_Kx'
  cases Kx_R_Kx'
  · rename_i K' K_R_K'
    cases K_R_K'
  · rename_i x' x_R_x'
    exact x_IH x' x_R_x'

lemma SN_S : (SN (@S α β γ)) :=
  by
  constructor
  intro S' S_R_S'
  cases S_R_S'

lemma SN_Sx {x : Exp (α ⇒' β ⇒' γ)}
  : SN (x) → SN (S ⬝ x) :=
  by
  intro SN_x
  induction SN_x
  clear x; rename_i x SN_x x_IH
  constructor
  intro Sx' Sx_R_Sx'
  cases Sx_R_Sx'
  · rename_i S' S_R_S'
    cases S_R_S'
  · rename_i x' x_R_x'
    exact x_IH x' x_R_x'

lemma SN_Sxy {x : Exp (α ⇒' β ⇒' γ)} {y : Exp (α ⇒' β)}
  : SN (x) → SN (y) → SN (S ⬝ x ⬝ y) :=
  by
  intro SN_x
  revert y
  induction SN_x
  clear x ; rename_i x SN_x x_IH ; replace SN_x := SN.mk SN_x
  replace x_IH := fun x' x_R_x' z SN_z => @x_IH x' x_R_x' z SN_z
  intro y SN_y
  revert x_IH
  induction SN_y
  clear y ; rename_i y SN_y y_IH ; replace SN_y := SN.mk SN_y
  replace y_IH := fun y' => y_IH y'
  intro x_IH
  constructor
  intro e Sxy_R_e
  cases Sxy_R_e
  · rename_i Sx' Sx_R_Sx'
    cases Sx_R_Sx'
    · rename_i S' S_R_S'
      cases S_R_S'
    · rename_i x' x_R_x'
      aesop
  · rename_i y' y_R_y'
    aesop


def Red (e : Exp α) : Prop :=
  match α,e with
  | nat,       n => SN n
  | arrow α β, f => SN f ∧ ∀ x, Red x → Red (f ⬝ x)

lemma Red_SN (x : Exp α) : (Red x) → SN x :=
  by
  cases α
  all_goals
    unfold Red
    aesop

lemma Red_R (x y : Exp α) : (x →β y) → Red x → Red y :=
  by
  revert y x
  induction α
  · unfold Red
    apply SN_R
  · rename_i α β α_IH β_IH
    intro f f' f_R_f' Red_f
    apply And.intro
    · have SN_f :=  Red_SN f Red_f
      exact SN_R f_R_f' SN_f
    · intro x Red_x
      rcases Red_f with ⟨left, Red_f⟩ ; clear left
      specialize β_IH (f ⬝ x) (f' ⬝ x) (R.app_f f_R_f') (Red_f x Red_x)
      assumption

lemma Red_invR (x : Exp α) (neutral_x : neutral x = true) : (∀ y, (x →β y) → Red y) → Red x :=
  by
  revert x
  induction α
    --by def of SN
  · unfold Red
    exact fun x neutral_x a ↦ SN.mk a
  · rename_i α β α_IH β_IH
    intro f f_neutral f_h
    apply And.intro
      --by def of SN
    · constructor
      exact fun y a ↦ Red_SN y (f_h y a)
    · intro x Red_x
      have SN_x := Red_SN x Red_x
      induction SN_x
      clear x ; rename_i x SN_x x_IH
      apply β_IH
      exact neutral_func f_neutral
      intro e fx_R_e
      cases fx_R_e
      · cases f_neutral
      · cases f_neutral
      · rename_i f' f_R_f'
        specialize f_h f' f_R_f'
        rcases f_h with ⟨left, Red_f'⟩ ; clear left
        exact Red_f' x Red_x
      · rename_i x' x_R_x'
        apply x_IH
        · exact x_R_x'
        · exact Red_R x x' x_R_x' Red_x

lemma Red_x : Red (var α n) :=
  by
  apply Red_invR
  · rfl
  · intro e vₙ_R_e
    cases vₙ_R_e

lemma Red_Kxy {x : Exp α} {y : Exp β}
  : Red x → Red y → Red (K ⬝ x ⬝ y) :=
  by
  intro Red_x Red_y
  revert Red_y y
  have SN_x := Red_SN x Red_x ; revert Red_x
  induction SN_x
  clear x; rename_i x SN_x x_IH ; clear SN_x
  replace x_IH := fun x' x_R_x' Red_x' y₁ Red_y₁  => @x_IH x' x_R_x' Red_x' y₁ Red_y₁

  intro Red_x y Red_y
  revert x_IH ; revert Red_x x
  have SN_y := Red_SN y Red_y ; revert Red_y
  induction SN_y
  clear y; rename_i y SN_y y_IH; clear SN_y

  intro Red_y x Red_x x_IH
  apply Red_invR (K ⬝ x ⬝ y) rfl
  intro Kxy' Kxy_R_Kxy'
  cases Kxy_R_Kxy'
  · exact Red_x

  · rename_i Kx' Kx_R_Kx'
    cases Kx_R_Kx'
    · rename_i K' K_R_K'
      cases K_R_K'
    · rename_i x' x_R_x'
      apply x_IH
      · exact x_R_x'
      · exact Red_R x x' x_R_x' Red_x
      · exact Red_y

  · rename_i y' y_R_y'
    apply y_IH
    · exact y_R_y'
    · exact Red_R y y' y_R_y' Red_y
    · exact Red_x
    · exact x_IH

lemma Red_Sxyz {x : Exp (α ⇒' β ⇒' γ)} {y : Exp (α ⇒' β)} {z : Exp α}
  : Red (x) → Red (y) → Red (z) → Red (S ⬝ x ⬝ y ⬝ z) :=
  by
  intro Red_x Red_y Red_z
  revert Red_z z ; revert Red_y y
  have SN_x : SN x := Red_SN x Red_x ; revert Red_x
  induction SN_x
  clear x ; rename_i x SN_x x_IH ; clear SN_x
  replace x_IH := fun x' x_R_x' Red_x' y₁ Red_y₁ z₁ Red_z₁ => @x_IH x' x_R_x' Red_x' y₁ Red_y₁ z₁ Red_z₁

  intro Red_x y Red_y
  revert x_IH ; revert Red_x x
  have SN_y : SN y := Red_SN y Red_y ; revert Red_y
  induction SN_y
  clear y ; rename_i y SN_y y_IH ; clear SN_y
  replace y_IH := fun y' y_R_y' Red_y' x₁ Red_x₁ x₁_IH z₁ Red_z₁ =>  @y_IH y' y_R_y' Red_y' x₁ Red_x₁ x₁_IH z₁ Red_z₁

  intro Red_y x Red_x x_IH z Red_z
  revert y_IH ; revert Red_y y ; revert x_IH ; revert Red_x x
  have SN_z : SN z := Red_SN z Red_z ; revert Red_z
  induction SN_z
  clear z ; rename_i z SN_z z_IH ; clear SN_z
  replace z_IH := fun z' z_R_z' Red_z' x₁ Red_x₁ x₁_IH y₁ Red_y₁ y₁_IH => @z_IH z' z_R_z' Red_z' x₁ Red_x₁ x₁_IH y₁ Red_y₁ y₁_IH

  intro Red_z x Red_x x_IH y Red_y y_IH
  apply Red_invR (S ⬝ x ⬝ y ⬝ z) rfl
  intro e Sxyz_R_e
  cases Sxyz_R_e
  · clear z_IH y_IH x_IH
    rcases Red_x with ⟨left, Red_x⟩ ; clear left
    rcases Red_y with ⟨left, Red_y⟩ ; clear left
    have Red_xz : Red (x⬝ z) := Red_x z Red_z
    rcases Red_xz with ⟨left, Red_xz⟩ ; clear left
    have Red_yz : Red (y ⬝ z) := Red_y z Red_z
    have Red_xzyz : Red (x ⬝ z ⬝ (y ⬝ z)) := Red_xz (y ⬝ z) Red_yz
    assumption

  · rename_i e Sxy_R_e
    cases Sxy_R_e
    · rename_i Sx' Sx_R_Sx'
      cases Sx_R_Sx'
      · rename_i S' S_R_S'
        cases S_R_S'
      · rename_i x' x_R_x'
        apply x_IH
        · exact x_R_x'
        · exact Red_R x x' x_R_x' Red_x
        · exact Red_y
        · exact Red_z
    · rename_i y' y_R_y'
      apply y_IH
      · exact y_R_y'
      · exact Red_R y y' y_R_y' Red_y
      · exact Red_x
      · apply x_IH
      · exact Red_z

  · rename_i z' z_R_z'
    apply z_IH
    · exact z_R_z'
    · exact Red_R z z' z_R_z' Red_z
    · exact Red_x
    · exact x_IH
    · exact Red_y
    · apply y_IH


lemma all_Red (e : Exp α) : Red e :=
  by
  induction e
  all_goals clear α

  case var α n =>
    exact Red_x

  case K α β =>
    apply And.intro
    · exact SN_K
    · intro x Red_x
      apply And.intro
      · have SN_x := Red_SN x Red_x
        exact SN_Kx SN_x
      · intro y Red_y
        exact Red_Kxy Red_x Red_y

  case S α β γ =>
    apply And.intro
    · exact SN_S
    · intro x Red_x
      apply And.intro
      · have SN_x := Red_SN x Red_x
        exact SN_Sx SN_x
      · intro y Red_y
        apply And.intro
        · have SN_x := Red_SN x Red_x
          have SN_y := Red_SN y Red_y
          exact SN_Sxy SN_x SN_y
        · intro z Red_z
          exact Red_Sxyz Red_x Red_y Red_z

  case app α β f x f_IH x_IH =>
    rcases f_IH with ⟨left, Red_f⟩ ; clear left
    exact Red_f x x_IH



theorem all_SN (e : Exp α) : SN e := Red_SN e (all_Red e)
