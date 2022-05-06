import order.complete_lattice
import order.fixed_points
import data.set.lattice

import syntax

-- Definition 2, page 6
-- TODO: think about whether char is infinite / has to be ...
structure kripkeModel (W : Type) : Type :=
  (val : W → char → Prop)
  (rel : W → W → Prop)

-- Definition 3, page 6
def evaluate {W : Type} : (kripkeModel W × W) → formula → Prop
| (M,w) ⊥     := false
| (M,w) (· c) := M.val w c
| Mw (~ φ)    := not (evaluate Mw φ)
| Mw (φ ⋏ ψ)  := evaluate Mw φ ∧ evaluate Mw ψ
| (M,w) (□ φ) := ∀ v : W, (M.rel w v → evaluate (M,v) φ)

def tautology     (φ : formula) := ∀ W (M : kripkeModel W) w, evaluate (M,w) φ
def contradiction (φ : formula) := ∀ W (M : kripkeModel W) w, ¬ evaluate (M,w) φ

-- Definition 4, page 8

-- Definition 5, page 9
class has_sat (α : Type) := (satisfiable : α → Prop)
open has_sat
instance form_has_sat : has_sat formula := has_sat.mk (λ ϕ, ∃ W (M : kripkeModel W) w, evaluate (M,w) ϕ)
instance set_has_sat : has_sat (finset formula) := has_sat.mk (λ X, ∃ W (M : kripkeModel W) w, (∀ φ ∈ X, evaluate (M,w) φ))

lemma notsatisfnotThenTaut : ∀ φ, ¬ satisfiable (~φ) → tautology φ :=
begin
  intro phi,
  unfold satisfiable,
  unfold tautology,
  simp,
  intro lhs,
  intros W M w,
  specialize lhs W M w,
  unfold evaluate at *,
  simp at lhs,
  exact lhs,
end

@[simp]
lemma singletonSat_iff_sat : ∀ φ, satisfiable ({ φ } : finset formula) ↔ satisfiable φ :=
begin
  intro phi,
  unfold satisfiable,
  simp,
end

lemma tautImp_iff_comboNotUnsat {ϕ ψ} : tautology (ϕ ↣ ψ) ↔ ¬satisfiable ({ϕ, ~ψ} : finset formula) :=
begin
  unfold tautology,
  unfold satisfiable,
  simp,
  split ;
  { intro hyp,
    intros W M w,
    specialize hyp W M w,
    intro sat_phi,
    unfold evaluate at *, simp at *, tauto,
  },
end

def semImplies_sets (X : finset formula) (Y : finset formula) := ∀ (W : Type) (M : kripkeModel W) w,
  (∀ φ ∈ X, evaluate (M,w) φ) → (∀ ψ ∈ Y, evaluate (M,w) ψ)

-- Definition 5, page 9
class vDash {α : Type} {β : Type} := (semImplies : α → β → Prop)
open vDash
@[simp]
instance model_canSemImply_form {W : Type} : vDash := vDash.mk (@evaluate W)
@[simp]
instance model_canSemImply_set {W : Type} : vDash := @vDash.mk (kripkeModel W × W) (finset formula) (λ Mw X, ∀ f ∈ X, @evaluate W Mw f)
instance set_canSemImply_set : vDash := vDash.mk semImplies_sets
instance set_canSemImply_form : vDash := vDash.mk (λ X ψ, semImplies_sets X {ψ})
instance form_canSemImply_set : vDash := vDash.mk (λ φ X, semImplies_sets {φ} X)
instance form_canSemImply_form : vDash := vDash.mk (λ φ ψ, semImplies_sets {φ} {ψ})

infixl `⊨`:40 := semImplies
infixl `⊭`:40 := λ a b, ¬ (a ⊨ b)

-- useful lemmas to connect all the different ⊨ cases

lemma forms_to_sets { φ ψ : formula } : φ ⊨ ψ → ({φ}: finset formula) ⊨ ({ψ} : finset formula):=
begin
  intros impTaut,
  intros W M w lhs ψ1 psi1_in_setpsi,
  specialize impTaut W M w,
  simp at *,
  subst psi1_in_setpsi,
  apply impTaut,
  exact lhs
end
