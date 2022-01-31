import order.complete_lattice
import order.fixed_points
import data.set.lattice

import syntax

/- Kripke Models wih one binary relation  -/
structure kripkeModel (W : Type) : Type :=
  (val : W → char → Prop)
  (rel : W → W → Prop)

def evaluate {W : Type} : kripkeModel W → W → formula → Prop
| M w ⊥       := false
| M w (· c)   := M.val w c
| M w (~ φ)   := not (evaluate M w φ)
| M w (φ ⋀ ψ) := evaluate M w φ ∧ evaluate M w ψ
| M w ([] φ) := ∀ v : W, (M.rel w v → evaluate M v φ)

@[simp]
def evaluatePoint {W : Type} : (kripkeModel W × W) → formula → Prop
| (M,w) ϕ := evaluate M w ϕ

def tautology     (φ : formula) := ∀ W (M : kripkeModel W) w, evaluatePoint (M, w) φ
def contradiction (φ : formula) := ∀ W (M : kripkeModel W) w, ¬ evaluatePoint (M, w) φ

-- TODO class satisf
def satisfiable   (φ : formula) := ∃ W (M : kripkeModel W) w, evaluate M w φ
def setSatisfiable (X : finset formula) := ∃ W (M : kripkeModel W) w, (∀ φ ∈ X, evaluate M w φ)

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

lemma sat_iff_singleton_sat : ∀ φ, satisfiable φ ↔ setSatisfiable { φ } :=
begin
  intro phi,
  unfold satisfiable,
  unfold setSatisfiable,
  simp,
end

def semImplies_sets (X : finset formula) (Y : finset formula) := ∀ (W : Type) (M : kripkeModel W) w,
  (∀ φ ∈ X, evaluatePoint (M, w) φ) → (∀ ψ ∈ Y, evaluatePoint (M, w) ψ)

class vDash {α : Type} {β : Type} := (semImplies : α → β → Prop)
open vDash
@[simp]
instance model_canSemImply_form {W : Type} : vDash := vDash.mk (@evaluatePoint W)
@[simp]
instance model_canSemImply_set {W : Type} : vDash := @vDash.mk (kripkeModel W × W) (finset formula) (λ Mw X, ∀ f ∈ X, @evaluatePoint W Mw f)
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
  intros W M w lhs ψ psi_in_psi,
  specialize impTaut W M w,
  simp at psi_in_psi lhs impTaut,
  rewrite psi_in_psi, -- needed even though no ψ_1 in goal here?!
  apply impTaut,
  exact lhs
end
