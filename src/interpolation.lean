import syntax
import semantics
import completeness
import partitions

open hasVocabulary vDash

def interpolant (φ : formula) (ψ : formula) (θ : formula) :=
  tautology (φ ↣ θ)  ∧  tautology (θ ↣ ψ)  ∧  voc θ ⊆ (voc φ ∩ voc ψ)

open has_sat

lemma interpolation {ϕ ψ} : tautology (ϕ ↣ ψ) → ∃ (θ : formula), interpolant ϕ ψ θ :=
begin
  intros hyp,
  let X1 : finset formula := {ϕ},
  let X2 : finset formula := {~ψ},
  have ctX : closedTableau (X1 ∪ X2), {
    rw tautImp_iff_comboNotUnsat at hyp,
    rw ← completeness at hyp, -- using completeness!
    unfold consistent at hyp,
    simp at hyp,
    unfold inconsistent at hyp,
    change closedTableau {ϕ, ~ψ},
    exact classical.choice hyp,
  },
  have partInt := tabToInt ctX, -- using tableau interpolation!
  rcases partInt with ⟨θ,pI_prop⟩,
  unfold partInterpolant at pI_prop,
  use θ,
  split,
  { rw tautImp_iff_comboNotUnsat, tauto, },
  split,
  { rw tautImp_iff_comboNotUnsat, simp at *, tauto, },
  { cases pI_prop, unfold voc vocabOfSetFormula at *, simp at *, tauto, },
end
