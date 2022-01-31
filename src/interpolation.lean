import syntax
import semantics

open hasVocabulary vDash

def interpolant (φ : formula) (ψ : formula) (θ : formula) :=
  φ ⊨ θ  ∧  θ ⊨ ψ  ∧  voc θ ⊆ (voc φ ∩ voc ψ)

-- TODO: should set interpolation be defined using ⊨ or ⊢ or do we need both?

-- NOTE: this notion here is NOT (yet) equivalent to the one used by Borzechowski.

def setInterpolant (X : finset formula) (Y : finset formula) (θ : formula) :=
  (X ⊨ θ)  ∧  (θ ⊨ Y)  ∧  voc θ ⊆ (voc X ∩ voc Y)

lemma setInterpolation :
  ∀ (X : finset formula) (Y : finset formula), (X ⊨ Y) → ∃ (θ : formula), setInterpolant X Y θ :=
begin
  sorry
end

lemma interpolation :
  ∀ (φ : formula) (ψ : formula), (φ ⊨ ψ → ∃ (θ : formula), interpolant φ ψ θ) :=
begin
  intros φ ψ hyp,
  have haveInt := setInterpolation {φ} {ψ} (forms_to_sets hyp),
  cases haveInt with θ haveInt_hyp,
  use θ,
  unfold setInterpolant at haveInt_hyp,
  cases haveInt_hyp with φ_θ haveInt_hyp,
  cases haveInt_hyp with θ_ψ vocSubs,
  unfold interpolant,
  split,
  { use φ_θ, },
  split,
  { use θ_ψ, },
  { unfold voc, unfold voc at vocSubs,
    unfold vocabOfSetFormula at vocSubs,
    simp at vocSubs,
    exact vocSubs,
  },
end
