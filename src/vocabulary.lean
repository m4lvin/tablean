-- VOCABULARY

import tactic.norm_num

import syntax
import setsimp

def vocabOfFormula : formula → finset char
| (⊥)      := set.to_finset { }
| ( (· c)) := { c }
| (~ φ)    := vocabOfFormula φ
| (φ ⋏ ψ ) := vocabOfFormula φ ∪ vocabOfFormula ψ
| (□ φ)    := vocabOfFormula φ

def vocabOfSetFormula : finset formula → finset char
| X := finset.bUnion X vocabOfFormula

class hasVocabulary (α : Type) := (voc : α → finset char)
open hasVocabulary
instance formula_hasVocabulary : hasVocabulary formula := hasVocabulary.mk vocabOfFormula
instance setFormula_hasVocabulary : hasVocabulary (finset formula) := hasVocabulary.mk vocabOfSetFormula

@[simp]
lemma vocOfNeg {ϕ} : vocabOfFormula (~ϕ) = vocabOfFormula ϕ := by split

lemma vocElem_subs_vocSet {ϕ X} : ϕ ∈ X → vocabOfFormula ϕ ⊆ vocabOfSetFormula X :=
begin
  apply finset.induction_on X,
  -- case ∅:
  intro phi_in_X, cases phi_in_X,
  -- case insert:
  intros ψ S psi_not_in_S IH psi_in_insert,
  unfold vocabOfSetFormula at *,
  simp,
  intros a aIn,
  simp at *,
  cases psi_in_insert,
  { subst psi_in_insert, left, exact aIn, },
  { tauto, },
end

lemma vocMonotone {X Y : finset formula} (hyp : X ⊆ Y) : voc X ⊆ voc Y :=
begin
  unfold voc, unfold vocabOfSetFormula at *,
  intros a aIn,
  unfold finset.bUnion at *,
  simp at *,
  tauto,
end

lemma vocPreserved (X : finset formula) (ψ ϕ) :
  ψ ∈ X → voc ϕ = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ}) :=
begin
  intros psi_in_X eq_voc,
  unfold voc at *,
  unfold vocabOfSetFormula,
  ext1,
  split,
  all_goals { intro a_in, norm_num at *, },
  { rcases a_in with ⟨θ,_,a_in_vocTheta⟩,
    by_cases h : θ = ψ,
    { left, rw eq_voc, rw ← h, exact a_in_vocTheta, },
    { right, use θ, tauto, },
  },
  { cases a_in,
    { use ψ, rw ← eq_voc, tauto, },
    { rcases a_in with ⟨θ,_,a_in_vocTheta⟩, use θ, tauto, }
  },
end
