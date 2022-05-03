-- SYNTAX

import order.bounded_order
import data.set.finite
import data.finset.fold
import algebra.big_operators.basic

-- Definition 1, page 4
@[derive decidable_eq]
inductive formula : Type
| bottom : formula
| atom_prop : char -> formula
| neg : formula → formula
| and : formula → formula → formula
| box : formula → formula

/- Predefined atomic propositions for convenience -/
def p := formula.atom_prop 'p'
def q := formula.atom_prop 'q'
def r := formula.atom_prop 'r'

/- Notation and abbreviations -/
notation `·` c       := formula.atom_prop c
prefix `~`:88        := formula.neg
prefix `□`:77        := formula.box
infixr `⋏`:66        := formula.and
@[simp]
def impl (φ ψ : formula) := ~(φ ⋏ (~ψ))
infixr `↣`:55        := impl
infixl `⟷`:77        := λ ϕ ψ, (ϕ ↣ ψ) ⋏ (ψ ↣ ϕ)

@[simp]
instance : has_bot formula := ⟨formula.bottom⟩
instance : has_top formula := ⟨formula.neg formula.bottom⟩

-- showing formulas as strings that are valid Lean code
def formToString : formula → string
| ⊥       := "⊥"
| (· c)   := repr c
| ~ϕ      := "~" ++ formToString ϕ
| (ϕ ⋏ ψ) := "(" ++ formToString ϕ ++ " ⋏ " ++ formToString ψ ++ ")"
| (□ ϕ)   := "(□ "++ formToString ϕ ++ ")"

instance : has_repr formula := ⟨formToString⟩

-- COMPLEXITY

-- this should later be the measure from Lemma 2, page 20
@[simp]
def lengthOfFormula : formula → ℕ
| (⊥)     := 1 -- FIXME: has bad width
| (· c)   := 1
| (~ φ)   := 1 + lengthOfFormula φ
| (φ ⋏ ψ) := 1 + lengthOfFormula φ + lengthOfFormula ψ
| (□ φ)   := 1 + lengthOfFormula φ

@[simp]
def lengthOfSet : finset formula → ℕ
| X := X.sum lengthOfFormula

class hasLength (α : Type) := (lengthOf : α → ℕ)
open hasLength
instance formula_hasLength : hasLength formula := hasLength.mk lengthOfFormula
instance setFormula_hasLength : hasLength (finset formula) := hasLength.mk lengthOfSet

@[simp]
def complexityOfFormula : formula → ℕ
| (⊥)     := 1
| (· c)   := 1
| (~ φ)   := 1 + complexityOfFormula φ
| (φ ⋏ ψ) := 1 + max (complexityOfFormula φ) (complexityOfFormula ψ)
| (□ φ)   := 1 + complexityOfFormula φ

def complexityOfSet : finset formula → ℕ
| X := X.sum complexityOfFormula

class hasComplexity (α : Type) := (complexityOf : α → ℕ)
open hasComplexity
instance formula_hasComplexity : hasComplexity formula := hasComplexity.mk complexityOfFormula
instance setFormula_hasComplexity : hasComplexity (finset formula) := hasComplexity.mk complexityOfSet

-- VOCABULARY

def vocabOfFormula : formula → finset char
| (⊥)      := set.to_finset { }
| ( (· c)) := { c }
| (~ φ)    := vocabOfFormula φ
| (φ ⋏ ψ ) := vocabOfFormula φ ∪ vocabOfFormula ψ
| (□ φ)    := vocabOfFormula φ

def vocabOfSetFormula : finset formula → finset char
| X := finset.fold (∪) ∅ vocabOfFormula X

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
  { right, apply IH psi_in_insert aIn, },
end
