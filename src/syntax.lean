-- SYNTAX

import order.bounded_order
import data.set.finite
import data.finset.fold

-- think about using α instead of char
-- imports?
-- use namespaces?

/- Formulas -/
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
infixr `⋀`:66        := formula.and
@[simp]
def impl (φ ψ : formula) := ~(φ ⋀ (~ψ))
infixr `↣`:55        := impl
infixl `⟷`:77        := λ ϕ ψ, (ϕ ↣ ψ) ⋀ (ψ ↣ ϕ)

@[simp]
instance : has_bot formula := ⟨formula.bottom⟩
instance : has_top formula := ⟨formula.neg formula.bottom⟩

-- showing formulas as strings that are valid Lean code
def formToString : formula → string
| ⊥       := "⊥"
| (· ch)  := repr ch
| ~f      := "~" ++ formToString f
| (f ⋀ g) := "(" ++ formToString f ++ " ⋀ " ++ formToString g ++ ")"
| (□ f)   := "(□ "++ formToString f ++ ")"

instance : has_repr formula := ⟨formToString⟩

-- COMPLEXITY

@[simp]
def lengthOfFormula : formula → ℕ
| (⊥)     := 1
| (· c)   := 1
| (~ φ)   := 1 + lengthOfFormula φ
| (φ ⋀ ψ) := 1 + lengthOfFormula φ + lengthOfFormula ψ
| (□ φ)  := 1 + lengthOfFormula φ

def lengthOfSet : finset formula → ℕ
| X := finset.fold (+) 0 lengthOfFormula X

def complexityOfFormula : formula → ℕ
| (⊥)     := 1
| (· c)   := 1
| (~ φ)   := 1 + lengthOfFormula φ
| (φ ⋀ ψ) := 1 + max (lengthOfFormula φ) (lengthOfFormula ψ)
| (□ φ)  := 1 + lengthOfFormula φ

def complexityOfSet : finset formula → ℕ
| X := finset.fold (+) 0 complexityOfFormula X

class hasComplexity (α : Type) := (complexityOf : α → ℕ)
open hasComplexity
instance formula_hasComplexity : hasComplexity formula := hasComplexity.mk complexityOfFormula
instance setFormula_hasComplexity : hasComplexity (finset formula) := hasComplexity.mk complexityOfSet

-- VOCABULARY

def vocabOfFormula : formula → finset char
| (⊥)       := set.to_finset { }
| ( (· c))  := { c }
| (~ φ)     := vocabOfFormula φ
| ((φ ⋀ ψ)) := vocabOfFormula φ ∪ vocabOfFormula ψ
| ((□ φ))   := vocabOfFormula φ

def vocabOfSetFormula : finset formula → finset char
| (X) := finset.fold (∪) ∅ vocabOfFormula X

class hasVocabulary (α : Type) := (voc : α → finset char)
open hasVocabulary
instance formula_hasVocabulary : hasVocabulary formula := hasVocabulary.mk vocabOfFormula
instance setFormula_hasVocabulary : hasVocabulary (finset formula) := hasVocabulary.mk vocabOfSetFormula
