-- TABLEAU

import syntax
import semantics
import data.finset.basic
import data.finset.pimage

-- Definition 9
-- TODO add programs here!
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def closed : finset formula → Prop := λ X, ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X
-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def simpleForm : formula → Prop
| ⊥       := true
| (· _)   := true
| ~(· _)  := true
| (□ _)   := true
| ~(□ _)  := true
| _       := false
def simple : finset formula → Prop := λ X, ∀ P ∈ X, simpleForm P
-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : formula → option formula
| (□f) := some f
| _    := none
def projection : finset formula → finset formula := finset.pimage (part.of_option ∘ formProjection)

#eval projection { ~p, □□q, □q }

lemma proj { g: formula } { X : finset formula } :
  g ∈ projection X ↔ □g ∈ X :=
begin
  unfold projection,
  simp,
  split,
  {
    intro lhs,
    rcases lhs with ⟨ boxg, boxg_in_X, projboxg_is_g ⟩,
    cases boxg,
    repeat { finish },
  },
  {
    intro rhs,
    use □g,
    split,
    exact rhs,
    simp,
  },
end

-- -- IDEA: can we have a type were all its instances are tableau according to rules?
-- -- (note that correct does not mean closed!!)
-- from general to more demanding, which of these should the tableau data type represent?
-- - any tree
-- - tableau according to rules
-- - maximal tableau <<<<<<<<<<<<<<<<<<<<< new definition which we use now
-- - maximal and closed tableau <<<<<<< old definition! was too strict

open formula

-- rules: given this set, apply rule to formula, resulting in these new sets
-- rename candidates: "step" or "ruleApplication"
inductive rule : finset formula → finset (finset formula) → Type
-- closing rules:
| bot { α     } ( h : ⊥ ∈ α )          : rule α ∅
| not { α f   } ( h : f ∈ α ∧ ~f ∈ α ) : rule α ∅
-- simple rules:
| neg { α f   } ( h : ~~f        ∈ α ) : rule α { (α \ {~~f}) ∪ { f }    }
| con { α f g } ( h : f ⋀ g      ∈ α ) : rule α { (α \ {f ⋀ g}) ∪ { f, g } }
-- splitting rule:
| nCo { α f g } ( h : ~(f ⋀ g)   ∈ α ) : rule α { α \ { ~ (f ⋀ g) } ∪ {~f}
                                                , α \ { ~ (f ⋀ g) } ∪ {~g} }
-- the atomic rule:
| atm { α f   } ( h : ~□f       ∈ α ) : rule α { projection α ∪ {~f} }

-- Note: any tableau is maximal.
inductive tableau : finset formula → Type
| byRule { α B } (_ : rule α B) (_ : Π β ∈ B, tableau β) : tableau α
| stuck { α   } : (¬ ∃ B (_ : rule α B), true) → tableau α

-- approaches how to represent closed tableau:
-- - inductive Prop and then subtype <<<<< currently using this.
-- - inductive Type, then write conversion functions?
--   inductive closedTableau : finset formula → Type -- might not be possible to do ∀ α :-(
inductive isClosedTableau : Π { α : finset formula }, tableau α -> Prop
| byRule { α } { B } (r : rule α B) (prev : Π β ∈ B, tableau β) :
    (∀ β, Π H : β ∈ B, isClosedTableau (prev β H)) → isClosedTableau (tableau.byRule r prev)

@[simp]
lemma closedTableauIffChildrenClosed { X B r children }:
  isClosedTableau (tableau.byRule (r : rule X B) children) ↔
    ∀ t H, isClosedTableau (children t H) :=
begin
  split,
  { intro lhs,
    intros t H,
    cases lhs with _ _ _ _ children_closed,
    apply children_closed, },
  { intro rhs,
    apply isClosedTableau.byRule,
    apply rhs, },
end

@[simp]
lemma stuckTableausIsNotClosed { X h } :
  ¬ isClosedTableau (@tableau.stuck X h) :=
begin
  by_contra,
  cases h,
end


@[simp]
def closedTableau ( α ) := subtype (@isClosedTableau α)

@[simp]
def openTableau ( α ) := subtype (λ t, not (@isClosedTableau α t))

-- is this useful/needed?
@[simp]
def complexityOfTableau : (Σ (α : finset formula) , tableau α) → ℕ
| (⟨α,_⟩) := complexityOfSet α

inductive provable : formula → Prop
| byTableau {φ : formula} : closedTableau { ~ φ } → provable φ

-- Definition 17, page 30
def inconsistent : finset formula → Prop
| X := ∃ t : closedTableau X, true
def consistent : finset formula → Prop
| X := ¬ inconsistent X

-- avoid α and β for formula sets (follow Borzechowski and use X for set)
open hasComplexity
lemma rulesDecreaseComplexity { α : finset formula } { B : finset (finset formula) } (r : rule α B) :
  ∀ β ∈ B, complexityOf β < complexityOf α :=
begin
  cases r,
  all_goals { intros β inB, simp at *, },
  case rule.bot : {
    cases inB, -- no premises
  },
  case rule.not : {
    cases inB, -- no premises
  },
  case rule.neg : {
    subst inB, unfold complexityOf,
    unfold complexityOfSet,
    sorry, -- TODO

  },
  case rule.con : {
    subst inB, unfold complexityOf, unfold complexityOfSet,
    sorry, -- TODO
  },
  case rule.nCo : {
    cases inB, -- splitting rule!
    all_goals {
      subst inB,
      unfold complexityOf,
      unfold complexityOfSet,
    },
    { -- f
      sorry, -- TODO
    },
    { -- g
      sorry,
    },
  },
  case rule.atm : {
    subst inB, unfold complexityOf, unfold complexityOfSet,
    sorry, -- TODO
  },
end

-- maybe this should be data and not Prop ? // → tableau α
def existsTableauFor : ∀ N α, N = complexityOf α → ∃ _ : tableau α, true :=
begin
  intro N,
  apply nat.strong_induction_on N, -- TODO: only works in Prop?
  intros n IH α nDef,
  have canApplyRule := em (¬ ∃ B (_ : rule α B), true),
  cases canApplyRule,
  {
    use tableau.stuck canApplyRule,
  },
  {
    simp at canApplyRule,
    cases canApplyRule with B r_exists,
    cases r_exists with r _hyp,
    cases r,
    case rule.bot : _ h {
      have t := (tableau.byRule (rule.bot h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case rule.not : _ _ h {
      have t := (tableau.byRule (rule.not h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case rule.neg : _ f h {
      have t := (tableau.byRule (rule.neg h)) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseComplexity (rule.neg h) beta beta_def,
      subst nDef,
      specialize IH (complexityOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.con : _ f g h {
      have t := tableau.byRule (rule.con h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseComplexity (rule.con h) beta beta_def,
      subst nDef,
      specialize IH (complexityOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.nCo : _ f g h {
      have t := tableau.byRule (rule.nCo h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseComplexity (rule.nCo h) beta beta_def,
      subst nDef,
      specialize IH (complexityOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.atm : _ _ h {
      have t := tableau.byRule (rule.atm h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseComplexity (rule.atm h) beta beta_def,
      subst nDef,
      specialize IH (complexityOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
  }
end

-- try these:
-- #print existsTableauFor
-- reduce
-- eval
