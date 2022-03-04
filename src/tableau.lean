-- TABLEAU

import syntax
import semantics
import data.finset.basic
import data.finset.pimage
import algebra.big_operators.order
import tactic

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

-- TODO: this is unused?
lemma proj_singleton (g : formula) :
  projection { g } = ∅  ∨  projection { g } = (formProjection g).to_finset :=
begin
  cases g,
  all_goals { simp, finish, },
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
| stuck { α } : (¬ ∃ B (_ : rule α B), true) → tableau α

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

-- replace this with finset.insert_eq  ??
@[simp]
lemma union_singleton_is_insert {X : finset formula} {f : formula} :
  X ∪ {f} = insert f X :=
begin
  apply finset.induction_on X,
  simp,
  intros g Y gNotInY IH,
  simp,
  injections_and_clear,
  ext1,
  finish,
end

@[simp]
lemma sdiff_singleton_is_erase {X : finset formula} {f : formula} :
  X \ {f} = X.erase f :=
begin
  apply finset.induction_on X,
  simp,
  intros g Y gNotInY IH,
  ext1,
  finish,
end

@[simp]
lemma lengthAdd {X : finset formula} :
  ∀ {f} (h : f ∉ X), lengthOfSet (insert f X) = lengthOfSet X + lengthOfFormula f :=
begin
  apply finset.induction_on X,
  {
    unfold lengthOfSet,
    simp,
  },
  {
    intros g Y gNotInY IH,
    unfold lengthOfSet at *,
    intros f h,
    finish,
  },
end


lemma lemmaVanEmma {X: finset formula} :
  ∀ {f},lengthOfSet (insert f X) ≤ lengthOfSet X + lengthOfFormula f :=
begin
intro f,
cases (em (f ∈ X)),
{ rw finset.insert_eq_of_mem h, simp, },
{ rw lengthAdd h, },
end

@[simp]
lemma lengthRemove (X : finset formula) :
  ∀ f ∈ X, lengthOfSet (X.erase f) + lengthOfFormula f = lengthOfSet X :=
begin
  intros f fInX,
  have claim : lengthOfSet (insert f (X \ {f})) = lengthOfSet (X \ {f}) + lengthOfFormula f,
  {
    apply lengthAdd,
    simp,
  },
  have anotherClaim : insert f (X \ {f}) = X, {
    ext1,
    simp only [finset.mem_sdiff, finset.mem_insert, finset.mem_singleton],
    split,
    finish,
    tauto,
  },
  rw anotherClaim at claim,
  finish,
end

@[simp]
lemma lengthRemoveMin (X : finset formula) :
  ∀ f ∈ X, lengthOfSet (X.erase f) = lengthOfSet X - lengthOfFormula f:=
begin
  intros f fInX,
  have claim := lengthRemove X f fInX,
  dsimp at *,
  omega,
end

lemma sum_union_le { T } [decidable_eq T] : ∀ { X Y : finset T } { F : T → ℕ }, (X ∪ Y).sum F ≤ X.sum F + Y.sum F :=
begin
  intros X Y F,
  { calc (X ∪ Y).sum F
       ≤ (X ∪ Y).sum F + (X ∩ Y).sum F : by { simp, }
   ... = X.sum F + Y.sum F : finset.sum_union_inter,
  },
end

-- avoid α and β for formula sets (follow Borzechowski and use X for set)
open hasComplexity -- remove?
open hasLength

lemma rulesDecreaseLength { α : finset formula } { B : finset (finset formula) } (r : rule α B) :
  ∀ β ∈ B, lengthOfSet β < lengthOfSet α :=
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
    subst inB,
    { calc lengthOfSet (insert r_f (α.erase (~~r_f)))
         ≤ lengthOfSet (α.erase (~~r_f)) + lengthOf (r_f) : by { apply lemmaVanEmma, }
     ... < lengthOfSet (α.erase (~~r_f)) + lengthOf (r_f) + 2 : by { simp, }
     ... = lengthOfSet (α.erase (~~r_f)) + lengthOf (~~r_f) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet α : lengthRemove α (~~r_f) r_h,
    },
  },
  case rule.con : {
    subst inB,
    apply gt.lt, -- TODO remove this and turn around calc proof
    { calc lengthOfSet α
         = lengthOf (α.erase (r_f⋀r_g)) + lengthOf (r_f⋀r_g) : (lengthRemove α (r_f⋀r_g) r_h).symm
     ... = lengthOf (α.erase (r_f⋀r_g)) + lengthOf r_f + lengthOf r_g + 1 :
           by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... > lengthOf (α.erase (r_f⋀r_g)) + lengthOf r_f + lengthOf r_g : by { unfold lengthOf, simp, }
     ... = lengthOf (α.erase (r_f⋀r_g)) + lengthOf r_g + lengthOf r_f : by { ring, }
     ... ≥ lengthOf (insert r_g (α.erase (r_f⋀r_g))) + lengthOf r_f : by { simp, apply lemmaVanEmma, }
     ... ≥ lengthOf (insert r_f (insert r_g (α.erase (r_f⋀r_g)))) : by { simp, apply lemmaVanEmma, },
    },
  },
  case rule.nCo : {
    cases inB, -- splitting rule!
    all_goals {
      subst inB,
    },
    { -- f
    calc lengthOfSet (insert (~r_f) (α.erase (~(r_f⋀r_g))))
         ≤ lengthOfSet (α.erase (~(r_f⋀r_g))) + lengthOf (~r_f) : lemmaVanEmma
     ... < lengthOfSet (α.erase (~(r_f⋀r_g))) + 1 + 1 + lengthOf r_f + lengthOf r_g :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (α.erase (~(r_f⋀r_g))) + lengthOf (~(r_f⋀r_g)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet α : lengthRemove α (~(r_f⋀r_g)) r_h,
    },
    { -- g
    calc lengthOfSet (insert (~r_g) (α.erase (~(r_f⋀r_g))))
         ≤ lengthOfSet (α.erase (~(r_f⋀r_g))) + lengthOf (~r_g) : lemmaVanEmma
     ... < lengthOfSet (α.erase (~(r_f⋀r_g))) + 1 + 1 + lengthOf r_f + lengthOf r_g :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (α.erase (~(r_f⋀r_g))) + lengthOf (~(r_f⋀r_g)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet α : lengthRemove α (~(r_f⋀r_g)) r_h,
    },
  },
  case rule.atm : {
    subst inB,
    -- TODO: move some of these to top level lemmas
    have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f, {
      intros f g g_is_fP_f, cases f, all_goals { finish, },
    },
    have proj_claim : ∀ f, (projection {f}).sum lengthOfFormula ≤ lengthOfFormula f, {
      intro f,
      cases f,
      { omega, },
      { exact dec_trivial, },
      { exact dec_trivial, },
      { exact dec_trivial, },
      { have subsubClaim : projection {□f} = {f}, {
          ext1, rw proj, simp,
        },
        rw subsubClaim,
        unfold lengthOfFormula, simp,
      },
    },
    have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet { f }, {
      intro f, unfold lengthOfSet, simp,
    },
    have insert_comm_proj : ∀ X f, projection (insert f X) = (projection {f}) ∪ (projection X), {
      intros X f,
      unfold projection,
      ext1 g,
      simp,
      split, all_goals { finish, },
    },
    have claim : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X, {
      intro X,
      apply finset.induction_on X,
      { unfold lengthOfSet, simp, intros f f_in_empty, cases f_in_empty, },
      { simp, intros f S f_not_in_S IH,
        unfold lengthOfSet,
        rw finset.sum_insert f_not_in_S,
        simp,
        { calc (projection (insert f S)).sum lengthOfFormula
             = (projection (insert f S)).sum lengthOfFormula : refl _
         ... = (projection {f} ∪ projection S).sum lengthOfFormula : by { rw insert_comm_proj S f, }
         ... ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula : by { apply sum_union_le, }
         ... ≤ lengthOfFormula f + (projection S).sum lengthOfFormula : by { simp, apply proj_claim, }
         ... ≤ lengthOfFormula f + S.sum lengthOfFormula : by { simp, apply IH, },
        },
      },
    },
    have otherClaim : projection α = projection (α.erase (~□r_f)), {
      ext1 phi,
      rw proj, rw proj,
      simp,
    },
    { calc lengthOfSet (insert (~r_f) (projection α))
         ≤ lengthOfSet (projection α) + lengthOf (~r_f) : lemmaVanEmma
     ... = lengthOfSet (projection α) + 1 + lengthOf r_f : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... < lengthOfSet (projection α) + 1 + 1 + lengthOf r_f : by { simp, }
     ... = lengthOfSet (projection α) + lengthOf (~□r_f) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet (projection (α.erase (~□r_f))) + lengthOf (~□r_f) : by { rw otherClaim, }
     ... ≤ lengthOfSet (α.erase (~□r_f)) + lengthOf (~□r_f) : by { simp, apply claim, }
     ... = lengthOfSet α : lengthRemove α (~□r_f) r_h,
    }
  },
end

-- maybe this should be data and not Prop ? // → tableau α
def existsTableauFor : ∀ N α, N = lengthOf α → ∃ _ : tableau α, true :=
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
      have rDec := rulesDecreaseLength (rule.neg h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.con : _ f g h {
      have t := tableau.byRule (rule.con h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (rule.con h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.nCo : _ f g h {
      have t := tableau.byRule (rule.nCo h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (rule.nCo h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case rule.atm : _ _ h {
      have t := tableau.byRule (rule.atm h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (rule.atm h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
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
