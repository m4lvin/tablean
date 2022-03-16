-- TABLEAU

import syntax
import semantics
import data.finset.basic
import data.finset.pimage
import algebra.big_operators.order
import tactic

open formula

-- Definition 9, page 15
-- TODO add programs here!
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def closed : finset formula → Prop := λ X, ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X
-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def simpleForm : formula → Prop
| ⊥       := true
| (~⊥)    := true -- added!
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

-- #eval projection { ~p, □□q, □q }

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

-- rules: given this set, apply rule to formula, resulting in these new sets
-- rename candidates: "step" or "ruleApplication"
inductive rule : finset formula → finset (finset formula) → Type
-- closing rules:
| bot { X     } ( h : ⊥ ∈ X )          : rule X ∅
| not { X ϕ   } ( h : ϕ ∈ X ∧ ~ϕ ∈ X ) : rule X ∅
-- simple rules:
| neg { X ϕ   } ( h : ~~ϕ        ∈ X ) : rule X { (X \ {~~ϕ}) ∪ { ϕ }    }
| con { X ϕ ψ } ( h : ϕ ⋏ ψ      ∈ X ) : rule X { (X \ {ϕ ⋏ ψ}) ∪ { ϕ, ψ } }
-- splitting rule:
| nCo { X ϕ ψ } ( h : ~(ϕ ⋏ ψ)   ∈ X ) : rule X { X \ { ~ (ϕ ⋏ ψ) } ∪ {~ϕ}
                                                , X \ { ~ (ϕ ⋏ ψ) } ∪ {~ψ} }
-- the atomic rule:
| atm { X ϕ   } ( h : ~□ϕ       ∈ X )  : rule X { projection X ∪ {~ϕ} }

def isLocalRule : ∀ X B, rule X B  → Prop
| _ _ (rule.bot _) := true
| _ _ (rule.not _) := true
| _ _ (rule.neg _) := true
| _ _ (rule.con _) := true
| _ _ (rule.nCo _) := true
| _ _ (rule.atm _) := false

@[simp]
def localRule ( X B ) := subtype (@isLocalRule X B)

-- If X is not simple, then a local rule can be applied.
-- (page 13)
lemma notSimpleThenLocalRule { X } :
  ¬ simple X → (∃ B (_ : localRule X B), true) :=
begin
  intro notSimple,
  unfold simple at notSimple,
  simp at notSimple,
  rcases notSimple with ⟨ ϕ , ϕ_in_X, ϕ_not_simple ⟩,
  cases ϕ,
  case bottom: { tauto },
  case atom_prop: { tauto },
  case neg: ψ {
    cases ψ,
    case bottom: { tauto, },
    case atom_prop: { tauto, },
    case neg: {
      unfold simpleForm at *,
      use { (X \ {~~ψ}) ∪ { ψ } },
      split, split, rotate,
      use rule.neg ϕ_in_X,
      tauto,
      unfold isLocalRule,
    },
    case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ1}, X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ2} },
      split, split, rotate,
      use rule.nCo ϕ_in_X,
      tauto,
      unfold isLocalRule,
    },
    case box: { unfold simpleForm at *, tauto, },
  },
  case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { (X \ {ψ1 ⋏ ψ2}) ∪ { ψ1, ψ2 } },
      split, split, rotate,
      use rule.con ϕ_in_X,
      tauto,
      unfold isLocalRule,
  },
  case box: { unfold simpleForm at *, tauto, },
end

-- Definition 8, page 14
-- Note: any (t : tableau) is local-maximal.
inductive tableau : finset formula → Type
| byRule   { X B } (_ : rule X B) (_ : Π Y ∈ B, tableau Y) : tableau X
| stuck    { X } : (¬ ∃ B (_ : rule X B), true) → tableau X
| endLocal { X } : (¬ ∃ B (_ : localRule X B), true) → tableau X

-- approaches how to represent closed tableau:
-- - inductive Prop and then subtype <<<<< currently using this.
-- - inductive Type, then write conversion functions?
--   inductive closedTableau : finset formula → Type -- might not be possible to do ∀ α :-(
-- Definition 16, page 29
inductive isClosedTableau : Π { X : finset formula }, tableau X -> Prop
| byRule { X } { B } (r : rule X B) (prev : Π Y ∈ B, tableau Y) :
    (∀ Y, Π H : Y ∈ B, isClosedTableau (prev Y H)) → isClosedTableau (tableau.byRule r prev)

def closedTableau ( X ) := subtype (@isClosedTableau X)

def openTableau ( X ) := subtype (λ t, not (@isClosedTableau X t))

-- ca. Definition 11 (with all PDL stuff missing for now)
inductive isLocalTableau : Π { X : finset formula }, tableau X -> Prop
| byLocalRule{ X } { B } (r : localRule X B) (prev : Π Y ∈ B, tableau Y) :
    (∀ Y, Π H : Y ∈ B, isLocalTableau (prev Y H)) → isLocalTableau (tableau.byRule r.val prev)
| byEndLocal { X } (h : ¬ ∃ B (_ : localRule X B), true) : isLocalTableau (tableau.endLocal h)

@[simp]
def localTableau ( X ) := subtype (@isLocalTableau X)

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

-- is this useful/needed?
@[simp]
def complexityOfTableau : (Σ (X : finset formula) , tableau X) → ℕ
| (⟨X,_⟩) := complexityOfSet X

inductive provable : formula → Prop
| byTableau {φ : formula} : closedTableau { ~ φ } → provable φ

-- Definition 17, page 30
def inconsistent : finset formula → Prop
| X := ∃ t : tableau X, isClosedTableau t
def consistent : finset formula → Prop
| X := ¬ inconsistent X

@[simp]
lemma union_singleton_is_insert {X : finset formula} {ϕ: formula} :
  X ∪ {ϕ} = insert ϕ X :=
begin
  have fo := finset.insert_eq ϕ X,
  finish,
end

@[simp]
lemma sdiff_singleton_is_erase {X : finset formula} {ϕ: formula} :
  X \ {ϕ} = X.erase ϕ :=
begin
  apply finset.induction_on X,
  simp,
  intros g Y gNotInY IH,
  ext1,
  finish,
end

@[simp]
lemma lengthAdd {X : finset formula} :
  ∀ {ϕ} (h : ϕ ∉ X), lengthOfSet (insert ϕ X) = lengthOfSet X + lengthOfFormula ϕ :=
begin
  apply finset.induction_on X,
  {
    unfold lengthOfSet,
    simp,
  },
  {
    intros ψ Y psiNotInY IH,
    unfold lengthOfSet at *,
    intros ϕ h,
    finish,
  },
end

lemma lengthOf_insert_leq_plus {X: finset formula} {ϕ : formula} :
  lengthOfSet (insert ϕ X) ≤ lengthOfSet X + lengthOfFormula ϕ :=
begin
cases (em (ϕ ∈ X)) with in_x not_in_x,
{ rw finset.insert_eq_of_mem in_x, simp, },
{ rw lengthAdd not_in_x, },
end

@[simp]
lemma lengthRemove (X : finset formula) :
  ∀ ϕ ∈ X, lengthOfSet (X.erase ϕ) + lengthOfFormula ϕ = lengthOfSet X :=
begin
  intros ϕ in_X,
  have claim : lengthOfSet (insert ϕ (X \ {ϕ})) = lengthOfSet (X \ {ϕ}) + lengthOfFormula ϕ,
  {
    apply lengthAdd,
    simp,
  },
  have anotherClaim : insert ϕ (X \ {ϕ}) = X, {
    ext1,
    simp only [finset.mem_sdiff, finset.mem_insert, finset.mem_singleton],
    split,
    finish,
    tauto,
  },
  rw anotherClaim at claim,
  finish,
end

lemma projection_length_leq : ∀ f, (projection {f}).sum lengthOfFormula ≤ lengthOfFormula f :=
begin
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
end

lemma sum_union_le { T } [decidable_eq T] : ∀ { X Y : finset T } { F : T → ℕ }, (X ∪ Y).sum F ≤ X.sum F + Y.sum F :=
begin
  intros X Y F,
  { calc (X ∪ Y).sum F
       ≤ (X ∪ Y).sum F + (X ∩ Y).sum F : by { simp, }
   ... = X.sum F + Y.sum F : finset.sum_union_inter,
  },
end

lemma projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
begin
intro X,
apply finset.induction_on X,
{ unfold lengthOfSet, simp, intros f f_in_empty, cases f_in_empty, },
{ intros f S f_not_in_S IH,
  unfold lengthOfSet,
  rw finset.sum_insert f_not_in_S,
  simp,
  have insert_comm_proj : ∀ X f, projection (insert f X) = (projection {f}) ∪ (projection X), {
    intros X f,
    unfold projection,
    ext1 g,
    simp,
    split, all_goals { finish, },
  },
  { calc (projection (insert f S)).sum lengthOfFormula
       = (projection (insert f S)).sum lengthOfFormula : refl _
   ... = (projection {f} ∪ projection S).sum lengthOfFormula : by { rw insert_comm_proj S f, }
   ... ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula : by { apply sum_union_le, }
   ... ≤ lengthOfFormula f + (projection S).sum lengthOfFormula : by { simp, apply projection_length_leq, }
   ... ≤ lengthOfFormula f + S.sum lengthOfFormula : by { simp, apply IH, },
  },
},
end

-- avoid α and β for formula sets (follow Borzechowski and use X for set)
open hasComplexity -- remove?
open hasLength

lemma rulesDecreaseLength { X : finset formula } { B : finset (finset formula) } (r : rule X B) :
  ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
begin
  cases r,
  all_goals { intros β inB, simp at *, },
  case rule.bot : {
    cases inB, -- no premises
  },
  case rule.not : {
    cases inB, -- no premises
  },
  case rule.neg : X ϕ notnot_in_X {
    subst inB,
    { calc lengthOfSet (insert ϕ (X.erase (~~ϕ)))
         ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) : by { apply lengthOf_insert_leq_plus, }
     ... < lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) + 2 : by { simp, }
     ... = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~~ϕ) notnot_in_X,
    },
  },
  case rule.con : X ϕ ψ in_X {
    subst inB,
    apply gt.lt, -- TODO remove this and turn around calc proof
    { calc lengthOfSet X
         = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf (ϕ⋏ψ) : (lengthRemove X (ϕ⋏ψ) in_X).symm
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ + 1 :
           by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... > lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ : by { unfold lengthOf, simp, }
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ψ + lengthOf ϕ : by { ring, }
     ... ≥ lengthOf (insert ψ (X.erase (ϕ⋏ψ))) + lengthOf ϕ : by { simp, apply lengthOf_insert_leq_plus, }
     ... ≥ lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋏ψ)))) : by { simp, apply lengthOf_insert_leq_plus, },
    },
  },
  case rule.nCo : X ϕ ψ in_X {
    cases inB, -- splitting rule!
    all_goals {
      subst inB,
    },
    { -- f
    calc lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
    { -- g
    calc lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ψ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
  },
  case rule.atm : X ϕ in_X {
    subst inB,
    -- TODO: move some of these to top level lemmas
    have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f, {
      intros f g g_is_fP_f, cases f, all_goals { finish, },
    },
    have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet { f }, {
      intro f, unfold lengthOfSet, simp,
    },
    have otherClaim : projection X = projection (X.erase (~□ϕ)), {
      ext1 phi,
      rw proj, rw proj,
      simp,
    },
    { calc lengthOfSet (insert (~ϕ) (projection X))
         ≤ lengthOfSet (projection X) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... = lengthOfSet (projection X) + 1 + lengthOf ϕ : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ : by { simp, }
     ... = lengthOfSet (projection X) + lengthOf (~□ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet (projection (X.erase (~□ϕ))) + lengthOf (~□ϕ) : by { rw otherClaim, }
     ... ≤ lengthOfSet (X.erase (~□ϕ)) + lengthOf (~□ϕ) : by { simp, apply projection_set_length_leq, }
     ... = lengthOfSet X : lengthRemove X (~□ϕ) in_X,
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
