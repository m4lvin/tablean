-- TABLEAU

import syntax
import semantics
import data.finset.basic
import data.finset.pimage
import algebra.big_operators.order
import tactic
import order.well_founded_set

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
inductive localRule : finset formula → finset (finset formula) → Type
-- closing rules:
| bot { X     } ( h : ⊥          ∈ X ) : localRule X ∅
| not { X ϕ   } ( h : ϕ ∈ X ∧ ~ϕ ∈ X ) : localRule X ∅
-- simple localRules:
| neg { X ϕ   } ( h : ~~ϕ        ∈ X ) : localRule X { (X \ {~~ϕ}) ∪ { ϕ }    }
| con { X ϕ ψ } ( h : ϕ ⋏ ψ      ∈ X ) : localRule X { (X \ {ϕ ⋏ ψ}) ∪ { ϕ, ψ } }
-- splitting localRule:
| nCo { X ϕ ψ } ( h : ~(ϕ ⋏ ψ)   ∈ X ) : localRule X { X \ { ~ (ϕ ⋏ ψ) } ∪ {~ϕ}
                                                     , X \ { ~ (ϕ ⋏ ψ) } ∪ {~ψ} }

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
      use { (X \ {~~ψ}) ∪ { ψ } },
      use localRule.neg ϕ_in_X,
    },
    case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ1}, X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ2} },
      use localRule.nCo ϕ_in_X,
    },
    case box: { unfold simpleForm at *, tauto, },
  },
  case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { (X \ {ψ1 ⋏ ψ2}) ∪ { ψ1, ψ2 } },
      use localRule.con ϕ_in_X,
  },
  case box: { tauto, },
end


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

@[simp]
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

@[simp]
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

@[simp]
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
   ... ≤ lengthOfFormula f + (projection S).sum lengthOfFormula : by { simp only [add_le_add_iff_right, projection_length_leq], }
   ... ≤ lengthOfFormula f + S.sum lengthOfFormula : by { simp, apply IH, },
  },
},
end

open hasLength

lemma rulesDecreaseLength { X : finset formula } { B : finset (finset formula) } (r : localRule X B) :
  ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
begin
  cases r,
  all_goals { intros β inB, simp at *, },
  case bot : {
    cases inB, -- no premises
  },
  case not : {
    cases inB, -- no premises
  },
  case neg : X ϕ notnot_in_X {
    subst inB,
    { calc lengthOfSet (insert ϕ (X.erase (~~ϕ)))
         ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) : by { apply lengthOf_insert_leq_plus, }
     ... < lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) + 2 : by { simp, }
     ... = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~~ϕ) notnot_in_X,
    },
  },
  case con : X ϕ ψ in_X {
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
  case nCo : X ϕ ψ in_X {
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
  -- TODO: separate proof that the modal rule decreases length!
  /-
  case atm : X ϕ in_X {
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
  -/
end

-- Definition 8, page 14 (note: noLoc means this can be an open tableau, but has to be maximal)
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau from X
-- alternative IDEA: inductive localTableau : finset formula → finset (finset formula) → Type
--                   to say "from X to these diamond leafs"?
inductive localTableau : finset formula → Type
| byLocalRule { X B } (_ : localRule X B) (next : Π Y ∈ B, localTableau Y) : localTableau X
| sim { X } : simple X → localTableau X

open localTableau
open localRule

-- needed for endNodesOf
instance localTableau_has_sizeof : has_sizeof (Σ X, localTableau X) := ⟨ λ ⟨X, T⟩, lengthOfSet X ⟩

-- open end nodes of a given localTableau
def endNodesOf : (Σ X, localTableau X) → finset (finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ :=
  B.bUnion (λ (Y : finset formula), dite (Y ∈ B)
    (λ (h : Y ∈ B),
      have hyp : Y.sum lengthOfFormula < X.sum lengthOfFormula, by { apply rulesDecreaseLength lr, tauto, },
      endNodesOf ⟨Y, next Y h⟩ )
    (λ (h : Y ∉ B), ∅))
| ⟨X, sim _              ⟩ := { X }

-- mwah, should be the same as having no open end nodes!
inductive isClosedLocalTableau : Π { X : finset formula }, localTableau X -> Prop
| byLocalRule { X } { B } (r : localRule X B) (prev : Π Y ∈ B, localTableau Y) :
    (∀ Y, Π H : Y ∈ B, isClosedLocalTableau (prev Y H)) → isClosedLocalTableau (localTableau.byLocalRule r prev)


inductive tableau : finset formula → Type
| loc {X} : (localTableau X) → tableau X
| atm {X ϕ} (h : ~□ϕ ∈ X) : simple X → localTableau (projection X ∪ {~ϕ}) → tableau X -- NEW: must be simple!
| openTab { X } : (¬ ∃ B (_ : localRule X B), true) → (¬∃ ϕ, ~□ϕ ∈ X) → tableau X -- no more moves ;-)

-- approaches how to represent closed tableau:
-- - inductive Prop and then subtype <<<<< currently using this.
-- - inductive Type, then write conversion functions?
--   inductive closedTableau : finset formula → Type -- might not be possible to do ∀ α :-(
-- Definition 16, page 29
inductive closedTableau : Π ( X : finset formula ), Type
| loc { X } (lt : localTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ∀ ty : tableau Y, closedTableau X) → closedTableau X
| atm { X ϕ } (h : ~□ϕ ∈ X) (s : simple X) (lt : localTableau (projection X ∪ {~ϕ})) : closedTableau X


-- is this useful/needed?
@[simp]
def complexityOfTableau : (Σ (X : finset formula) , tableau X) → ℕ
| (⟨X,_⟩) := complexityOfSet X

inductive provable : formula → Prop
| byTableau {φ : formula} : closedTableau { ~ φ } → provable φ

-- Definition 17, page 30
def inconsistent : finset formula → Prop
| X := nonempty (closedTableau X)

def consistent : finset formula → Prop
| X := ¬ inconsistent X



-- maybe this should be data and not Prop ? // → tableau α
def existsTableauFor : ∀ N α, N = lengthOf α → ∃ _ : localTableau α, true :=
begin
  intro N,
  apply nat.strong_induction_on N, -- TODO: only works in Prop?
  intros n IH α nDef,
  have canApplyRule := em (¬ ∃ B (_ : localRule α B), true),
  cases canApplyRule,
  {
    split,
    apply localTableau.sim,
    by_contradiction hyp,
    have fop := notSimpleThenLocalRule hyp,
    tauto,
    tauto,
  },
  {
    simp at canApplyRule,
    cases canApplyRule with B r_exists,
    cases r_exists with r _hyp,
    cases r,
    case bot : _ h {
      have t := (localTableau.byLocalRule (localRule.bot h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case not : _ _ h {
      have t := (localTableau.byLocalRule (not h)) _, use t,
      intro beta, intro beta_in_empty, tauto,
    },
    case neg : _ f h {
      have t := (localTableau.byLocalRule (neg h)) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (neg h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case con : _ f g h {
      have t := localTableau.byLocalRule (con h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (con h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    case nCo : _ f g h {
      have t := localTableau.byLocalRule (nCo h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (nCo h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    /-
    case atm : _ _ h {
      have t := tableau.byRule (atm h) _, use t,
      intros beta beta_def,
      have rDec := rulesDecreaseLength (rule.atm h) beta beta_def,
      subst nDef,
      specialize IH (lengthOf beta) rDec beta,
      simp at IH,
      choose t _true using IH,
      use t,
    },
    -/
  }
end
