-- SOUNDNESS

import syntax
import tableau

open classical
local attribute [instance, priority 10] prop_decidable

-- Combine a collection of pointed models with one new world using the given valuation.
-- TODO: rewrite to term mode?
def combinedModel { β : Type } (collection : β → Σ (W : Type), kripkeModel W × W) (newVal : char → Prop) :
  kripkeModel (sum unit Σ k : β, (collection k).fst) × (sum unit Σ k : β, (collection k).fst) :=
begin
  split,
  split,
  { -- making the valuation function:
    intro world,
    cases world,
    { -- the one new world:
      cases world,
      exact newVal, -- use new given valuation here!!
    },
    { -- world in one of the given models:
      cases world with R w,
      exact (collection R).snd.fst.val w,
    }
  },
  { -- defining relations:
    intros worldOne worldTwo,
    cases worldOne; cases worldTwo,
    -- four cases about two new or old worlds:
    { exact false, }, -- no reflexive loop at the new world.
    { exact (worldTwo.snd == (collection worldTwo.fst).snd.snd), }, -- conect new world to given points.
    { exact false }, -- no connection from models to new world
    { -- connect two old worlds iff they are from the same model and were connected there already:
      cases worldOne with kOne wOne,
      cases worldTwo with kTwo wTwo,
      have help : kOne = kTwo → Prop, {
        intro same,
        have sameCol : (collection kOne = collection kTwo), {
          rw ← same,
        },
        rw ← sameCol at wTwo,
        exact (collection kOne).snd.fst.rel wOne wTwo,
      },
      exact dite (kOne = kTwo)
        (λ same, help same)
        (λ _, false)
    },
  },
  { -- point at the new world:
    left,
    exact (),
  }
end

-- The combined model preserves all truths at the old worlds.
lemma combMo_preserves_truth_at_oldWOrld { β : Type }
  (collection : β → Σ (W : Type), kripkeModel W × W) (newVal : char → Prop)
  : (∀ (f : formula) (R : β) (oldWorld : (collection R).fst),
    evaluate ((combinedModel collection newVal).fst, (sum.inr ⟨R, oldWorld⟩)) f ↔ evaluate ((collection R).snd.fst, oldWorld) f) :=
begin
  intro f,
  induction f ; intros R oldWorld,
  case bottom : {
    finish,
  },
  case atom_prop : c {
    unfold combinedModel,
    unfold evaluate,
  },
  case neg : f f_IH {
    unfold evaluate,
    rw f_IH R oldWorld,
  },
  case and : f g f_IH g_IH {
    unfold evaluate,
    rw f_IH R oldWorld,
    rw g_IH R oldWorld,
  },
  case box : f f_IH {
    unfold evaluate,
    split,
    {
      intro true_in_combo,
      intros otherWorld rel_in_old_model,
      specialize f_IH R otherWorld,
      rw ← f_IH,
      specialize true_in_combo (sum.inr ⟨R, otherWorld⟩),
      apply true_in_combo,
      unfold combinedModel,
      simp,
      exact rel_in_old_model,
    },
    {
      intro true_in_old,
      simp,
      split,
      {
        intro newWorld,
        unfold combinedModel,
        tauto, -- the new world is never reachable, trivial case
      },
      {
        intros otherR otherWorld,
        intro rel_in_new_model,
        specialize f_IH otherR otherWorld,
        unfold combinedModel at rel_in_new_model,
        have sameR : R = otherR, {
          by_contradiction,
          classical,
          finish,
        },
        subst sameR,
        rw f_IH,
        apply true_in_old,
        -- remains to show that related in old model
        simp at *,
        exact rel_in_new_model,
      },
    },
  },
end

-- The combined model for X satisfies X.
lemma combMo_sat_X { X : finset formula } { β : set formula } { beta_def : β = { R : formula | ~R.box ∈ X } }
  (simple_X : simple X)
  (not_closed_X : ¬ closed X)
  (collection : β → Σ (W : Type), kripkeModel W × W)
  (all_pro_sat : ∀ R : β, ∀ f ∈ projection X ∪ {~R}, evaluate ((collection R).snd.fst, (collection R).snd.snd) f)
  : (∀ f ∈ X, evaluate ((combinedModel collection (λ c, (formula.atom_prop c ∈ X))).fst, (combinedModel collection (λ c, (formula.atom_prop c ∈ X))).snd) f) :=
begin
  intros f f_in_X,
  cases f, -- no induction because X is simple
  case formula.bottom: {
    unfold closed at not_closed_X,
    tauto,
  },
  case atom_prop: {
    unfold combinedModel,
    unfold evaluate,
    simp,
    exact f_in_X,
  },
  case neg: {
    -- subcases :-/
    cases f,
    case atom_prop: {
      unfold combinedModel,
      unfold evaluate,
      unfold closed at not_closed_X,
      rw not_or_distrib at not_closed_X,
      simp at *,
      tauto,
    },
    case box: newf {
      -- set coMo := ,
      --unfold combinedModel,
      change (evaluate ((combinedModel collection (λ c, (·c) ∈ X)).fst, (combinedModel collection (λ (c : char), (·c) ∈ X)).snd) (~□newf)),
      unfold evaluate,
      rw not_forall,
      -- need a reachable world where newf holds, choose the witness
      let h : newf ∈ β, {
        rw beta_def,
        use f_in_X,
      },
      let oldWorld : unit ⊕ Σ (k : β), (collection k).fst :=
        sum.inr ⟨⟨newf, h⟩, (collection ⟨newf, h⟩).snd.snd⟩,
      use oldWorld,
      simp,
      split,
      { -- show that worlds are related in combined model (def above, case 2)
        unfold combinedModel, simp,
      },
      { -- show that f is false at old world
        have coMoLemma := combMo_preserves_truth_at_oldWOrld collection (λ (c : char), (·c) ∈ X) newf ⟨newf, h⟩ (collection ⟨newf, h⟩).snd.snd,
        rw coMoLemma,
        specialize all_pro_sat ⟨newf, h⟩ (~newf),
        unfold evaluate at all_pro_sat,
        simp at *,
        exact all_pro_sat,
      },
    },
    case bottom: {
      tauto,
    },
    all_goals {
      unfold simple at simple_X,
      by_contradiction,
      exact simple_X _ f_in_X,
    },
  },
  case and: fa fb {
    unfold simple at simple_X,
    by_contradiction,
    exact simple_X (fa ⋏ fb) f_in_X,
  },
  case box: f {
    unfold evaluate,
    intros otherWorld is_rel,
    cases otherWorld,
    { cases is_rel, }, -- otherWorld cannot be the (unreachable) new world
    have coMoLemma := combMo_preserves_truth_at_oldWOrld collection (λ c, (·c) ∈ X) f otherWorld.fst otherWorld.snd,
    simp at coMoLemma,
    rw coMoLemma,
    specialize all_pro_sat otherWorld.fst f,
    simp at all_pro_sat,
    rw or_imp_distrib at all_pro_sat,
    cases all_pro_sat with _ all_pro_sat_right,
    rw ← proj at f_in_X,
    specialize all_pro_sat_right f_in_X,
    have sameWorld : otherWorld.snd = (collection otherWorld.fst).snd.snd, {
      rw (heq_iff_eq.mp (heq.symm is_rel)),
    },
    rw sameWorld,
    simp,
    exact all_pro_sat_right,
  },
end

-- Lemma 1 (page 16)
-- A simple set of formulas X is satisfiable if and only if
-- it is not closed  and  for all ¬[A]R ∈ X also XA; ¬R is satisfiable.
lemma Lemma1_simple_sat_iff_all_projections_sat { X : finset formula } :
  simple X → (setSatisfiable X ↔ (¬ closed X ∧ ∀ R, (~□R) ∈ X → setSatisfiable (projection X ∪ {~R}))) :=
begin
  intro X_is_simple,
  split,
  { -- left to right
    intro sat_X,
    unfold setSatisfiable at *,
    rcases sat_X with ⟨ W, M, w, w_sat_X ⟩,
    split,
    { -- show that X is not closed:
      by_contradiction hyp,
      unfold closed at hyp,
      cases hyp with bot_in_X f_and_notf_in_X,
      {
        exact w_sat_X ⊥ bot_in_X,
      },
      {
        rcases f_and_notf_in_X with ⟨ f, f_in_X, notf_in_X ⟩,
        let w_sat_f :=  w_sat_X f f_in_X,
        let w_sat_notf :=  w_sat_X (~f) notf_in_X,
        unfold evaluate at *,
        exact absurd w_sat_f w_sat_notf,
      }
    },
    { -- show that for each ~[]R ∈ X the projection with ~R is satisfiable:
      intros R notboxr_in_X,
      let w_sat_notboxr := w_sat_X (~□R) notboxr_in_X,
      unfold evaluate at w_sat_notboxr,
      simp at w_sat_notboxr,
      rcases w_sat_notboxr with ⟨ v, w_rel_v, v_sat_notr ⟩,
      use [W, M, v],
      intro g,
      simp at *,
      rw or_imp_distrib,
      split,
      {
        intro g_is_notR,
        rw g_is_notR,
        exact v_sat_notr,
      },
      {
        intro boxg_in_X,
        rw proj at boxg_in_X,
        specialize w_sat_X (□g) boxg_in_X,
        unfold evaluate at w_sat_X,
        exact w_sat_X v w_rel_v,
      },
    },
  },
  { -- right to left
    intro rhs,
    cases rhs with not_closed_X all_pro_sat,
    unfold setSatisfiable at all_pro_sat,
    unfold setSatisfiable,
    -- Let's build a new Kripke model!
    let β := { R : formula | ~□R ∈ X },
    -- beware, using Axioms of Choice here!
    choose typeFor this_pro_sat using all_pro_sat,
    choose modelFor this_pro_sat using this_pro_sat,
    choose worldFor this_pro_sat using this_pro_sat,
    -- define the collection:
    let collection : β → (Σ (W : Type), (kripkeModel W × W)) := begin
      intro k,
      cases k with R notboxr_in_X,
      simp at notboxr_in_X,
      use [typeFor R notboxr_in_X, modelFor R notboxr_in_X, worldFor R notboxr_in_X],
    end,
    let newVal := λ c, formula.atom_prop c ∈ X,
    let BigM := combinedModel collection newVal,
    use unit ⊕ Σ k : β, (collection k).fst,
    use [BigM.fst, BigM.snd],
    -- apply Lemma, missing last argument "all_pro_sat"
    -- we need to use that X_is_simple (to restrict cases what phi can be)
    -- and that X is not closed (to ensure that it is locally consistent)
    apply combMo_sat_X X_is_simple not_closed_X collection,
    -- it remains to show that the new big model satisfies X
    intros R f f_inpro_or_notr,
    cases R with R notrbox_in_X,
    simp only [finset.mem_union, finset.mem_insert, finset.mem_singleton, subtype.coe_mk] at *,
    specialize this_pro_sat R notrbox_in_X,
    cases f_inpro_or_notr with f_inpro f_is_notboxR,
    { -- if f is in the projection
      specialize this_pro_sat f,
      rw or_imp_distrib at this_pro_sat,
      cases this_pro_sat with this_pro_sat_l  this_pro_sat_r,
      exact this_pro_sat_l f_inpro,
    },
    { -- case where f is ~[]R
      cases f_is_notboxR,
      specialize this_pro_sat (~R),
      rw or_imp_distrib at this_pro_sat,
      cases this_pro_sat with this_pro_sat_l  this_pro_sat_r,
      exact this_pro_sat_r f_is_notboxR,
    },
    simp, -- to check β
  },
end

-- Each rule is sound and preserves satisfiability "downwards"
lemma localRuleSoundness {α : finset formula} { B : finset (finset formula) } :
  localRule α B → (setSatisfiable α → ∃ β ∈ B, setSatisfiable β) :=
begin
  intro r,
  intro a_sat,
  unfold setSatisfiable at a_sat,
  rcases a_sat with ⟨ W, M, w, w_sat_a ⟩,
  cases r,
  case localRule.bot : a bot_in_a {
    by_contradiction,
    let w_sat_bot := w_sat_a ⊥ bot_in_a  ,
    unfold evaluate at w_sat_bot,
    exact w_sat_bot,
  },
  case localRule.not : a f hyp {
    by_contradiction,
    have w_sat_f : evaluate (M, w) f , {
      apply w_sat_a,
      exact hyp.left,
    },
    have w_sat_not_f : evaluate (M, w) (~f) , {
      apply w_sat_a (~f),
      exact hyp.right,
    },
    unfold evaluate at *,
    exact absurd w_sat_f w_sat_not_f,
  },
  case localRule.neg : a f hyp {
    have w_sat_f : evaluate (M, w) f, {
      specialize w_sat_a (~~f) hyp,
      unfold evaluate at *,
      finish,
    },
    use (a \ {~~f} ∪ {f}),
    simp only [true_and, eq_self_iff_true, sdiff_singleton_is_erase, multiset.mem_singleton, finset.mem_mk],
    unfold setSatisfiable,
    use [W, M, w],
    intro g,
    simp only [ne.def, union_singleton_is_insert, finset.mem_insert, finset.mem_erase],
    rw or_imp_distrib,
    split,
    {
      intro g_is_f, rw g_is_f, apply w_sat_f,
    },
    {
      rw and_imp,
      intros g_neq_notnotf g_in_a,
      apply w_sat_a,
      exact g_in_a,
    },
  },
  case localRule.con : a f g hyp {
    use ( (a \ {f ⋏ g}) ∪ { f, g } ),
    split,
    simp,
    unfold setSatisfiable,
    use [W, M, w],
    simp only [and_imp, forall_eq_or_imp, sdiff_singleton_is_erase, ne.def, finset.union_insert, finset.mem_insert, finset.mem_erase],
    split,
    { -- f
      specialize w_sat_a (f⋏g) hyp,
      unfold evaluate at *,
      exact w_sat_a.left,
    },
    {
      intros h hhyp,
      simp at hhyp,
      cases hhyp,
      { -- h = g
        specialize w_sat_a (f⋏g) hyp,
        unfold evaluate at *,
        rw hhyp,
        exact w_sat_a.right,
      },
      { -- h in a
        exact w_sat_a h hhyp.right,
      },
    },
  },
  case localRule.nCo : a f g notfandg_in_a {
    unfold setSatisfiable,
    simp,
    let w_sat_phi := w_sat_a (~(f⋏g)) notfandg_in_a,
    unfold evaluate at w_sat_phi,
    rw not_and_distrib at w_sat_phi,
    cases w_sat_phi with not_w_f not_w_g,
    { use (a \ { ~ (f ⋏ g) } ∪ {~f}),
      split,
      { simp at *, },
      { use [W, M, w],
        intro psi,
        simp,
        intro psi_def,
        cases psi_def,
        { rw psi_def,
          unfold evaluate,
          exact not_w_f,
        },
        { cases psi_def with psi_in_a,
          exact w_sat_a psi psi_def_right,
        },
      },
    },
    { use (a \ { ~ (f ⋏ g) } ∪ {~g}),
      split,
      { simp at *, },
      { use [W, M, w],
        intro psi,
        simp,
        intro psi_def,
        cases psi_def,
        { rw psi_def,
          unfold evaluate,
          exact not_w_g,
        },
        { cases psi_def with psi_in_a,
          exact w_sat_a psi psi_def_right,
        },
      },
    },
  },
end

-- The critical roule is sound and preserves satisfiability "downwards".
-- TODO: is this the same as (one of the directions of) Lemma 1 ??
lemma atmSoundness {α : finset formula} {f} (not_box_f_in_a : ~□f ∈ α) :
  simple α → setSatisfiable α → setSatisfiable (projection α ∪ {~f}) :=
begin
  intro s,
  intro aSat,
  unfold setSatisfiable at aSat,
  rcases aSat with ⟨W, M, w, w_sat_a⟩,
  split,
  simp,
  -- get the other reachable world:
  let w_sat_not_box_f := w_sat_a (~f.box) not_box_f_in_a,
  unfold evaluate at w_sat_not_box_f,
  simp at w_sat_not_box_f,
  rcases w_sat_not_box_f with ⟨ v,  w_rel_v, v_not_sat_f ⟩,
  -- show that the projection is satisfiable:
  use [M, v],
  split,
  { unfold evaluate,
    exact v_not_sat_f,
  },
  intros phi phi_in_proj,
  rw proj at phi_in_proj,
  {
    specialize w_sat_a phi.box _,
    exact phi_in_proj,
    unfold evaluate at w_sat_a,
    exact w_sat_a v w_rel_v,
  },
end

lemma localTableauAndEndNodesUnsatThenNOtSat {Z} (ltZ : localTableau Z) :
  (Π (Y), Y ∈ endNodesOf ⟨Z, ltZ⟩ → ¬ setSatisfiable Y) → ¬setSatisfiable Z :=
begin
  intro endsOfXnotSat,
  induction ltZ,
  case byLocalRule : X YS lr next IH {
    by_contradiction satX,
    rcases localRuleSoundness lr satX with ⟨Y,Y_in_YS,satY⟩,
    specialize IH Y Y_in_YS,
    set ltY := next Y Y_in_YS,
    have endNodesInclusion : ∀ W, W ∈ endNodesOf ⟨Y, ltY⟩ → W ∈ endNodesOf ⟨X, localTableau.byLocalRule lr next⟩ , {
      finish,
    },
    have endsOfYnotSat : (∀ (Y_1 : finset formula), Y_1 ∈ endNodesOf ⟨Y, ltY⟩ → ¬setSatisfiable Y_1), {
      intros W W_is_endOf_Y,
      apply endsOfXnotSat W (endNodesInclusion W W_is_endOf_Y),
    },
    finish,
  },
  case sim : X X_is_simple {
    apply endsOfXnotSat,
    unfold endNodesOf,
    simp,
  },
end

lemma tableauThenNotSat : ∀ X, closedTableau X → ¬ setSatisfiable X :=
begin
  intros X t,
  induction t,
  case loc: Y ltY next IH {
    apply localTableauAndEndNodesUnsatThenNOtSat ltY,
    intros Z ZisEndOfY,
    exact IH Z ZisEndOfY,
  },
  case atm: Y ϕ notBoxPhiInY Y_is_simple ltProYnPhi {
    rw Lemma1_simple_sat_iff_all_projections_sat Y_is_simple,
    simp,
    intro Ynotclosed,
    use ϕ,
    use notBoxPhiInY,
    finish,
  },
end

-- Theorem 2, page 30
theorem correctness : ∀ X, setSatisfiable X → consistent X :=
begin
  intro X,
  contrapose,
  unfold consistent,
  simp,
  unfold inconsistent,
  intro hyp,
  cases hyp with t,
  exact tableauThenNotSat X t,
end

lemma soundTableau : ∀ φ, provable φ → ¬ setSatisfiable {~φ} :=
begin
  intro phi,
  intro prov,
  cases prov with _ tabl,
  apply tableauThenNotSat,
  exact tabl,
end

theorem soundness : ∀ φ, provable φ → tautology φ :=
begin
  intros φ prov,
  apply notsatisfnotThenTaut,
  rw sat_iff_singleton_sat,
  apply soundTableau,
  exact prov,
end
