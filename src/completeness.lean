-- COMPLETENESS

import syntax
import tableau
import soundness
import modelgraphs


-- Definition 20, page 34 -- TODO

-- Each local rule is "complete", i.e. preserves satisfiability "upwards"
lemma localRuleCompleteness {α : finset formula} { B : finset (finset formula) } :
  localRule α B → (∃ β ∈ B, setSatisfiable β) → setSatisfiable α :=
begin
  intro r,
  cases r,
  case localRule.bot {
    simp,
  },
  case localRule.not {
    simp,
  },
  case localRule.neg : a f notnotf_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩,
    unfold setSatisfiable at *,
    simp at b_sat,
    rcases b_sat with ⟨ H, W, M, w, w_sat_b ⟩,
    use [W, M, w],
    intros phi phi_in_a,
    have b_is_af : b = insert f (a \ {~~f}), {
      subst H, ext1, simp,
    },
    have phi_in_b_or_is_f : phi ∈ b ∨ phi = ~~f, {
      rw b_is_af,
      simp,
      finish,
    },
    cases phi_in_b_or_is_f with phi_in_b phi_is_notnotf,
    {
      apply w_sat_b,
      exact phi_in_b,
    },
    {
      rw phi_is_notnotf,
      unfold evaluate at *,
      simp, -- this removes double negation
      apply w_sat_b,
      rw b_is_af ,
      simp at *,
    },
  },
  case localRule.con : a f g fandg_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩,
    unfold setSatisfiable at *,
    rcases b_sat with ⟨ b_def, W, M, w, w_sat_b ⟩,
    use [W, M, w],
    intros phi phi_in_a,
    simp at b_def,
    have b_is_fga : b = insert f (insert g (a \ {f⋏g})), {
      subst b_def, ext1, simp,
    },
    have phi_in_b_or_is_fandg : phi ∈ b ∨ phi = f⋏g, {
      rw b_is_fga,
      simp,
      finish, -- finish,
    },
    cases phi_in_b_or_is_fandg with phi_in_b phi_is_fandg,
    {
      apply w_sat_b,
      exact phi_in_b,
    },
    { rw phi_is_fandg,
      unfold evaluate at *,
      split,
      { apply w_sat_b, rw b_is_fga, simp, },
      { apply w_sat_b, rw b_is_fga, simp, },
    },
  },
  case localRule.nCo : a f g not_fandg_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩ ,
    unfold setSatisfiable at *,
    rcases b_sat with ⟨ b_def, W, M, w, w_sat_b ⟩,
    use [W, M, w],
    intros phi phi_in_a,
    simp at *,
    have phi_in_b_or_is_notfandg : phi ∈ b ∨ phi = ~(f⋏g), {
      cases b_def ; { rw b_def, simp, finish, },
    },
    cases b_def,
    { -- b contains ~f
      cases phi_in_b_or_is_notfandg with phi_in_b phi_def,
      { exact w_sat_b phi phi_in_b, },
      {
        rw phi_def,
        unfold evaluate,
        rw b_def at w_sat_b,
        specialize w_sat_b (~f),
        rw not_and_distrib,
        left,
        unfold evaluate at w_sat_b,
        apply w_sat_b,
        finish,
      },
    },
    { -- b contains ~g
     cases phi_in_b_or_is_notfandg with phi_in_b phi_def,
      { exact w_sat_b phi phi_in_b, },
      {
        rw phi_def,
        unfold evaluate,
        rw b_def at w_sat_b,
        specialize w_sat_b (~g),
        rw not_and_distrib,
        right,
        unfold evaluate at w_sat_b,
        apply w_sat_b,
        finish,
      },
    },
  },
end


-- Lemma 11 (but rephrased to be about local tableau!?)
lemma inconsUpwards {X} {ltX : localTableau X} : (Π en ∈ endNodesOf ⟨X, ltX⟩, inconsistent en) → inconsistent X :=
begin
  intro lhs,
  unfold inconsistent at *,
  let leafTableaus : Π en ∈ endNodesOf ⟨X, ltX⟩, closedTableau en := λ Y YinEnds, (lhs Y YinEnds).some,
  split,
  exact closedTableau.loc ltX leafTableaus,
end

-- Converse of Lemma 11
lemma consToEndNodes {X} {ltX : localTableau X} : consistent X → (∃ en ∈ endNodesOf ⟨X, ltX⟩, consistent en) :=
begin
  intro consX,
  unfold consistent at *,
  have claim := not.imp consX (@inconsUpwards X ltX),
  simp at claim,
  tauto,
end

def projOfConsSimpIsCons : Π {X ϕ}, consistent X → simple X → ~□ϕ ∈ X → consistent (projection X ∪ {~ϕ}) :=
begin
  intros X ϕ consX simpX notBoxPhi_in_X,
  unfold consistent at *,
  unfold inconsistent at *,
  by_contradiction h,
  simp at *,
  cases h with ctProj,
  have ctX : closedTableau X, {
    apply closedTableau.atm notBoxPhi_in_X simpX,
    simp, exact ctProj,
  },
  cases consX, tauto,
end


-- note: removed (notSimpX : ¬ simple X) premise
lemma locTabEndSatThenSat {X Y} (ltX : localTableau X) (Y_endOf_X : Y ∈ endNodesOf ⟨X, ltX⟩) :
  setSatisfiable Y → setSatisfiable X :=
begin
  intro satY,
  induction ltX,
  case byLocalRule : X B lr next IH {
    apply localRuleCompleteness lr,
    cases lr,
    case localRule.bot : W bot_in_W {
      simp at *,
      exact Y_endOf_X,
    },
    case localRule.not : _ ϕ h {
      simp at *,
      exact Y_endOf_X,
    },
    case localRule.neg : Z ϕ notNotPhi_inX {
      simp at *,
      specialize IH (insert ϕ (Z.erase (~~ϕ))),
      simp at IH,
      apply IH,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,
      subst W_def,
      exact Y_endOf_W,
    },
    case localRule.con : Z ϕ ψ _ {
      simp at *,
      specialize IH (insert ϕ (insert ψ (Z.erase (ϕ⋏ψ)))),
      simp at IH,
      apply IH,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,
      subst W_def,
      exact Y_endOf_W,
    },
    case localRule.nCo : Z ϕ ψ _ {
      simp at *,
      rcases Y_endOf_X with ⟨W, W_def, Y_endOf_W⟩,

      cases W_def,
      all_goals { subst W_def, },
      { specialize IH (insert (~ϕ) (Z.erase (~(ϕ⋏ψ)))),
        simp at IH,
        use (insert (~ϕ) (Z.erase (~(ϕ⋏ψ)))),
        split,
        { left, refl, },
        { apply IH, exact Y_endOf_W, }
      },
      { specialize IH (insert (~ψ) (Z.erase (~(ϕ⋏ψ)))),
        simp at IH,
        use (insert (~ψ) (Z.erase (~(ϕ⋏ψ)))),
        split,
        { right, refl, },
        { apply IH, exact Y_endOf_W, }
      },
    },
  },
  case sim : X simpX {
    finish,
  },
end


lemma simpSat : Π n X, lengthOfSet X = n → consistent X → setSatisfiable X :=
begin
  intro n,
  apply nat.strong_induction_on n,
  intros n IH,
  intros X lX_is_n consX,
  refine if simpX : simple X then _ else _,
  -- CASE 1: X is simple
  rw Lemma1_simple_sat_iff_all_projections_sat simpX,
  split,
  { -- show that X is not closed
    by_contradiction h,
    unfold consistent at consX,
    unfold inconsistent at consX,
    simp at consX,
    cases consX, apply consX,
    unfold closed at h,
    refine if botInX : ⊥ ∈ X then _ else _,
    { apply closedTableau.loc, rotate, apply localTableau.byLocalRule,
      exact localRule.bot botInX,
      intros Y YinEmpty, cases YinEmpty,
      rw botNoEndNodes, intros Y YinEmpty, cases YinEmpty,
    },
    { have f1 : ∃ (f : formula) (H : f ∈ X), ~f ∈ X := by tauto,
      have : nonempty (closedTableau X), {
      rcases f1 with ⟨f, f_in_X, notf_in_X⟩,
      fconstructor,
      apply closedTableau.loc, rotate, apply localTableau.byLocalRule,
      apply localRule.not ⟨f_in_X , notf_in_X⟩,
      intros Y YinEmpty, cases YinEmpty,
      rw notNoEndNodes, intros Y YinEmpty, cases YinEmpty,
      },
      exact classical.choice this,
    },
  },
  { -- show that all projections are sat
    intros R notBoxR_in_X,
    apply IH (lengthOfSet (projection X ∪ {~R})),
    { -- projection decreases lengthOfSet
      subst lX_is_n,
      exact atmRuleDecreasesLength notBoxR_in_X,
    },
    { refl, },
    { exact projOfConsSimpIsCons consX simpX notBoxR_in_X, },
  },
  -- CASE 2: X is not simple
  rename simpX notSimpX,
  have foo := notSimpleThenLocalRule notSimpX,
  rcases foo with ⟨B,lr,_⟩,
  have rest : Π (Y : finset formula), Y ∈ B → localTableau Y, {
    intros Y Y_in_B,
    set N := hasLength.lengthOf Y,
    have h := existsLocalTableauFor N Y,
    simp at h,
    exact classical.some h,
  },

  -- local approach seems wrong here!
  -- apply localRuleCompleteness lr,

  rcases @consToEndNodes X (localTableau.byLocalRule lr rest) consX with ⟨E, E_endOf_X, consE⟩,
  have satE : setSatisfiable E, {
    apply IH (lengthOfSet E),
    { -- end Node of local rule is LT
      subst lX_is_n,
      apply endNodesOfLocalRuleLT E_endOf_X,
    },
    { refl, },
    { exact consE, },
  },
  exact locTabEndSatThenSat (localTableau.byLocalRule lr rest) E_endOf_X satE,
end



-- TODO: decidability via tableau, needed for worldBuilder(?)
-- this first needs a lemma about the maximal size / that ther eare only finitely many tableaus for X!
instance cons_dec {X} : decidable (consistent X) := sorry


-- If X is consistent, build a world from a local Tableau for X.
-- TODO: also return that this world satisfies X, or make this a lemma?
def worldBuilder : Π X, consistent X → localTableau X → finset formula
| X consX (localTableau.byLocalRule (localRule.bot bot_in_X) noNexts) :=
begin
  exfalso,
  have claim : nonempty (closedTableau X), {
    fconstructor,
    apply closedTableau.loc (localTableau.byLocalRule (localRule.bot bot_in_X) noNexts),
    rw botNoEndNodes,
    intros Y YinEmpty,
    tauto,
  },
  tauto,
end
| X consx (localTableau.byLocalRule (localRule.not phinotphi_in_X) noNexts) :=
begin
  exfalso,
  have claim : nonempty (closedTableau X), {
    fconstructor,
    apply closedTableau.loc (localTableau.byLocalRule (localRule.not phinotphi_in_X) noNexts),
    rw notNoEndNodes,
    intros Y YinEmpty,
    tauto,
  },
  tauto,
end
| X consX (@localTableau.byLocalRule _ B (@localRule.neg _ ϕ notnotPhi_in_X) next) :=
begin
  set Y := X \ {~~ϕ} ∪ {ϕ},
  have fo := next Y (by { simp, }),
  have consY : consistent Y := sorry,
  exact (
     have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength (@localRule.neg X ϕ notnotPhi_in_X) Y (by {simp,ext1,simp,tauto,}),
     worldBuilder Y consY fo),
end
| X consX (@localTableau.byLocalRule _ B (@localRule.con _ ϕ ψ pnp_in_X) next) :=
begin
  set Y := X \ {ϕ⋏ψ} ∪ {ϕ, ψ},
  have ltY := next Y (by { simp, }),

  have consY : consistent Y := sorry,
  exact (
    have lengthOfSet Y < lengthOfSet X :=
      localRulesDecreaseLength (localRule.con pnp_in_X) Y (by {simp,ext1,simp,tauto,}),
    worldBuilder Y consY ltY),
end
| X consX (localTableau.byLocalRule (@localRule.nCo _ ϕ ψ nCon_in_X) next) :=
begin
  set Y1 := X \ {~(ϕ⋏ψ)} ∪ {~ϕ},
  set Y2 := X \ {~(ϕ⋏ψ)} ∪ {~ψ},
  have ltY1 := next Y1 (by { simp, }),
  have ltY2 := next Y2 (by { simp, }),
  have consYsome : consistent Y1 ∨ consistent Y2 := sorry,
  refine if consY1 : consistent Y1 then _ else _,
  {
  exact (
    have lengthOfSet Y1 < lengthOfSet X :=
      localRulesDecreaseLength (localRule.nCo nCon_in_X) Y1 (by {simp,left,ext1,finish,}),
    worldBuilder Y1 consY1 ltY1),
  },
  {
  have consY2 : consistent Y2 := by {tauto,},
  exact (
    have lengthOfSet Y2 < lengthOfSet X :=
      localRulesDecreaseLength (localRule.nCo nCon_in_X) Y2 (by {simp,right,ext1,finish,}),
    worldBuilder Y2 consY2 ltY2),
  }
end
| X consX (localTableau.sim simpleX) := X
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ ⟨X,_,_⟩, lengthOfSet X)⟩]}
-- using_well_founded {rel_tac := sorry}

-- If X is consistent, build a model from a tableau for X.
-- TODO: add that this model satisfies X, or make it a lemma? OR directly build a modelgraph?
-- TODO: do we need induction on ltX here to avoid non-wellfoundedness?
def modelBuilder : Π X, consistent X → tableau X → Σ W : finset (finset formula), (kripkeModel W × W)
| X consX (tableau.loc ltX next) :=
begin
  set w := worldBuilder X consX ltX,
  let ends := (endNodesOf ⟨X, ltX⟩),
  let nextModels : endNodesOf ⟨X, ltX⟩ → Σ W : finset (finset formula), (kripkeModel W × W) := by {
    rintro ⟨Y, YinEnds⟩,
    have consY := sorry,
    exact (
      have lengthOfSet Y < lengthOfSet X := sorry,  -- well-foundedness problem!
      modelBuilder Y consY (next Y YinEnds)
    ),
  },
  split,
  -- "combinedModel nextModels" is not good here!
  -- NOPE: using combinedModel will not give us a modelgraph :-(
  -- we should avoid () unit type worlds, but need finsets of formulas!
  split,
  split,
  -- define valuation:
  { rintro ⟨v,_⟩ ch, exact (·ch) ∈ v,},
  -- exact λ v_in_w ch, subtype.cases_on v_in_w (λ v _, (·ch) ∈ v),
  -- relation: -- empty?
  { intros v1 v2, exact false, },
  rotate,
  use {w}, -- TODO: the set of worlds, for now singleton which is wrong!
  use w,
  simp,
end
| X consX (tableau.atm notBoxPhi_in_X simpleX tproj) := sorry
| X consX (tableau.opn simpleX noDiamonds) := sorry
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ ⟨X,_⟩, lengthOfSet X)⟩]}


-- use Lemma1_simple_sat_iff_all_projections_sat ??

-- Theorem 3, page 36
-- later TODO: add "normal Z0" constraint
theorem model_existence { Z0 : finset formula } :
  consistent Z0 → ∃ W (μ : modelGraph W) (S ∈ W), Z0 ⊆ S :=
begin
  intro cons_Z0,
  set N := lengthOfSet Z0,
  have existsT := existsTableauFor N Z0 (by {refl, }),
  cases existsT with T _,
  let M := modelBuilder Z0 cons_Z0 T,
  -- BIG TODO: show that modelBuilder gives a modelGraph !!
  simp at *,
  sorry,
end

-- Theorem 4, page 37
theorem completeness : ∀ X, consistent X ↔ setSatisfiable X :=
begin
  intro X,
  split,
  { intro X_is_consistent,
    -- Use Theorem 3:
    rcases model_existence X_is_consistent with ⟨W, μ, S, S_in_W, X_subseteq_S⟩,
    unfold setSatisfiable,
    use W,
    -- use Lemma 9:
    have tL := truthLemma μ,
    rcases μ with ⟨M, _⟩,
    use [M, ⟨S, S_in_W⟩],
    intros ϕ phi_in_X,
    apply tL,
    apply X_subseteq_S,
    exact phi_in_X,
  },
  -- use Theorem 2:
  exact correctness X,
end

lemma singletonCompleteness : ∀ φ, consistent {φ} ↔ satisfiable φ :=
begin
  intro f,
  split,
  {
    intro cons_f,
    rw completeness at cons_f,
    unfold satisfiable,
    unfold setSatisfiable at *,
    rcases cons_f with ⟨W, M, w, sat_f⟩,
    use [W, M, w],
    specialize sat_f f,
    finish,
  },
  {
    intro sat_f,
    have setSat : setSatisfiable {f}, {
      unfold satisfiable at *,
      unfold setSatisfiable at *,
      rcases sat_f with ⟨W, M, w, sat_f⟩,
      use [W, M, w],
      simp,
      exact sat_f,
    },
    rw ← completeness at setSat,
    exact setSat,
  },
end
