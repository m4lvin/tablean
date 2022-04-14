-- COMPLETENESS

import syntax
import tableau
import soundness
import modelgraphs


-- Definition 20, page 34 -- TODO

-- Each rule is "complete", i.e. preserves satisfiability "upwards"
-- Fixme: only holds for LOCAL rules, not for the modal atm rule!
lemma ruleCompleteness {α : finset formula} { B : finset (finset formula) } :
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

-- build a modelgraph world from a local Tableau, if possible
-- TODO: lemma or add here that "consistent X → some" ?
def worldBuilder : (Σ X, localTableau X) → option (finset formula)
| ⟨X, localTableau.byLocalRule (localRule.bot _) _⟩ := none -- closed
| ⟨X, localTableau.byLocalRule (localRule.not _) _⟩ := none -- closed
| ⟨X, @localTableau.byLocalRule _ B lr@(@localRule.neg _ ϕ notnotPhi_in_X) next⟩ :=
begin
  set Y := X \ {~~ϕ} ∪ {ϕ},
  have fo := next Y (by { simp, }),
  exact (
     have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength (@localRule.neg X ϕ notnotPhi_in_X) Y (by {simp,ext1,simp,tauto,}),
     worldBuilder ⟨Y, fo⟩),
end
| ⟨X, @localTableau.byLocalRule _ B (@localRule.con _ ϕ ψ pnp_in_X) next⟩ :=
begin
  set Y := X \ {ϕ⋏ψ} ∪ {ϕ, ψ},
  have ltY := next Y (by { simp, }),
  exact (
    have lengthOfSet Y < lengthOfSet X :=
      localRulesDecreaseLength (localRule.con pnp_in_X) Y (by {simp,ext1,simp,tauto,}),
    worldBuilder ⟨Y, ltY⟩),
end
| ⟨X, localTableau.byLocalRule (@localRule.nCo _ ϕ ψ nCon_in_X) next⟩ :=
begin
  set Y1 := X \ {~(ϕ⋏ψ)} ∪ {~ϕ},
  set Y2 := X \ {~(ϕ⋏ψ)} ∪ {~ψ},
  have ltY1 := next Y1 (by { simp, }),
  have ltY2 := next Y2 (by { simp, }),
  let optWorld1 :=
    have lengthOfSet Y1 < lengthOfSet X :=
      localRulesDecreaseLength (localRule.nCo nCon_in_X) Y1 (by {simp,left,ext1,finish,}),
    worldBuilder ⟨Y1, ltY1⟩,
  let optWorld2 :=
    have lengthOfSet Y2 < lengthOfSet X :=
      localRulesDecreaseLength (localRule.nCo nCon_in_X) Y2 (by {simp,right,ext1,finish,}),
    worldBuilder ⟨Y2, ltY2⟩,
  -- choose the first world if there is one, otherwise the second result:
  exact optWorld1.elim optWorld2 some,
end
| ⟨X, localTableau.sim simpleX⟩ := some X

-- build a model from a tableau, if possible
def modelBuilder : (Σ X, tableau X) → option Σ W, (kripkeModel W × W)
| ⟨X, tableau.loc ltX next⟩ :=
begin
  set optW := worldBuilder ⟨X,ltX⟩,
  refine dite optW.is_some _ (λ _, none),
  intro w_is_some,
  let w := option.get  w_is_some ,
  apply some,
  let ends := (endNodesOf ⟨X, ltX⟩),
  let nextModels : endNodesOf ⟨X, ltX⟩ → option Σ W, (kripkeModel W × W) := by {
    rintro ⟨Y, YinEnds⟩,
    sorry,
    -- exact (modelBuilder ⟨Y, next Y YinEnds⟩), -- well-foundedness problem!
  },
  split,
  -- apply combinedModel nextModels, -- "option" in the way!?

  -- different idea needed here!
  -- NOPE: using combinedModel will not give us a modelgraph :-(
  -- we should avoid () unit type worlds, but need finsets of formulas!
  split,
  rotate,
  -- TODO: define the set of worlds, for now singleton:
  use ({w} : finset (finset formula)), -- TODO: also use nextWorlds here!
  split,
  -- define valuation:
  -- show_term { rintro ⟨v,_⟩ ch, exact (·ch) ∈ v,},
  -- exact λ v_in_w ch, subtype.cases_on v_in_w (λ v _, (·ch) ∈ v),
  -- relation: -- empty?
  { intros v1 v2, exact false, },
  sorry, -- still need actual world here? why does "w" not work?
end
| ⟨X, tableau.atm notBoxPhi_in_X simpleX tproj⟩ := some (by { sorry })
| ⟨X, tableau.opn simpleX noDiamonds⟩ := some (by { sorry })


-- Theorem 3, page 36
-- later TODO: add "normal Z0" constraint
theorem model_existence { Z0 : finset formula } :
  consistent Z0 → ∃ W (μ : modelGraph W) (S ∈ W), Z0 ⊆ S :=
begin
  intro cons_Z0,
  -- unfold consistent at *,
  -- unfold inconsistent at *,
  -- push_neg at cons_Z0,
  set N := lengthOfSet Z0,
  -- TODO: it would be much nicer if existsTableauFor were a function / data
  have existsLT := existsLocalTableauFor N Z0 (by {refl, }),
  cases existsLT with T _,

  let endNodes := endNodesOf ⟨Z0,T⟩,

  --specialize cons_Z0 T,
  -- TODO: given the non-closed (= open) tableau T, build the modelGraph ...

  induction T, -- is this a good idea??

  case byLocalRule : X YS lr next IH {
    -- need to build a model that satisfies X

    have foo := ruleCompleteness lr,
simp at foo,

    sorry,
  },
  case sim : X X_is_simple {
    unfold consistent at *,
    unfold inconsistent at *,
    simp at *,
    -- have foo := Lemma1_simple_sat_iff_all_projections_sat X_is_simple, -- useful ??
    sorry,
  },
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
