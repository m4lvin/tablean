-- COMPLETENESS

import syntax
import tableau
import soundness
import modelgraphs


-- Definition 20, page 34 -- TODO

-- each individual rule is sound "upwards"
-- i.e.: if B is not satisfiable,
--       then there is a rule such that all the child nodes are not satisfiable.
lemma tableauCompleteness {α : finset formula} { B : finset (finset formula) } :
  ¬ setSatisfiable α → (∃ r : rule α B, (∀ β ∈ B, ¬ setSatisfiable β)) :=
begin
  contrapose,
  intro hyp,
  simp at *,
  --- but where should we get a rule from now???
  sorry,
end

-- Each rule is "complete", i.e. preserves satisfiability "upwards"
-- Fixme: only holds for LOCAL rules, not for the modal atm rule!
lemma ruleCompleteness {α : finset formula} { B : finset (finset formula) } :
  rule α B → (∃ β ∈ B, setSatisfiable β) → setSatisfiable α :=
begin
  intro r,
  cases r,
  case rule.bot {
    simp,
  },
  case rule.not {
    simp,
  },
  case rule.neg : a f notnotf_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩,
    unfold setSatisfiable at *,
    simp at b_sat,
    rcases b_sat with ⟨ H, W, M, w, w_sat_b ⟩,
    use W, use M, use w,
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
  case rule.con : a f g fandg_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩,
    unfold setSatisfiable at *,
    rcases b_sat with ⟨ b_def, W, M, w, w_sat_b ⟩,
    use W, use M, use w,
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
  case rule.nCo : a f g not_fandg_in_a {
    intro hyp,
    rcases hyp with ⟨ b, b_sat ⟩ ,
    unfold setSatisfiable at *,
    rcases b_sat with ⟨ b_def, W, M, w, w_sat_b ⟩,
    use W, use M, use w,
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
  case rule.atm : X f notboxf_in_X {
    intro hyp,
    cases hyp with b H,
    dsimp at H,
    have projection_is_sat : setSatisfiable (projection X ∪ {~f}), {
      unfold setSatisfiable at *,
      cases H with b_def b_sat,
      sorry,
    },
    -- how to show that X is satisfiable?
    -- there might be contradictory stuff not affecting the projection
    -- is it enough to only allow atm when not other rule is applicable?
    -- needs to be added above!!
    -- still, what about other negated boxes?
    -- Example: X = { ~[]p, []p, ~[]q, []~q }
    -- then projection X = { p, ~q }
    -- and the rule application to ~[]p leads to closed,
    -- but the rule application to ~[]q does not!?!?!?!
    -- see page 17 of Borzechowski
    have X_is_simple : simple X, {
      -- this needs that no other rule can be applied!
      sorry,
    },
    rw Lemma1_simple_sat_iff_all_projections_sat X_is_simple,
    split,
    { -- to show that X_is_not_closed : ¬ closed X,
      sorry,
    },
    { -- to show that for all R, (projection X ∪ {~R}) is satisfiable,
      sorry,
    },
    },
end

-- do we need this?
lemma cons_then_open : ∀ X, consistent X → openTableau X :=
begin
  intros X X_cons,
  unfold consistent at *,
  unfold inconsistent at *,
  sorry,
end

lemma notSatThenTableau : ∀ X, ¬ setSatisfiable X → closedTableau X :=
begin
  intro X,
  intro not_sat_X,
  unfold setSatisfiable at *,
  simp at *,
  sorry,
  -- induction tabl_X with a B f f_in_a rule_a_B children IH,
end

-- Theorem 4, page 37
theorem completeness : ∀ X, consistent X ↔ setSatisfiable X :=
begin
  intro X,
  split,
  {
    sorry,
  },
  {
    exact correctness X,
  },
end

lemma formCompleteness : ∀ φ, consistent {φ} ↔ satisfiable φ :=
begin
  intro f,
  split,
  {
    intro cons_f,
    rw completeness at cons_f,
    unfold satisfiable,
    unfold setSatisfiable at *,
    rcases cons_f with ⟨W, M, w, sat_f⟩,
    use W, use M, use w,
    specialize sat_f f,
    finish,
  },
  {
    intro sat_f,
    have setSat : setSatisfiable {f}, {
      unfold satisfiable at *,
      unfold setSatisfiable at *,
      rcases sat_f with ⟨W, M, w, sat_f⟩,
      use W, use M, use w,
      simp,
      exact sat_f,
    },
    rw ← completeness at setSat,
    exact setSat,
  },
end
