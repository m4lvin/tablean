-- COMPLETENESS

import syntax
import tableau
import soundness
import modelgraphs

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

lemma almostCompleteness : Π n X, lengthOfSet X = n → consistent X → setSatisfiable X :=
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

-- Theorem 4, page 37
theorem completeness : ∀ X, consistent X ↔ setSatisfiable X :=
begin
  intro X,
  split,
  { intro X_is_consistent,
    let n := lengthOfSet X,
    apply almostCompleteness n X (by refl) X_is_consistent,
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
