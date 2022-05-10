
import syntax
import tableau
import semantics
import soundness
import vocabulary

open hasVocabulary has_sat

def partition := finset formula × finset formula


-- Definition 24
def partInterpolant (X1 X2 : finset formula) (θ : formula) :=
  voc θ ⊆ (voc X1 ∩ voc X2)  ∧  ¬ satisfiable ( X1 ∪ {~θ} )  ∧  ¬ satisfiable ( X2 ∪ {θ} )

-- Lemma 14
lemma botInter {X1 X2} : ⊥ ∈ (X1 ∪ X2) → ∃ θ, partInterpolant X1 X2 θ :=
begin
  intro bot_in_X,
  refine if side : ⊥ ∈ X1 then _ else _,
  { -- case ⊥ ∈ X1
    use ⊥,
    split,
    { unfold voc, unfold vocabOfFormula, simp, },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, specialize sat ⊥, simp at *, tauto, },
  },
  { -- case ⊥ ∈ X2
    have : ⊥ ∈ X2, { simp at *, tauto, },
    use ~⊥,
    split,
    { unfold voc, unfold vocabOfFormula, simp, },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, },
    { specialize sat (~~⊥), simp at *, unfold evaluate at sat, tauto, },
    { specialize sat ⊥, simp at *, tauto, },
  }
end
lemma notInter {X1 X2 ϕ} : ϕ ∈ (X1 ∪ X2) ∧ ~ϕ ∈ (X1 ∪ X2) → ∃ θ, partInterpolant X1 X2 θ :=
begin
  intro in_both, cases in_both with pIn nIn,
  by_cases pSide : ϕ ∈ X1, all_goals { by_cases nSide :~ϕ ∈ X1 }, -- four cases
  { use ⊥, -- both in X1
    split,
    { unfold voc, unfold vocabOfFormula, simp, },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, },
    { have h1 := sat ϕ, have h2 := sat (~ϕ), simp at *, tauto, },
    { specialize sat ⊥, simp at *, tauto, },
  },
  { use ϕ, -- ϕ ∈ X1 and ~ϕ ∈ X2
    split,
    { unfold voc, intros a aIn, simp, split,
      exact vocElem_subs_vocSet pSide aIn,
      have h : ~ϕ ∈ X2 , { finish, },
      have := vocElem_subs_vocSet h,
      simp at *,
      tauto,
    },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, },
    { simp at *, tauto, },
    { have h1 := sat (~ϕ), simp at *, tauto, },
  },
  { use ~ϕ, -- ~ϕ ∈ X1 and ϕ ∈ X2
    split,
    { unfold voc, intros a aIn, simp, split,
      exact vocElem_subs_vocSet nSide aIn,
      have h : ϕ ∈ X2 , { finish, },
      have := vocElem_subs_vocSet h,
      simp at *,
      tauto,
    },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, },
    { have h1 := sat (~ϕ), simp at *, tauto, },
    { simp at *, tauto, },
  },
  { use ~⊥, -- both in X2
    split,
    { unfold voc, unfold vocabOfFormula, simp, },
    split,
    all_goals { by_contradiction h, rcases h with ⟨W,M,w1,sat⟩, },
    { specialize sat (~~⊥), simp at *, unfold evaluate at sat, tauto, },
    { have h1 := sat ϕ, have h2 := sat (~ϕ), simp at *, tauto, },
  },
end

lemma notnotInterpolantX1 {X1 X2 ϕ θ} : (~~ϕ) ∈ X1 → partInterpolant (X1 \ {~~ϕ} ∪ {ϕ}) (X2 \ {~~ϕ}) θ → partInterpolant X1 X2 θ :=
begin
  intros notnotphi_in_X1 theta_is_chInt,
  rcases theta_is_chInt with ⟨vocSub,noSatX1,noSatX2⟩,
  unfold partInterpolant at *,
  simp,
  split,
  { rw vocPreserved X1 (~~ϕ) ϕ notnotphi_in_X1 (by {unfold voc, simp, }),
    change voc θ ⊆ voc (X1 \ {~~ϕ} ∪ {ϕ}) ∩ voc X2,
    have : voc (X2 \ {~~ϕ}) ⊆ voc X2 , { apply vocMonotone, simp, intros a aIn, finish, },
    intros a aInVocTheta,
    simp at *,
    rw finset.subset_inter_iff at vocSub,
    tauto,
  },
  split,
  all_goals { by_contradiction hyp, unfold satisfiable at hyp, rcases hyp with ⟨W,M,w,sat⟩, },
  { have : satisfiable ((X1 \ {~~ϕ} ∪ {ϕ}) ∪ {~θ}), {
      unfold satisfiable,
      use [W,M,w],
      intros ψ psi_in_newX_u_notTheta,
      simp at psi_in_newX_u_notTheta,
      cases psi_in_newX_u_notTheta,
      { apply sat, rw psi_in_newX_u_notTheta, simp at *, },
      cases psi_in_newX_u_notTheta,
      { rw psi_in_newX_u_notTheta, apply of_not_not,
        change evaluate (M, w) (~~ϕ),
        apply sat (~~ϕ), simp, right, assumption,
      },
      { apply sat, simp at *, tauto, },
    },
    tauto,
  },
  { have : satisfiable ( (X2 \ {~~ϕ}) ∪ {θ}), {
      unfold satisfiable at *,
      use [W,M,w],
      intros ψ psi_in_newX2cupTheta,
      apply sat, simp at *, tauto,
    },
    tauto,
  },
end

lemma notnotInterpolantX2 {X1 X2 ϕ θ} : (~~ϕ) ∈ X2 → partInterpolant (X1 \ {~~ϕ}) (X2 \ {~~ϕ} ∪ {ϕ}) θ → partInterpolant X1 X2 θ :=
begin
  intros notnotphi_in_X2 theta_is_chInt,
  rcases theta_is_chInt with ⟨vocSub,noSatX1,noSatX2⟩,
  unfold partInterpolant at *,
  simp,
  split,
  { rw vocPreserved X2 (~~ϕ) ϕ notnotphi_in_X2 (by {unfold voc, simp, }),
    change voc θ ⊆ voc X1 ∩ voc (X2 \ {~~ϕ} ∪ {ϕ}),
    have : voc (X1 \ {~~ϕ}) ⊆ voc X1 , { apply vocMonotone, simp, intros a aIn, finish, },
    intros a aInVocTheta,
    simp at *,
    rw finset.subset_inter_iff at vocSub,
    tauto,
  },
  split,
  all_goals { by_contradiction hyp, unfold satisfiable at hyp, rcases hyp with ⟨W,M,w,sat⟩, },
  { have : satisfiable ((X1 \ {~~ϕ}) ∪ {~θ}), {
      unfold satisfiable,
      use [W,M,w],
      intros ψ psi_in_newX_u_notTheta,
      simp at psi_in_newX_u_notTheta,
      cases psi_in_newX_u_notTheta,
      { apply sat, rw psi_in_newX_u_notTheta, simp at *, },
      cases psi_in_newX_u_notTheta,
      { apply sat, simp at *, tauto, },
    },
    tauto,
  },
  { have : satisfiable ( (X2 \ {~~ϕ} ∪ {ϕ}) ∪ {θ}), {
      unfold satisfiable at *,
      use [W,M,w],
      intros ψ psi_in_newX2cupTheta,
      simp at psi_in_newX2cupTheta,
      cases psi_in_newX2cupTheta, -- ! changed from here onwards
      { apply sat, simp at *, tauto, },
      cases psi_in_newX2cupTheta,
      { rw psi_in_newX2cupTheta, apply of_not_not,
        change evaluate (M, w) (~~ϕ),
        apply sat (~~ϕ), simp, right, assumption,
      },
      { apply sat, simp at *, tauto, },
    },
    tauto,
  },
end


lemma localTabToInt : Π n X,
  n = lengthOfSet X →
    ∀ {X1 X2}, X = X1 ∪ X2 →
      (∃ ltX : localTableau X, (∀ Y1 Y2, Y1 ∪ Y2 ∈ endNodesOf ⟨X, ltX⟩ → ∃ θ, partInterpolant Y1 Y2 θ)) →
        ∃ θ, partInterpolant X1 X2 θ :=
begin
  intro N,
  apply nat.strong_induction_on N,
  intros n IH,
  intros X lenX_is_n X1 X2 defX pt,
  rcases pt with ⟨pt,nextInter⟩,
  cases pt,
  case byLocalRule : X B lr next {
    cases lr,
      -- The bot and not cases use Lemma 14
      case bot : X bot_in_X { rw defX at bot_in_X, exact botInter bot_in_X, },
      case not : X ϕ in_both { rw defX at in_both, exact notInter in_both },
      case neg : X ϕ notnotphi_in {
        have notnotphi_in_union : ~~ϕ ∈ X1 ∪ X2, { rw defX at notnotphi_in, assumption, },
        simp at *,
        cases notnotphi_in_union,
        { -- case ~~ϕ ∈ X1
          subst defX,
          let newX1 := X1 \ {~~ϕ} ∪ {ϕ},
          let newX2 := X2 \ {~~ϕ}, -- to deal with possible overlap
          have yclaim : newX1 ∪ newX2 ∈ { (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ} }, {
            rw finset.mem_singleton,
            change (X1 \ {~~ϕ} ∪ {ϕ}) ∪ (X2 \ {~~ϕ}) = (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ},
            ext1 a, split ; { intro hyp, simp at hyp, simp, tauto, },
          },
          set m := lengthOfSet (newX1 ∪ newX2),
          have m_lt_n : m < n, {
            rw lenX_is_n,
            exact localRulesDecreaseLength (localRule.neg (by {finish} : ~~ϕ ∈ X1 ∪ X2)) (newX1 ∪ newX2) yclaim,
          },
          have nextNextInter : (∀ (Y1 Y2 : finset formula), Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, (next (newX1 ∪ newX2) yclaim)⟩ → Exists (partInterpolant Y1 Y2)), {
            intros Y1 Y2, apply nextInter, finish,
          },
          have childInt : Exists (partInterpolant newX1 newX2) :=
            IH m m_lt_n (newX1 ∪ newX2) (by refl) (by refl) (next (newX1 ∪ newX2) yclaim) nextNextInter,
          cases childInt with θ theta_is_chInt,
          use θ,
          exact notnotInterpolantX1 notnotphi_in_union theta_is_chInt,
        },
        { -- case ~~ϕ ∈ X2
          ---- based on copy-paste from previous case, changes marked with "!" ---
          subst defX,
          let newX1 := X1 \ {~~ϕ}, -- to deal with possible overlap -- !
          let newX2 := X2 \ {~~ϕ} ∪ {ϕ}, -- !
          have yclaim : newX1 ∪ newX2 ∈ { (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ} }, {
            rw finset.mem_singleton,
            change (X1 \ {~~ϕ}) ∪ (X2 \ {~~ϕ} ∪ {ϕ}) = (X1 ∪ X2) \ {~~ϕ} ∪ {ϕ}, -- !
            ext1 a, split ; { intro hyp, simp at hyp, simp, tauto, },
          },
          set m := lengthOfSet (newX1 ∪ newX2),
          have m_lt_n : m < n, {
            rw lenX_is_n,
            exact localRulesDecreaseLength (localRule.neg (by {finish} : ~~ϕ ∈ X1 ∪ X2)) (newX1 ∪ newX2) yclaim,
          },
          have nextNextInter : (∀ (Y1 Y2 : finset formula), Y1 ∪ Y2 ∈ endNodesOf ⟨newX1 ∪ newX2, (next (newX1 ∪ newX2) yclaim)⟩ → Exists (partInterpolant Y1 Y2)), {
            intros Y1 Y2, apply nextInter, finish,
          },
          have childInt : Exists (partInterpolant newX1 newX2) :=
            IH m m_lt_n (newX1 ∪ newX2) (by refl) (by refl) (next (newX1 ∪ newX2) yclaim) nextNextInter,
          cases childInt with θ theta_is_chInt,
          use θ,
          exact notnotInterpolantX2 notnotphi_in_union theta_is_chInt,
        },
      },
      case con : {
        sorry,
      },
      case nCo : {
        sorry,
      },
  },
  case sim : X X_is_simple {
    apply nextInter,
    unfold endNodesOf,
    rw defX, simp,
  }
end

lemma vocProj (X) : voc (projection X) ⊆ voc X :=
begin
  unfold voc vocabOfFormula vocabOfSetFormula,
  simp,
  intros ϕ phi_in_proj,
  rw proj at phi_in_proj,
  intros a aInVocPhi,
  simp,
  tauto,
end

lemma projUnion {X Y} : projection (X ∪ Y) = projection X ∪ projection Y :=
begin
  unfold projection finset.bUnion,
  ext1,
  split ; finish,
end

open hasLength

-- tableau interpolation -- IDEA: similar to almostCompleteness
-- part of this is part of Lemma 15
lemma almostTabToInt {X} (ctX : closedTableau X) : Π X1 X2, X = X1 ∪ X2 → ∃ θ, partInterpolant X1 X2 θ :=
begin
  induction ctX,
  case loc: X ltX next IH {
    intros X1 X2 defX,
    have nextLtAndInter : (∃ ltX : localTableau X, (∀ Y1 Y2, Y1 ∪ Y2 ∈ endNodesOf ⟨X, ltX⟩ → ∃ θ, partInterpolant Y1 Y2 θ)), {
      use ltX,
      intros Y1 Y2 y_is_endOfX,
      specialize next (Y1 ∪ Y2) y_is_endOfX,
      exact IH (Y1 ∪ Y2) y_is_endOfX Y1 Y2 (by refl),
    },
    exact localTabToInt _ X (by refl) defX nextLtAndInter,
  },
  case atm: X ϕ notBoxPhi_in_X simpleX ctProjNotPhi IH {
    intros X1 X2 defX,
    subst defX,
    simp at *,
    cases notBoxPhi_in_X,
    { -- case ~□ϕ ∈ X1
      let newX1 := projection X1 ∪ { ~ϕ },
      let newX2 := projection X2,
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ}, { rw projUnion, ext1, simp, tauto, },
      rw ← yclaim at ctProjNotPhi,
      have nextInt : ∃ θ, partInterpolant newX1 newX2 θ :=
        IH newX1 newX2 (by {rw yclaim, simp,}),
      rcases nextInt with ⟨θ,vocSub,unsat1,unsat2⟩,
      use ~□~θ,
      repeat { split, },
      -- it remains to show the three properties of the interpolant
      { change voc θ ⊆ voc X1 ∩ voc X2,
        have inc1 : voc newX1 ⊆ voc X1, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at *,
          rcases aIn with ⟨ψ,psi_in_projX1|psi_is_notPhi⟩,
          { use □ψ, change □ψ ∈ X1 ∧ a ∈ voc □ψ, rw ← proj, tauto, },
          { use ~□ϕ, subst psi_is_notPhi, tauto, }
        },
        have inc2 : voc newX2 ⊆ voc X2, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at *,
          rcases aIn with ⟨ψ,psi_in_projX2⟩,
          { use □ψ, change □ψ ∈ X2 ∧ a ∈ voc □ψ, rw ← proj, tauto, },
        },
        intros a aIn, norm_num,
        specialize vocSub aIn, simp at vocSub,
        split,
        apply inc1, tauto,
        apply inc2, tauto,
      },
      all_goals { unfold satisfiable at *, },
      { by_contradiction hyp,
        rcases hyp with ⟨W,M,w,sat⟩,
        apply unsat1,
        use [W,M],
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~□ϕ) (by {simp, apply notBoxPhi_in_X, }),
        unfold evaluate at othersat,
        simp at othersat,
        rcases othersat with ⟨v,rel_w_v,v_not_phi⟩,
        use v,
        intros ψ psi_in_newX1,
        simp at psi_in_newX1,
        cases psi_in_newX1,
        { subst psi_in_newX1, specialize sat (~~□~θ), unfold evaluate at *, simp at sat, exact sat v rel_w_v, },
        cases psi_in_newX1,
        { rw proj at psi_in_newX1, specialize sat □ψ, unfold evaluate at sat, apply sat, simp, assumption, assumption, },
        { subst psi_in_newX1, unfold evaluate, assumption, },
      },
      { by_contradiction hyp,
        rcases hyp with ⟨W,M,w,sat⟩,
        apply unsat2,
        use [W,M],
        --- we use ~□~θ to get a different world:
        let othersat := sat (~□~θ) (by simp),
        unfold evaluate at othersat,
        simp at othersat,
        rcases othersat with ⟨v,rel_w_v,v_not_phi⟩,
        use v,
        intros ψ psi_in_newX2,
        simp at psi_in_newX2,
        cases psi_in_newX2,
        { subst psi_in_newX2, assumption, },
        { rw proj at psi_in_newX2, specialize sat □ψ, unfold evaluate at sat, apply sat, simp, assumption, assumption, },
      },
    },
    {  -- case ~□ϕ ∈ X2
      let newX1 := projection X1,
      let newX2 := projection X2 ∪ { ~ϕ },
      ---- what follows is *based* on copying the previous case ----
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ}, { rw projUnion, ext1, simp, tauto, },
      rw ← yclaim at ctProjNotPhi,
      have nextInt : ∃ θ, partInterpolant newX1 newX2 θ :=
        IH newX1 newX2 (by {rw yclaim, simp,}),
      rcases nextInt with ⟨θ,vocSub,unsat1,unsat2⟩,
      use □θ, -- !!
      repeat { split, },
      -- it remains to show the three properties of the interpolant
      { change voc θ ⊆ voc X1 ∩ voc X2,
        have inc1 : voc newX1 ⊆ voc X1, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at *,
          rcases aIn with ⟨ψ,psi_in_projX1⟩,
          { use □ψ, change □ψ ∈ X1 ∧ a ∈ voc □ψ, rw ← proj, tauto, },
        },
        have inc2 : voc newX2 ⊆ voc X2, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at *,
          rcases aIn with ⟨ψ,psi_in_projX1|psi_is_notPhi⟩,
          { use □ψ, change □ψ ∈ X2 ∧ a ∈ voc □ψ, rw ← proj, tauto, },
          { use ~□ϕ, subst psi_is_notPhi, tauto, }
        },
        intros a aIn, norm_num,
        specialize vocSub aIn, simp at vocSub,
        split,
        apply inc1, tauto,
        apply inc2, tauto,
      },
      all_goals { unfold satisfiable at *, },
      { by_contradiction hyp,
        rcases hyp with ⟨W,M,w,sat⟩,
        apply unsat1,
        use [W,M],
        --- we use ~□θ to get a different world:
        let othersat := sat (~□θ) (by simp ),
        unfold evaluate at othersat,
        simp at othersat,
        rcases othersat with ⟨v,rel_w_v,v_not_phi⟩,
        use v,
        intros ψ psi_in_newX1,
        simp at psi_in_newX1,
        cases psi_in_newX1,
        { subst psi_in_newX1, specialize sat (~□θ), unfold evaluate at *, simp at sat, tauto, },
        { rw proj at psi_in_newX1, specialize sat □ψ, unfold evaluate at sat, apply sat, simp, assumption, assumption, },
      },
      { by_contradiction hyp,
        rcases hyp with ⟨W,M,w,sat⟩,
        apply unsat2,
        use [W,M],
        --- we use ~□ϕ to get a different world:
        let othersat := sat (~□ϕ) (by { simp, assumption, }),
        unfold evaluate at othersat,
        simp at othersat,
        rcases othersat with ⟨v,rel_w_v,v_not_phi⟩,
        use v,
        intros ψ psi_in_newX2,
        simp at psi_in_newX2,
        cases psi_in_newX2,
        { rw psi_in_newX2, specialize sat □θ, simp at sat, unfold evaluate at sat, apply sat, assumption, },
        cases psi_in_newX2,
        { rw proj at psi_in_newX2, specialize sat □ψ, simp at sat, unfold evaluate at sat, apply sat, right, assumption, assumption, },
        { rw psi_in_newX2, unfold evaluate, assumption, },
      },
    },
  },
end

lemma tabToInt {X1 X2} : closedTableau (X1 ∪ X2) → ∃ θ, partInterpolant X1 X2 θ
| ctX := almostTabToInt ctX X1 X2 (by refl)
