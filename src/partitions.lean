
import syntax
import tableau
import semantics
import soundness
import vocabulary

open hasVocabulary has_sat

def partition := finset formula × finset formula

def partedTableau (X1 X2) : Type := closedTableau (X1 ∪ X2)

def partedLocalTableau (X1 X2) : Type := localTableau (X1 ∪ X2)


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

lemma localTabToInt : Π n X, n = lengthOfSet X → ∀ {X1 X2}, X = X1 ∪ X2 → partedLocalTableau X1 X2 → ∃ θ, partInterpolant X1 X2 θ :=
begin
  intro N,
  apply nat.strong_induction_on N,
  intros n IH,
  intros X lenX_is_n X1 X2 defX pt,
  unfold partedLocalTableau at pt,
  cases pt,
  case byLocalRule : B lr next {
    cases lr,
      -- The bot and not cases use Lemma 14
      case bot : bot_in_X { exact botInter bot_in_X, },
      case not : ϕ in_both { exact notInter in_both },
      case neg : ϕ notnotphi_in {
        simp at *,
        cases notnotphi_in,
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
          have childInt : Exists (partInterpolant newX1 newX2) :=
            IH m m_lt_n (newX1 ∪ newX2) (by refl) (by refl) (next (newX1 ∪ newX2) yclaim),
          cases childInt with θ theta_is_chInt,
          rcases theta_is_chInt with ⟨vocSub,noSatX1,noSatX2⟩,
          use θ,
          unfold partInterpolant at *,
          split,
          { rw vocPreserved X1 (~~ϕ) ϕ notnotphi_in (by {unfold voc, simp, }),
            change voc θ ⊆ voc newX1 ∩ voc X2,
            have : voc newX2 ⊆ voc X2 , { apply vocMonotone, simp, },
            intros a aInVocTheta,
            simp at *,
            rw finset.subset_inter_iff at vocSub,
            tauto,
          },
          split,
          { by_contradiction hyp,
            unfold satisfiable at hyp,
            rcases hyp with ⟨W,M,w,sat⟩,
            have : satisfiable (newX1 ∪ {~θ}), {
              unfold satisfiable,
              use [W,M,w],
              intros ψ psi_in_newX_u_notTheta,
              simp at psi_in_newX_u_notTheta,
              cases psi_in_newX_u_notTheta,
              { apply sat, rw psi_in_newX_u_notTheta, simp at *, },
              cases psi_in_newX_u_notTheta,
              { apply sat, simp at *, tauto, },
              { rw psi_in_newX_u_notTheta, apply of_not_not,
                change evaluate (M, w) (~~ϕ),
                specialize sat (~~ϕ),
                apply sat, simp, right, assumption,
              },
            },
            tauto,
          },
          { by_contradiction hyp,
            unfold satisfiable at hyp,
            rcases hyp with ⟨W,M,w,sat⟩,
            have : satisfiable (newX2 ∪ {θ}), {
              unfold satisfiable at *,
              use [W,M,w],
              intros ψ psi_in_newX2cupTheta,
              apply sat, simp at *, tauto,
            },
            tauto,
          },
        },
        { -- case ~~ϕ ∈ X2
          sorry,
        }
      },
      case con : {
        sorry,
      },
      case nCo : {
        sorry,
      },
  },
  case sim : X_is_simple {
    -- NOTE: still missing: also need to assume that interpolants for (all partitions of) all end nodes are given!?
    sorry,
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

-- tableau interpolation -- IDEA: similar to almostCompleteness
-- part of this is part of Lemma 15
lemma almostTabToInt : Π {n} X, n = lengthOfSet X → ∀ {X1 X2}, X = X1 ∪ X2 → closedTableau X → ∃ θ, partInterpolant X1 X2 θ :=
begin
  intro n,
  apply nat.strong_induction_on n,
  intros n IH,
  intros X lX_is_n X1 X2 defX ctX,
  cases ctX,
  case loc: X ltX next { -- CASE: X is not simple
    apply localTabToInt _ X (by refl) defX,
    -- TODO: use IH to get interpolants for everything in "next" -- NEXT HERE !!!
    unfold partedLocalTableau, rw defX at *, assumption,
  },
  case atm: X ϕ notBoxPhi_in_X simpleX ctProjNotPhi { -- CASE: X is simple
    subst defX,
    simp at *,
    cases notBoxPhi_in_X,
    { -- case ~□ϕ ∈ X1
      let newX1 := projection X1 ∪ { ~ϕ },
      let newX2 := projection X2,
      have yclaim : newX1 ∪ newX2 = projection (X1 ∪ X2) ∪ {~ϕ}, { rw projUnion, ext1, simp, tauto, },
      rw ← yclaim at ctProjNotPhi,
      have m_lt_n : lengthOfSet (newX1 ∪ newX2) < n, {
         calc lengthOfSet (newX1 ∪ newX2)
            = lengthOfSet (projection (X1 ∪ X2) ∪ {~ϕ}) : by { rw yclaim, }
        ... < lengthOfSet (X1 ∪ X2) : atmRuleDecreasesLength (by {simp, tauto} : ~□ϕ ∈ X1 ∪ X2)
        ... = n : by { tauto, } ,
      },
      have nextInt : ∃ θ, partInterpolant newX1 newX2 θ :=
        IH _ m_lt_n (newX1 ∪ newX2) (by refl) (by refl) ctProjNotPhi,
      rcases nextInt with ⟨θ,vocSub,unsat1,unsat2⟩,
      use ~□~θ,
      repeat { split, },
      -- it remains to show the three properties of the interpolant
      { change voc θ ⊆ voc X1 ∩ voc X2,
        have inc1 : voc newX1 ⊆ voc X1, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at aIn,
          simp,
          rcases aIn with ⟨ψ,psi_in_projX1|psi_is_notPhi⟩,
          { use □ψ, change □ψ ∈ X1 ∧ a ∈ voc □ψ, rw ← proj, tauto, },
          { use ~□ϕ, split, assumption, subst psi_is_notPhi, tauto, }
        },
        have inc2 : voc newX2 ⊆ voc X2, {
          intros a aIn, unfold voc vocabOfSetFormula finset.bUnion at *, simp at aIn,
          simp,
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
        { subst psi_in_newX1, unfold evaluate, specialize sat (~~□~θ), simp at sat,
          unfold evaluate at sat, simp at sat,
          exact sat v rel_w_v,
        },
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
      sorry,
      -- TODO: use □θ,
    },
  },
end

lemma tabToInt {X1 X2} : closedTableau (X1 ∪ X2) → ∃ θ, partInterpolant X1 X2 θ :=
begin
  apply almostTabToInt,
  refl,
  simp,
end
