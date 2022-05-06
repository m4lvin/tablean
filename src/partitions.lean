
import syntax
import tableau
import semantics

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

-- TODO: move to syntax.lean
lemma vocMonotone {X Y : finset formula} (hyp : X ⊆ Y) : voc X ⊆ voc Y :=
begin
  unfold voc, unfold vocabOfSetFormula at *,
  intros a aIn,
  unfold finset.bUnion at *,
  simp at *,
  tauto,
end

-- TODO: move to syntax.lean or create new vocabulary.lean ?!
lemma vocPreserved (X : finset formula) (ψ ϕ) :
  ψ ∈ X → voc ϕ = voc ψ → voc X = voc (X \ {ψ} ∪ {ϕ}) :=
begin
  intros psi_in_X eq_voc,
  unfold voc at *,
  unfold vocabOfSetFormula,
  ext1,
  split,
  all_goals { intro a_in, norm_num at *, },
  { rcases a_in with ⟨θ,_,a_in_vocTheta⟩,
    by_cases h : θ = ψ,
    { left, rw eq_voc, rw ← h, exact a_in_vocTheta, },
    { right, use θ, tauto, },
  },
  { cases a_in,
    { use ψ, rw ← eq_voc, tauto, },
    { rcases a_in with ⟨θ,_,a_in_vocTheta⟩, use θ, tauto, }
  },
end

lemma localTabToInt : Π n X, n = lengthOfSet X → ∀ X1 X2, X = X1 ∪ X2 → partedLocalTableau X1 X2 → ∃ θ, partInterpolant X1 X2 θ :=
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
          specialize IH m m_lt_n (newX1 ∪ newX2) (by refl) newX1 newX2,
          have ltNew := next (newX1 ∪ newX2) yclaim,
          have childInt : Exists (partInterpolant newX1 newX2), {
            apply IH (by refl) ltNew,
          },
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
  case sim : {
    -- NOTE: still missing: also need to assume that interpolants for (all partitions of) all end nodes are given!?
    sorry,
  }
end

-- tableau interpolation -- IDEA: similar to almostCompleteness
lemma almostTabToInt : Π n X, n = lengthOfSet X → ∀ X1 X2, X = X1 ∪ X2 → closedTableau X → ∃ θ, partInterpolant X1 X2 θ :=
begin
  sorry,
end

lemma tabToInt {X1 X2} : closedTableau (X1 ∪ X2) → ∃ θ, partInterpolant X1 X2 θ :=
begin
  apply almostTabToInt,
  refl,
  simp,
end
