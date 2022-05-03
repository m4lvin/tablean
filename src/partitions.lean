
import syntax
import tableau
import semantics

open hasVocabulary has_sat

def partition := finset formula × finset formula

def partedTableau (X1 X2) : Type := closedTableau (X1 ∪ X2)

def partedLocalTableau (X1 X2) : Type := localTableau (X1 ∪ X2)


-- Definition 24
def interpolant (X1 X2 : finset formula) (θ : formula) :=
  voc θ ⊆ (voc X1 ∩ voc X2)  ∧  ¬ satisfiable ( X1 ∪ {~θ} )  ∧  ¬ satisfiable ( X2 ∪ {θ} )

-- Lemma 14
lemma botInter {X1 X2} : ⊥ ∈ (X1 ∪ X2) → ∃ θ, interpolant X1 X2 θ :=
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
lemma notInter {X1 X2 ϕ} : ϕ ∈ (X1 ∪ X2) ∧ ~ϕ ∈ (X1 ∪ X2) → ∃ θ, interpolant X1 X2 θ :=
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


lemma tabToInt : Π n X, n = lengthOfSet X → ∀ X1 X2 {h}, X = (finset.disj_union X1 X2 h) → partedLocalTableau X1 X2 → ∃ θ, interpolant X1 X2 θ :=
begin
  intro N,
  apply nat.strong_induction_on N,
  intros n IH,
  intros X lenX_is_n X1 X2 noOverlap defX pt,
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
          have sameVoc : voc X1 = voc newX1, {
            sorry,
          },
          set m := lengthOfSet (newX1 ∪ X2),
          have m_lt_n : m < n, {
            have t:= localRulesDecreaseLength (localRule.neg (_ : ~~ϕ ∈ X1 ∪ X2)) (newX1 ∪ X2),
            { subst lenX_is_n,
              apply t,
              simp at *,
              ext1 a, specialize noOverlap a, simp at *,
              split,
              all_goals { intro lhs, sorry, }, -- FIXME: can "finish", but slow
            },
            finish,
          },
          specialize IH m m_lt_n (newX1 ∪ X2) (by refl) newX1 X2,
          have ltNew : localTableau (newX1 ∪ X2), { apply next, simp, sorry, },
          have childInt : Exists (interpolant newX1 X2), {
            apply IH _ (by refl) ltNew,
            intros a a_in_newX1,
            apply noOverlap a,
            -- STUCK: what if a = ϕ ???
            sorry,
          },
          cases childInt with θ theta_is_chInt,
          use θ,
          unfold interpolant at *,
          split,
          { rw sameVoc, tauto, },
          split,
          { sorry, }, -- TODO: use the satisfiability preservation from soundness or completeness?
          tauto,
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
    -- NOTE: still missing: also need to assume that interpolants for end nodes are given!?
    sorry,
  }
end
