
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


-- TODO: move to syntax.lean
lemma vocSingleToSet {ϕ X} : ϕ ∈ X → vocabOfFormula ϕ ⊆ vocabOfSetFormula X :=
begin
  intros phi_in_X a a_invocPhi,
  unfold vocabOfSetFormula,
  sorry,
end

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
      exact vocSingleToSet pSide aIn,
      have h : ~ϕ ∈ X2 , { finish, },
      have := vocSingleToSet h,
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
      exact vocSingleToSet nSide aIn,
      have h : ϕ ∈ X2 , { finish, },
      have := vocSingleToSet h,
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


lemma tabToInt : ∀ X1 X2, partedLocalTableau X1 X2 → ∃ θ, interpolant X1 X2 θ :=
begin
  intros X1 X2 pt,
  unfold partedLocalTableau at pt,
  cases pt, -- NOTE: we need induction, but that loses the partition, do induction on n:=|X| instead???
  case byLocalRule : B lr next {
    cases lr,
      -- The bot and not cases use Lemma 14
      case bot : bot_in_X { exact botInter bot_in_X, },
      case not : ϕ in_both { exact notInter in_both },
      case neg : {
        sorry,
      },
      case con : {
        sorry,
      },
      case nCo : {
        sorry,
      },
  },
  case sim : {
    sorry,
  }
end
