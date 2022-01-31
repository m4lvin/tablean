import syntax
import semantics

lemma mytaut1 (p : char) : tautology ((·p) ↣ (·p)) :=
begin
  unfold tautology evaluatePoint evaluate,
  intros W M w,
  tauto,
end

open classical

lemma mytaut2 (p : char) : tautology ((~ (~ · p)) ↣ · p) :=
begin
  unfold tautology evaluatePoint evaluate,
  intros W M w,
  classical,
  tauto,
end

def myModel : kripkeModel ℕ :=
  { val := (λ _ _ , true),
    rel := (λ _ v, v == 1 ) }

lemma mysat (p : char) : satisfiable (·p) :=
begin
  unfold satisfiable,
  existsi ℕ,
  existsi myModel,
  existsi 1,
  unfold evaluatePoint evaluate,
end

-- Some validities of basic modal logic

lemma boxTop :
  tautology ([]⊤) :=
begin
  unfold tautology evaluatePoint evaluate,
  tauto,
end

lemma A3 (X Y : formula) :
  tautology ([](X ⋀ Y) ↣ []X ⋀ []Y) :=
begin
  unfold tautology evaluatePoint evaluate,
  intros W M w,
  by_contradiction hyp,
  cases hyp with hl hr,
  contrapose! hr,
  split,
  { intros v1 ass, exact (hl v1 ass).1 },
  { intros v2 ass, exact (hl v2 ass).2 },
end
