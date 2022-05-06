import syntax

@[simp]
lemma union_singleton_is_insert {X : finset formula} {ϕ: formula} :
  X ∪ {ϕ} = insert ϕ X :=
begin
  have fo := finset.insert_eq ϕ X,
  finish,
end

@[simp]
lemma sdiff_singleton_is_erase {X : finset formula} {ϕ: formula} :
  X \ {ϕ} = X.erase ϕ :=
begin
  apply finset.induction_on X,
  simp,
  intros g Y gNotInY IH,
  ext1,
  finish,
end

@[simp]
lemma lengthAdd {X : finset formula} :
  ∀ {ϕ} (h : ϕ ∉ X), lengthOfSet (insert ϕ X) = lengthOfSet X + lengthOfFormula ϕ :=
begin
  apply finset.induction_on X,
  {
    unfold lengthOfSet,
    simp,
  },
  {
    intros ψ Y psiNotInY IH,
    unfold lengthOfSet at *,
    intros ϕ h,
    finish,
  },
end

@[simp]
lemma lengthOf_insert_leq_plus {X: finset formula} {ϕ : formula} :
  lengthOfSet (insert ϕ X) ≤ lengthOfSet X + lengthOfFormula ϕ :=
begin
cases (em (ϕ ∈ X)) with in_x not_in_x,
{ rw finset.insert_eq_of_mem in_x, simp, },
{ rw lengthAdd not_in_x, },
end

@[simp]
lemma lengthRemove (X : finset formula) :
  ∀ ϕ ∈ X, lengthOfSet (X.erase ϕ) + lengthOfFormula ϕ = lengthOfSet X :=
begin
  intros ϕ in_X,
  have claim : lengthOfSet (insert ϕ (X \ {ϕ})) = lengthOfSet (X \ {ϕ}) + lengthOfFormula ϕ,
  {
    apply lengthAdd,
    simp,
  },
  have anotherClaim : insert ϕ (X \ {ϕ}) = X, {
    ext1,
    simp only [finset.mem_sdiff, finset.mem_insert, finset.mem_singleton],
    split,
    finish,
    tauto,
  },
  rw anotherClaim at claim,
  finish,
end


@[simp]
lemma sum_union_le { T } [decidable_eq T] : ∀ { X Y : finset T } { F : T → ℕ }, (X ∪ Y).sum F ≤ X.sum F + Y.sum F :=
begin
  intros X Y F,
  { calc (X ∪ Y).sum F
       ≤ (X ∪ Y).sum F + (X ∩ Y).sum F : by { simp, }
   ... = X.sum F + Y.sum F : finset.sum_union_inter,
  },
end
