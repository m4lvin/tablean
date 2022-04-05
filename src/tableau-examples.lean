import syntax
import tableau

-- set_option pp.proofs true
lemma noBot : provable (~ ⊥) :=
begin
  apply provable.byTableau,
  apply closedTableau.loc,
  swap 2,
  {
    apply localTableau.byLocalRule (localRule.neg (finset.mem_singleton.mpr (refl (~~⊥)))),
    intros β inB,
    rw finset.sdiff_self at inB,
    rw finset.empty_union at inB,
    rw finset.mem_singleton at inB,
    rw inB,
    apply (localTableau.byLocalRule (localRule.bot (finset.mem_singleton.mpr (refl ⊥)))),
    tauto,
  },
  { intros β inB,
    simp at *,
    cases inB,
  },
end

def emptyTableau : Π (β : finset formula), β ∈ ∅ → localTableau β :=
begin
  intros beta b_in_empty,
  exact absurd b_in_empty (finset.not_mem_empty beta),
end

-- an example:
lemma noContradiction : provable (~ (p ⋏ ~p)) :=
begin
  apply provable.byTableau,
  apply closedTableau.loc,
  swap 2,
  {
    apply localTableau.byLocalRule,
    -- neg:
    apply localRule.neg,
    simp,
    intros β β_prop,
    simp at β_prop,
    subst β_prop,
    -- con:
    apply localTableau.byLocalRule,
    apply localRule.con,
    simp,
    split,
    refl,
    refl,
    intros β2 β2_prop,
    simp at β2_prop,
    subst β2_prop,
    -- closed:
    apply localTableau.byLocalRule,
    apply localRule.not,
    repeat { finish, },
    exact emptyTableau,
  },
  { -- no simple end nodes:
    intros β β_prop,
    simp at *,
    cases β_prop,
  },
end



-- preparing example 2
def subTabForEx2 : closedTableau {r, ~□p, □(p ⋏ q)} :=
begin
  apply @closedTableau.atm {r, ~□p, □(p ⋏ q)} p (by {simp,}),
  -- show that this set is simple:
  { unfold simple, simp at *, tauto, },
  unfold projection,
  dsimp at *,
  -- change tableau ({~p, (p⋏·'q')}), -- blocked due to formProjection
  -- con:
  apply localTableau.byLocalRule,
  apply @localRule.con _ p q,
  simp only [exists_prop, part.mem_of_option, or_false, finset.mem_union, finset.mem_insert, finset.mem_pimage, finset.mem_singleton, option.mem_def] at *,
  use □(p ⋏ q),
  simp only [eq_self_iff_true, or_true, formProjection, and_self],
  intros child childDef,
  simp only [finset.union_insert, finset.mem_singleton] at *,
  subst childDef,
  -- not:
  apply localTableau.byLocalRule,
  apply @localRule.not _ p,
  finish,
  exact emptyTableau,
end


-- set_option profiler true

-- Example 2
example : closedTableau { r ⋏ ~□p, r ↣ □(p ⋏ q) } :=
begin
  let α := { r ⋏ ~□p, r ↣ □(p ⋏ q) },
  change closedTableau α,
  dsimp at *, -- gets rid of ↣
  apply closedTableau.loc,
  rotate,
  { -- localTableau α
    -- con
    apply localTableau.byLocalRule (localRule.con (by {simp only [eq_self_iff_true, or_false, and_self, finset.mem_insert, finset.mem_singleton]} : (r ⋏ ~□p) ∈ α )),
    intros branch branch_def,
    simp only [finset.union_insert, finset.mem_singleton] at branch_def,
    -- nCo
    apply localTableau.byLocalRule (localRule.nCo (by {finish} : ~(r ⋏ (~(p ⋏ q).box)) ∈ branch)),
    subst branch_def,
    dsimp only at *,
    intros b b_in,
    simp only [finset.mem_insert, finset.mem_singleton] at b_in,
    change b = {r, ~□p, ~r} ∨
           b = {r, ~□p, ~~□(p⋏q)} at b_in,
    refine if h1 : b = {r, ~□p, ~r} then _ else if h2 : b = {r, ~□p, ~~□(p⋏q)} then _ else _,
    { rw h1, -- right branch
      let stuff : finset formula := { r, ~p.box, ~r},
      -- not:
      apply localTableau.byLocalRule (localRule.not (by {simp only [true_or, eq_self_iff_true, or_true, and_self, finset.mem_insert, finset.mem_singleton]} : r ∈ stuff ∧ ~r ∈ stuff)),
      exact emptyTableau,
    },
    { rw h2, --left branch
      -- neg:
      apply localTableau.byLocalRule (localRule.neg (by {simp only [eq_self_iff_true, or_true, and_self, finset.mem_insert, finset.mem_singleton]} : ~~□(p ⋏ q) ∈ { r, ~□p, ~~□(p ⋏ q) })),
      intros child childDef,
      simp only [finset.mem_singleton] at *,
      subst childDef,
      -- ending local tableau with a simple node:
      apply localTableau.sim (by { unfold simple, simp at *, tauto, } : simple {r, ~□p, □(p ⋏ q)} ),
    },
    { itauto, }
  },
  { -- tableau for the simple end nodes:
    intro Y,
    intro YisEndNode,
    unfold endNodesOf at *,
    simp at *,
    have Yis : Y = {r, ~□p, □(p ⋏ q)}, {
      cases YisEndNode,
      -- unfold endNodesOf at *,
      sorry,
      sorry,
    },
    subst Yis,
    exact subTabForEx2,
  },
end
