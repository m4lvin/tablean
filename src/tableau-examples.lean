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
    intros Y YinEmpty,
    cases YinEmpty,
  },
  { -- show that endNodesOf is empty
    intros Y,
    intro YisEndNode,
    unfold endNodesOf at *,
    simp at *,
    exfalso,
    rcases YisEndNode with ⟨a,h,hyp⟩,
    subst h,
    simp at *,
    cases hyp,
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
    apply localTableau.byLocalRule (@localRule.not _ p _) emptyTableau,
    exact dec_trivial,
  },
  { -- show that endNodesOf is empty
    intros Y,
    intro YisEndNode,
    simp at *,
    exfalso,
    rcases YisEndNode with ⟨a,h,hyp⟩,
    subst h,
    simp at *,
    rcases hyp with ⟨Y,Ydef,YinEndNodes⟩,
    subst Ydef,
    finish,
  },
end

-- preparing example 2
def subTabForEx2 : closedTableau {r, ~□p, □(p ⋏ q)} :=
begin
  apply @closedTableau.atm {r, ~□p, □(p ⋏ q)} p (by {simp,}),
  -- show that this set is simple:
  { unfold simple, simp at *, tauto, },
  apply closedTableau.loc,
  rotate,
  -- con:
  apply localTableau.byLocalRule (@localRule.con {p⋏q, ~p} p q (by {simp, })),
  intros child childDef,
  rw finset.mem_singleton at childDef,
  -- not:
  apply localTableau.byLocalRule (@localRule.not _ p _) emptyTableau,
  { subst childDef, exact dec_trivial, },
  { -- show that endNodesOf is empty
    intros Y,
    intro YisEndNode,
    simp at *,
    exfalso,
    assumption,
},
end

-- Example 2
example : closedTableau { r ⋏ ~□p, r ↣ □(p ⋏ q) } :=
begin
  apply closedTableau.loc,
  rotate,
  { -- localTableau α
    -- con
    apply localTableau.byLocalRule,
    apply localRule.con,
    simp,
    split,
    refl,
    refl,
    intros branch branch_def,
    rw finset.mem_singleton at branch_def,
    rw finset.union_insert at branch_def,
    -- nCo
    apply localTableau.byLocalRule,
    apply @localRule.nCo _ r (~□(p ⋏ q)),
    rw branch_def,
    simp,
    intros b b_in,
    simp only [finset.mem_insert, finset.mem_singleton] at b_in,
    refine if h1 : b = branch \ {~(r⋏~□(p⋏q))} ∪ {~r} then _ else _,
    { -- right branch
      -- not:
      apply localTableau.byLocalRule (@localRule.not _ r _) emptyTableau,
      finish,
    },
    { --left branch
      have h2 : b = branch \ {~(r⋏~□(p⋏q))} ∪ {~~□(p⋏q)}, { tauto, },
      -- neg:
      apply localTableau.byLocalRule (@localRule.neg _ (□(p ⋏ q)) _),
      rotate, {rw h2, simp,},
      intros child childDef,
      -- ending local tableau with a simple node:
      apply localTableau.sim,
      rw finset.mem_singleton at childDef,
      rw childDef,
      unfold simple, simp at *, split, unfold simpleForm,
      intros f f_notDef1 f_in_branch,
      cases b_in,
      tauto,
      rw b_in at f_in_branch,
      simp at f_in_branch,
      cases f_in_branch,
      tauto,
      rw branch_def at f_in_branch,
      cases f_in_branch with l r, simp at r,
      cases r,
      { subst r, unfold r, },
      cases r,
      { subst r, unfold simpleForm, },
      { exfalso, tauto, },
    },
  },
  { -- tableau for the simple end nodes:
    rw conEndNodes,
    rw nCoEndNodes,
    intros Y Yin,
    simp at *,
    split_ifs at *,
    { -- not-R branch
      exfalso, -- show that there are no endnodes!
      simp at Yin,
      exact Yin,
    },
    { -- notnotbranch
      dedup,
      have Yis : Y = {r, ~□p, □(p ⋏ q)}, {
        simp at *,
        subst Yin,
        simp at *,
        ext1,
        split ; { intro hyp, finish, },
      },
      subst Yis,
      exact subTabForEx2,
    },
  },
end
