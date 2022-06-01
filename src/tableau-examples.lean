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
noncomputable example : closedTableau { r ⋏ ~□p, r ↣ □(p ⋏ q) } :=
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
    -- rw branch_def at b_in,
    refine if h1 : b = branch \ {~(r⋏~□(p⋏q))} ∪ {~r} then _ else _,
    { rw h1, -- right branch
      -- not:
      apply localTableau.byLocalRule (localRule.not _) emptyTableau,
      use r, simp, finish,
    },
    { have h2 : b = branch \ {~(r⋏~□(p⋏q))} ∪ {~~□(p⋏q)}, { tauto, },
      rw h2, --left branch
      -- neg:
      apply localTableau.byLocalRule (@localRule.neg _ (□(p ⋏ q)) _),
      rotate, simp,
      intros child childDef,
      rw finset.mem_singleton at childDef,
      rw childDef,
      -- ending local tableau with a simple node:
      rw branch_def,
      apply localTableau.sim,
      unfold simple, simp at *, split, unfold simpleForm,
      intros f f_notDef1 f_notDef2 f_in_branch,
      cases f_in_branch,
      rw f_in_branch, unfold r,
      cases f_in_branch,
      rw f_in_branch, unfold simpleForm,
      rw f_in_branch, unfold simpleForm,
      tauto,
    },
  },
  { -- tableau for the simple end nodes:
    rw conEndNodes,
    rw nCoEndNodes,
    intros Y Yin,
    rw finset.mem_union at Yin,
    apply classical.choice, -- NOTE: This should not be needed?
    cases Yin,
    { -- not-R branch
      exfalso, -- show that there are no endnodes!
      simp at *,
      exact Yin,
    },
    { -- notnotbranch
      have Yis : Y = {r, ~□p, □(p ⋏ q)}, {
        dsimp at Yin,
        simp at Yin,
        sorry, -- How to simplify a 'dite false'?
      },
      subst Yis,
      fconstructor,
      exact subTabForEx2,
    },

  },
end
