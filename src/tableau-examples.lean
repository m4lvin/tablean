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
  let α := { r ⋏ ~□p, r ↣ □(p ⋏ q) },
  change closedTableau α,
  dsimp at *, -- gets rid of ↣
  apply closedTableau.loc,
  rotate,
  { -- localTableau α
    -- con
    apply localTableau.byLocalRule (localRule.con (by {simp} : (r ⋏ ~□p) ∈ α )),
    intros branch branch_def,
    simp only [finset.union_insert, finset.mem_singleton] at branch_def,
    -- nCo
    apply localTableau.byLocalRule (localRule.nCo (by {finish} : ~(r ⋏ (~(p ⋏ q).box)) ∈ branch)),
    dsimp only at *,
    intros b b_in,
    rw branch_def at b_in,
    simp only [finset.mem_insert, finset.mem_singleton] at b_in,
    refine if h1 : b = {r, ~□p, ~r} then _ else if h2 : b = {r, ~□p, ~~□(p⋏q)} then _ else _,
    { rw h1, -- right branch
      -- not:
      apply localTableau.byLocalRule (localRule.not (by {simp} : r ∈ { r, ~p.box, ~r} ∧ ~r ∈ { r, ~p.box, ~r})),
      exact emptyTableau,
    },
    { rw h2, --left branch
      -- neg:
      apply localTableau.byLocalRule (localRule.neg (by {simp} : ~~□(p ⋏ q) ∈ { r, ~□p, ~~□(p ⋏ q) })),
      intros child childDef,
      simp only [finset.mem_singleton] at *,
      rw childDef,
      -- ending local tableau with a simple node:
      apply localTableau.sim (by { unfold simple, simp at *, tauto, } : simple {r, ~□p, □(p ⋏ q)} ),
    },
    { itauto, }
  },
  { -- tableau for the simple end nodes:
    intro Y,
    intro Yin,
    rw setEndNodes at Yin,
    simp at Yin,
    -- rw help at Yin,
    apply classical.choice,
    rcases Yin with ⟨a,h,YnotRbranch|YnotnotBranch⟩,
    { -- not-R branch
      exfalso, -- show that there are no endnodes!
      subst h,
      sorry,
    },
    { -- notnotbranch
      have Yis : Y = {r, ~□p, □(p ⋏ q)}, {
        subst h,
        sorry,
      },
      subst Yis,
      fconstructor,
      exact subTabForEx2,
    },
  },
end

-- Problematic "infinite not-progressing tableau"
def explosion : nonempty (closedTableau { p }) :=
begin
  fconstructor,
  -- this should not be allowed, proof checking takes forever!
  -- repeat {
    apply closedTableau.loc,
    rotate,
    apply localTableau.sim,
    { unfold simple, simp, },
    intros Y Yin,
    simp at Yin,
    subst Yin,
  -- },
  sorry,
end
