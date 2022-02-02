import syntax
import tableau

-- set_option pp.proofs true
lemma noBot : provable (~ ⊥) :=
begin
  apply provable.byTableau,
  unfold closedTableau,
  split,
  swap 2,
  {
    apply tableau.byRule (rule.neg (finset.mem_singleton.mpr (refl (~~⊥)))),
    intros β inB,
    rw finset.sdiff_self at inB,
    rw finset.empty_union at inB,
    rw finset.mem_singleton at inB,
    rw inB,
    apply (tableau.byRule (rule.bot (finset.mem_singleton.mpr (refl ⊥)))),
    tauto,
  },
  {
    apply isClosedTableau.byRule (rule.neg (finset.mem_singleton.mpr (refl (~~⊥)))),
    intros β inB,
    have same : β = {⊥}, { finish, },
    subst same, -- this was the key idea to get rid of .mpr and cast :-)
    apply isClosedTableau.byRule,
    intro β,
    intro inNothing,
    tauto,
  },
end

-- an example:
lemma noContradiction : provable (~ (p ⋀ ~p)) :=
begin
  apply provable.byTableau,
  unfold closedTableau,
  split,
  swap 2,
  {
    apply tableau.byRule,
    -- neg:
    apply rule.neg,
    simp,
    intros β β_prop,
    simp at β_prop,
    rw β_prop,
    -- con:
    apply tableau.byRule,
    apply rule.con,
    simp,
    split,
    refl,
    refl,
    intros β2 β2_prop,
    simp at β2_prop,
    rw β2_prop,
    -- closed:
    apply tableau.byRule,
    apply rule.not,
    repeat { finish, },
    tauto,
  },
  {
    apply isClosedTableau.byRule,
    intros β β_prop,
    simp at β_prop,
    subst β_prop,
    apply isClosedTableau.byRule,
    intros β β_prop,
    simp at β_prop,
    simp,
    subst β_prop,
    apply isClosedTableau.byRule,
    tauto, -- no mopre premises
  },
end


def emptyTableau : Π (β : finset formula), β ∈ ∅ → tableau β :=
begin
  intros beta b_in_empty,
  exact absurd b_in_empty (finset.not_mem_empty beta),
end


-- Example 2
example : closedTableau { r ⋀ ~□p, r ↣ □(p ⋀ q) } :=
begin
  let α := { r ⋀ ~□p, r ↣ □(p ⋀ q) },
  change closedTableau α,
  dsimp at *, -- gets rid of ↣
  split,
  rotate,
  { -- con
    apply tableau.byRule (rule.con (by {simp} : (r ⋀ ~□p) ∈ α )),
    intros branch branch_def,
    simp at branch_def,
    -- nCo
    apply tableau.byRule (rule.nCo (by {finish} : ~(r ⋀ (~(p ⋀ q).box)) ∈ branch)),
    subst branch_def,
    dsimp at *,
    intros b b_in,
    simp at b_in,
    change b = {r, ~□p, ~r} ∨
           b = {r, ~□p, ~~□(p⋀q)} at b_in,
    refine if h1 : b = {r, ~□p, ~r} then _ else if h2 : b = {r, ~□p, ~~□(p⋀q)} then _ else _,
    { rw h1, -- right branch
      let stuff : finset formula := { r, ~p.box, ~r},
      -- not:
      apply tableau.byRule (rule.not (by {simp} : r ∈ stuff ∧ ~r ∈ stuff)),
      exact emptyTableau,
    },
    { rw h2, --left branch
      -- neg:
      apply tableau.byRule (rule.neg (by {simp} : ~~□(p ⋀ q) ∈ { r, ~□p, ~~□(p ⋀ q) })),
      intros child childDef,
      simp [*] at *,
      subst childDef,
      -- change tableau ({r, ~□p, □(p ⋀ q)}), -- SLOW, why?
      -- atm:
      apply tableau.byRule (rule.atm (by {simp} : ~□p ∈ {r, ~□p, □(p ⋀ q)} )),
      intros child childDef,
      simp [*] at *,
      subst childDef,
      unfold projection,
      dsimp at *,
      -- change tableau ({~p, (p⋀·'q')}), -- blocked due to formProjection
      -- con:
      apply tableau.byRule,
      apply @rule.con _ p q,
      simp at *,
      use □(p ⋀ q),
      simp,
      intros child childDef,
      simp at *,
      subst childDef,
      -- not:
      apply tableau.byRule,
      apply @rule.not _ p,
      simp,
      exact emptyTableau,
    },
    { finish, }
  },
  { -- show that it is closed
    apply isClosedTableau.byRule,
    intros β β_prop,
    simp at β_prop,
    simp,
    subst β_prop,

    apply isClosedTableau.byRule,
    intros β β_prop_left_right,

    cases β_prop_left_right with β_prop β_prop,
    { subst β_prop,
      apply isClosedTableau.byRule,
      intros β β_prop,
      simp at β_prop,
      finish, },
    { simp at *,
      cases β_prop with β_prop in_empty,
      subst β_prop,
      apply isClosedTableau.byRule,
      intros β β_prop,
      simp at β_prop,

      subst β_prop,
      simp at *,
      apply isClosedTableau.byRule,
      intros β β_prop,
      simp at β_prop,
      subst β_prop,

      apply isClosedTableau.byRule,
      intros β β_prop,
      simp at β_prop,
      subst β_prop,
      simp at *,

      apply isClosedTableau.byRule,
      intros β β_prop,
      simp at β_prop,
      finish,

      -- in_empty
      exact absurd in_empty (list.not_mem_nil β),
     },
  },
end
