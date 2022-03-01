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
    simp,
    intros β inB,
    have same : β = {⊥}, { finish, },
    subst same,
    simp,
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
    simp,
    intros β β_prop,
    subst β_prop,
    simp at *,
    intros β β_prop,
    subst β_prop,
    simp,
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
    apply tableau.byRule (rule.con (by {simp only [eq_self_iff_true, or_false, and_self, finset.mem_insert, finset.mem_singleton]} : (r ⋀ ~□p) ∈ α )),
    intros branch branch_def,
    simp only [finset.union_insert, finset.mem_singleton] at branch_def,
    -- nCo
    apply tableau.byRule (rule.nCo (by {finish} : ~(r ⋀ (~(p ⋀ q).box)) ∈ branch)),
    subst branch_def,
    dsimp only at *,
    intros b b_in,
    simp only [finset.mem_insert, finset.mem_singleton] at b_in,
    change b = {r, ~□p, ~r} ∨
           b = {r, ~□p, ~~□(p⋀q)} at b_in,
    refine if h1 : b = {r, ~□p, ~r} then _ else if h2 : b = {r, ~□p, ~~□(p⋀q)} then _ else _,
    { rw h1, -- right branch
      let stuff : finset formula := { r, ~p.box, ~r},
      -- not:
      apply tableau.byRule (rule.not (by {simp only [true_or, eq_self_iff_true, or_true, and_self, finset.mem_insert, finset.mem_singleton]} : r ∈ stuff ∧ ~r ∈ stuff)),
      exact emptyTableau,
    },
    { rw h2, --left branch
      -- neg:
      apply tableau.byRule (rule.neg (by {simp only [eq_self_iff_true, or_true, and_self, finset.mem_insert, finset.mem_singleton]} : ~~□(p ⋀ q) ∈ { r, ~□p, ~~□(p ⋀ q) })),
      intros child childDef,
      simp only [finset.mem_singleton] at *,
      subst childDef,
      -- change tableau ({r, ~□p, □(p ⋀ q)}), -- SLOW, why?
      -- atm:
      apply tableau.byRule (rule.atm (by {simp} : ~□p ∈ {r, ~□p, □(p ⋀ q)} )),
      intros child childDef,
      simp only [false_or, eq_self_iff_true, finset.mem_singleton] at *,
      subst childDef,
      unfold projection,
      dsimp at *,
      -- change tableau ({~p, (p⋀·'q')}), -- blocked due to formProjection
      -- con:
      apply tableau.byRule,
      apply @rule.con _ p q,
      simp only [exists_prop, part.mem_of_option, or_false, finset.mem_union, finset.mem_insert, finset.mem_pimage, finset.mem_singleton, option.mem_def] at *,
      use □(p ⋀ q),
      simp only [eq_self_iff_true, or_true, formProjection, and_self],
      intros child childDef,
      simp only [finset.union_insert, finset.mem_singleton] at *,
      subst childDef,
      -- not:
      apply tableau.byRule,
      apply @rule.not _ p,
      finish,
      exact emptyTableau,
    },
    { itauto, }
  },
  { -- show that it is closed
    simp only [id.def, closedTableauIffChildrenClosed, finset.union_insert, finset.mem_insert, finset.mem_singleton, eq_mpr_eq_cast,
  cast_eq],
    intros β β_prop,
    simp only at β_prop,
    subst β_prop,
    intros β β_prop_left_right,
    cases β_prop_left_right with β_prop β_prop,
    { subst β_prop,
      simp only [cast_eq],
      apply isClosedTableau.byRule, -- why is this sill needed?
      simp,
    },
    { simp only at *,
      subst β_prop,
      simp only [cast_eq] at *,
      apply isClosedTableau.byRule,
      intros β β_prop,
      simp only [finset.mem_singleton] at β_prop,
      subst β_prop,
      simp only [closedTableauIffChildrenClosed, finset.mem_singleton] at *,
      intros β β_prop,
      simp only at β_prop,
      subst β_prop,
      simp only [sdiff_singleton_is_erase, closedTableauIffChildrenClosed, finset.union_insert, union_singleton_is_insert, finset.mem_singleton] at *,
      intros β β_prop,
      subst β_prop,
      norm_cast at *,

     },
  },
end
