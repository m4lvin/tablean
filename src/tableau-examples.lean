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


-- Example 2
example : closedTableau { (·'r') ⋀ ~[](·'p'), (· 'r') ↣ []((·'p') ⋀ (·'q')) } :=
begin
  set α : finset formula := { (·'r') ⋀ ~[](·'p'), (· 'r') ↣ []((·'p') ⋀ (·'q')) },
  change closedTableau α,
  dsimp at *, -- gets rid of ↣
  split,
  rotate,
{
  -- con
  apply tableau.byRule (rule.con (by {simp} : ((·'r') ⋀ ~[](·'p')) ∈ α)),
  intros branch branch_def,
  simp at branch_def,
  -- nCo
  apply tableau.byRule (rule.nCo (by {finish} : ~((·'r') ⋀ (~((·'p')⋀·'q').box)) ∈ branch)),
  subst branch_def,
  dsimp at *,
  have rightBranch : tableau { (·'r'), ~(·'p').box, ~·'r'}, {
    let stuff : finset formula := { (·'r'), ~(·'p').box, ~·'r'},
    -- closed with negationg
    apply tableau.byRule (rule.not (by {simp} : (·'r') ∈ stuff ∧ ~(·'r') ∈ stuff)),
    intros noMorePremises inEmpty, finish,
  },
  have leftBranch : tableau { (·'r'), ~(·'p').box, ~~((·'p')⋀·'q').box }, {
    -- neg:
    apply tableau.byRule (rule.neg (by {simp} : ~~((·'p')⋀·'q').box ∈ { (·'r'), ~(·'p').box, ~~((·'p')⋀·'q').box })),
    intros child childDef,
    simp [*] at *,
    subst childDef,
    change tableau ({·'r', ~(·'p').box, ((·'p')⋀·'q').box}),
    -- atm:
    apply tableau.byRule (rule.atm (by {simp} : ~(·'p').box ∈ {·'r', ~(·'p').box, ((·'p')⋀·'q').box} )),
    intros child childDef,
    simp [*] at *,
    subst childDef,
    unfold projection,
    dsimp at *,
    -- change tableau ({~(·'p'), ((·'p')⋀·'q')}), -- blocked due to formProjection
    -- con:
    apply tableau.byRule,
    apply @rule.con _ (·'p') (·'q'),
    simp at *,
    use ((·'p')⋀·'q').box,
    simp,
    intros child childDef,
    simp at *,
    subst childDef,
    -- not:
    apply tableau.byRule,
    apply @rule.not _ (·'p'),
    simp,
    intros noMorePremises inEmpty, finish,
  },

  sorry, -- how to combine the two branches to a larger tableau?
},
{
  -- show that it is closed
  sorry,
},
end
