/- GID: D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/WeightedCycleWalk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic parity coordinates identify the actual alternating walk product with the quotient of the two matching products. -/
import D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
import D5.S3.Combinatorics.Graph.Walks.WeightedVertexProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
open SimpleGraph
open scoped BigOperators Classical Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open D5.S3.Combinatorics.Graph.Walks.WeightedVertexProducts

/-- Interleave the two parity classes around the ordinary cycle. -/
def parityEquiv (n : ℕ) : (Fin (n + 2) ⊕ Fin (n + 2)) ≃ Fin (2 * (n + 2)) where
  toFun
    | Sum.inl i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩
    | Sum.inr i => ⟨2 * i.val, by have := i.isLt; omega⟩
  invFun j := if j.val % 2 = 1 then Sum.inl ⟨j.val / 2, by have := j.isLt; omega⟩
    else Sum.inr ⟨j.val / 2, by have := j.isLt; omega⟩
  left_inv := by
    rintro (i | i) <;> dsimp <;> simp [Nat.add_div, Nat.mul_div_right] <;> congr <;> omega
  right_inv j := by
    dsimp
    split_ifs <;> apply Fin.ext <;> dsimp <;> omega

/-- The parity-coordinate graph is an ordinary even cycle. -/
def parityIso (n : ℕ) : evenCycleGraph n ≃g cycleGraph (2 * (n + 2)) where
  __ := parityEquiv n
  map_rel_iff' := by
    intro i j
    rw [cycleGraph_adj']
    have hc (z : ℕ) : z = 1 ↔ (z : ℤ) = 1 := by omega
    simp only [hc]
    rw [Fin.intCast_val_sub_eq_sub_add_ite, Fin.intCast_val_sub_eq_sub_add_ite]
    cases i <;> cases j
    all_goals
      simp only [parityEquiv, Equiv.coe_fn_mk, evenCycleGraph,
        finRotate_apply, Fin.ext_iff, Fin.val_add_one, Fin.le_iff_val_le_val]
      push_cast
      split_ifs <;> (try simp_all only [Fin.ext_iff, Fin.val_last])
      all_goals push_cast
      all_goals first | omega | (simp only [iff_false, not_or]; constructor <;> intro h <;> omega)

private def traversals (n : ℕ) :
    (m : ℕ) → (evenCycleGraph n).Walk (Sum.inl 0) (Sum.inl (m : Fin (n + 2)))
  | 0 => .nil
  | m + 1 =>
    let h₁ : (evenCycleGraph n).Adj (Sum.inl (m : Fin (n + 2)))
        (Sum.inr ((m + 1 : ℕ) : Fin (n + 2))) :=
      Or.inr (by simp [finRotate_apply])
    let h₂ : (evenCycleGraph n).Adj (Sum.inr ((m + 1 : ℕ) : Fin (n + 2)))
        (Sum.inl ((m + 1 : ℕ) : Fin (n + 2))) := Or.inl rfl
    ((traversals n m).concat h₁).concat h₂

private theorem traversals_length (n m : ℕ) : (traversals n m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [traversals, Walk.length_concat, ih]; omega

private theorem traversals_support (n m : ℕ) :
    (traversals n m).support = Sum.inl 0 :: (List.range m).flatMap
      (fun j => [Sum.inr ((j + 1 : ℕ) : Fin (n + 2)), Sum.inl ((j + 1 : ℕ) : Fin (n + 2))]) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [traversals, Walk.support_concat, ih, List.range_succ, List.flatMap_append, List.append_assoc]

/-- One actual traversal of the coordinate cycle, with its actual edges. -/
def circuit (n : ℕ) : (evenCycleGraph n).Walk (Sum.inl 0) (Sum.inl 0) :=
  (traversals n (n + 2)).copy rfl (by simp)

theorem circuit_length (n : ℕ) : (circuit n).length = 2 * (n + 2) := by
  simp [circuit, traversals_length]

theorem circuit_isCycle (n : ℕ) : (circuit n).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    rw [Walk.support_tail_of_not_nil _ (by
      apply Walk.not_nil_iff_lt_length.mpr
      rw [circuit_length]
      omega)]
    simp only [circuit, Walk.support_copy, traversals_support, List.tail_cons]
    apply List.nodup_flatMap.mpr
    refine ⟨fun j hj => by simp, ?_⟩
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.getElem_range]
    intro z hz hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hz'
    have hne : ((i + 1 : ℕ) : Fin (n + 2)) ≠ ((j + 1 : ℕ) : Fin (n + 2)) := by
      intro he
      have he' : finRotate (n + 2) (i : Fin (n + 2)) = finRotate (n + 2) (j : Fin (n + 2)) := by
        simpa [finRotate_apply] using he
      have hh := congrArg Fin.val ((finRotate (n + 2)).injective he')
      simp only [List.length_range] at hi hj
      simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hh
      omega
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · rw [circuit_length]
    omega

private theorem traversals_alpha {A : Type*} [CommGroup A] (n : ℕ)
    (w : Sym2 (Fin (n + 2) ⊕ Fin (n + 2)) → A) (m : ℕ) :
    alpha w (traversals n m) = ∏ j ∈ Finset.range m,
      w s(Sum.inl (j : Fin (n + 2)), Sum.inr ((j + 1 : ℕ) : Fin (n + 2))) /
        w s(Sum.inl ((j + 1 : ℕ) : Fin (n + 2)), Sum.inr ((j + 1 : ℕ) : Fin (n + 2))) := by
  induction m with
  | zero => simp [traversals, alpha]
  | succ m ih =>
    rw [Finset.prod_range_succ]
    simp only [traversals, alpha, Walk.edges_concat, List.concat_eq_append, List.map_append,
      List.map_singleton, List.alternatingProd_append, List.length_append,
      List.length_singleton, List.length_map,
      Walk.length_edges, Walk.length_concat, traversals_length,
      List.alternatingProd_singleton] at *
    rw [show (-1 : ℤ) ^ (2 * m) = 1 by simp [pow_mul],
      show (-1 : ℤ) ^ (2 * m + 1) = -1 by simp [pow_add, pow_mul]]
    simp only [zpow_one, zpow_neg_one]
    have hswap : s(Sum.inr ((m + 1 : ℕ) : Fin (n + 2)),
        Sum.inl ((m + 1 : ℕ) : Fin (n + 2))) =
        s(Sum.inl ((m + 1 : ℕ) : Fin (n + 2)),
          Sum.inr ((m + 1 : ℕ) : Fin (n + 2))) := Sym2.eq_swap
    rw [ih, hswap]
    simp [div_eq_mul_inv, mul_assoc]

/-- The closed traversal's alternating product is the quotient of its actual matchings. -/
theorem circuit_alpha {A : Type*} [CommGroup A] (n : ℕ)
    (w : Sym2 (Fin (n + 2) ⊕ Fin (n + 2)) → A) :
    alpha w (circuit n) =
      (∏ i, w s(Sum.inl i, Sum.inr (finRotate (n + 2) i))) /
        ∏ i : Fin (n + 2), w s(Sum.inl i, Sum.inr i) := by
  change alpha w ((traversals n (n + 2)).copy _ _) = _
  simp only [alpha, Walk.edges_copy]
  change alpha w (traversals n (n + 2)) = _
  rw [traversals_alpha, Finset.prod_div_distrib]
  have hnum := Fin.prod_univ_eq_prod_range
    (fun j : ℕ => w s(Sum.inl (j : Fin (n + 2)), Sum.inr (finRotate (n + 2) (j : Fin (n + 2))))) (n + 2)
  have hden := Fin.prod_univ_eq_prod_range
    (fun j : ℕ => w s(Sum.inl (finRotate (n + 2) (j : Fin (n + 2))),
      Sum.inr (finRotate (n + 2) (j : Fin (n + 2))))) (n + 2)
  simp only [finRotate_apply, Fin.cast_val_eq_self] at hnum hden
  simp only [Nat.cast_add, Nat.cast_one] at *
  rw [← hnum, ← hden]
  simpa only [finRotate_apply] using congrArg
    (fun a => (∏ i, w s(Sum.inl i, Sum.inr (finRotate (n + 2) i))) / a)
    (Equiv.prod_comp (finRotate (n + 2)) (fun i => w s(Sum.inl i, Sum.inr i)))

end D5.S3.Combinatorics.Graph.Walks.WeightedCycleWalk
