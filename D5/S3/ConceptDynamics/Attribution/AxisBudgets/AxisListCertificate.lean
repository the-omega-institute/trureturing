/- GID: D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded row and column lists certify a Boolean inclusion factor with exact selected incidence. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import D5.S3.Combinatorics.ErdosUlam.SublatticeDefs

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open D5.S3.Combinatorics.ErdosUlam.SublatticeDefs

open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

namespace D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate

/-- An inclusion factor whose selected entries realize the specified incidence relation. -/
def MaskedFactorWithRows {d : ℕ} (k : ℕ) (i : Fin d) (budget : ℕ)
    (RowEdge : AxisSubset d i → AxisSubset d i → Prop) : Prop :=
  ∃ (f : AxisSubset d i → AxisSubset d i → Bool) (selected : Bool),
    f (axisTop i) (axisTop i) = false ∧ (selected = false → 3 ≤ k) ∧
    (∀ A, residualDegree k selected (decide (A = axisTop i)) (∑ B, (f A B).toNat)) ∧
    (∀ B, residualDegree k selected (decide (B = axisTop i)) (∑ A, (f A B).toNat)) ∧
    (∀ A B, A ≠ axisTop i → f A B = true → A.val ⊆ B.val) ∧
    axisCost i f ≤ budget ∧ ∀ A B, f A B = true ↔ RowEdge A B

namespace AxisMaskTransport

private def eraseZero {n : ℕ} (s : Finset (Fin n)) : AxisSubset (n + 1) 0 :=
  ⟨s.map (Fin.succEmb n), by simp⟩

private theorem eraseZero_injective (n : ℕ) :
    Function.Injective (eraseZero (n := n)) := by
  intro s t h
  obtain hs := congrArg Subtype.val h
  exact Finset.map_injective (Fin.succEmb n) hs

private theorem eraseZero_surjective (n : ℕ) :
    Function.Surjective (eraseZero (n := n)) := by
  intro A
  refine ⟨univ.filter (fun j => j.succ ∈ A.val), Subtype.ext ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hx
    exact (mem_filter.mp hj).2
  · intro hx
    have hne : x ≠ 0 := fun h => A.property (h ▸ hx)
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hne
    exact mem_map.mpr ⟨j, by simp [hx], rfl⟩

/-- Interpret a mask as a subset of the coordinates other than zero. -/
noncomputable def maskEquiv (n : ℕ) : Fin (2 ^ n) ≃ AxisSubset (n + 1) 0 :=
  Equiv.ofBijective (fun m => eraseZero (decode n m))
    ⟨(eraseZero_injective n).comp (decode_injective n),
      (eraseZero_surjective n).comp (decode_surjective n)⟩

theorem mask_rank (n : ℕ) (m : Fin (2 ^ n)) :
    (maskEquiv n m).val.card = weight n m := by
  change ((decode n m).map (Fin.succEmb n)).card = weight n m
  rw [card_map, decode_card]

private theorem mask_order {n : ℕ} (a b : Fin (2 ^ n)) :
    (maskEquiv n a).val ⊆ (maskEquiv n b).val ↔ a.val &&& b.val = a.val := by
  change (decode n a).map (Fin.succEmb n) ⊆ (decode n b).map (Fin.succEmb n) ↔ _
  rw [map_subset_map, ← inter_eq_left, ← decode_inter]
  let c : Fin (2 ^ n) := ⟨a.val &&& b.val, Nat.and_le_left.trans_lt a.isLt⟩
  exact ⟨fun h => congrArg Fin.val (decode_injective n (a₁ := c) (a₂ := a) h),
    congrArg (decode n)⟩

theorem mask_top (n : ℕ) (m : Fin (2 ^ n)) (hm : m.val = 2 ^ n - 1) :
    maskEquiv n m = axisTop 0 := by
  have hu : decode n m = univ := by
    ext j
    simp [decode, hm, Nat.testBit_two_pow_sub_one]
  apply Subtype.ext
  change (decode n m).map (Fin.succEmb n) = univ.erase 0
  rw [hu]
  ext x
  simp [Fin.succEmb, Fin.exists_succ_eq]

end AxisMaskTransport
open D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

namespace SparseAxisFactor

private theorem sum_sparse_degree {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) :
    (∑ x : V, (decide (x ∈ s)).toNat) = s.card := by
  calc
    _ = ∑ x : V, if x ∈ s then 1 else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases h : x ∈ s <;> simp [h]
    _ = s.card := by simp [sum_ite_mem]

private theorem sum_sparse_cost {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (p : V → Prop) [DecidablePred p] :
    (∑ x : V, if p x then (decide (x ∈ s)).toNat else 0) = (s.filter p).card := by
  calc
    _ = ∑ x : V, (decide (x ∈ s.filter p)).toNat := by
      apply sum_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
    _ = _ := sum_sparse_degree _

private theorem of_sparse_rows_and_columns {d : ℕ} (i : Fin d) (k budget : ℕ)
    (row col : AxisSubset d i → Finset (AxisSubset d i)) (marked : Bool)
    (ends : axisTop i ∉ row (axisTop i))
    (mode : marked = false → 3 ≤ k)
    (agree : ∀ A B, B ∈ row A ↔ A ∈ col B)
    (rowDegree : ∀ A, residualDegree k marked (decide (A = axisTop i)) (row A).card)
    (colDegree : ∀ B, residualDegree k marked (decide (B = axisTop i)) (col B).card)
    (support : ∀ A ≠ axisTop i, ∀ B ∈ row A, A.val ⊆ B.val)
    (budgetScore : 4 * (1 + ∑ A, if A ≠ axisTop i ∧ A.val.card % 2 = 1 then
      ((row A).filter fun B => B.val.card % 2 = 1).card else 0) ≤ budget) :
    MaskedFactorWithRows k i budget (fun a b => b ∈ row a) := by
  let edge : AxisSubset d i → AxisSubset d i → Bool := fun A B => decide (B ∈ row A)
  refine ⟨edge, marked, ?_, mode, ?_, ?_, ?_, ?_, ?_⟩
  · change edge (axisTop i) (axisTop i) = false
    simp [edge, ends]
  · intro A
    simpa only [edge, sum_sparse_degree] using rowDegree A
  · intro B
    simpa only [edge, agree, sum_sparse_degree] using colDegree B
  · intro A B ha hb
    exact support A ha B (of_decide_eq_true hb)
  · change 4 * (1 + ∑ A, ∑ B, if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧
        B.val.card % 2 = 1 then (edge A B).toNat else 0) ≤ budget
    have h (A : AxisSubset d i) :
        (∑ B : AxisSubset d i, if A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧
          B.val.card % 2 = 1 then (edge A B).toNat else 0) =
        if A ≠ axisTop i ∧ A.val.card % 2 = 1 then
          ((row A).filter fun B => B.val.card % 2 = 1).card else 0 := by
      by_cases active : A ≠ axisTop i ∧ A.val.card % 2 = 1
      · rw [ite_eq_left active]
        calc
          _ = ∑ B : AxisSubset d i,
              if B.val.card % 2 = 1 then (decide (B ∈ row A)).toNat else 0 := by
            apply sum_congr rfl
            intro B _
            by_cases odd : B.val.card % 2 = 1
            · rw [ite_eq_left ⟨active.1, active.2, odd⟩, ite_eq_left odd]
            · have off : ¬ (A ≠ axisTop i ∧ A.val.card % 2 = 1 ∧ B.val.card % 2 = 1) :=
                fun h => odd h.2.2
              rw [ite_eq_right off, ite_eq_right odd]
          _ = _ := sum_sparse_cost (row A) (fun B : AxisSubset d i => B.val.card % 2 = 1)
      · rw [ite_eq_right active]
        simp [← and_assoc, active]
    simpa only [h] using budgetScore
  · intro a b
    exact decide_eq_true_iff

end SparseAxisFactor

open SparseAxisFactor
open AxisMaskTransport

private theorem masked_axis_factor {n k budget : ℕ}
    (row col : Fin (2 ^ n) → Finset (Fin (2 ^ n))) (marked : Bool)
    (top : Fin (2 ^ n)) (topWeight : top.val = 2 ^ n - 1)
    (ends : top ∉ row top)
    (mode : marked = false → 3 ≤ k)
    (agree : ∀ a b, b ∈ row a ↔ a ∈ col b)
    (rowDegree : ∀ a, residualDegree k marked (decide (a = top)) (row a).card)
    (colDegree : ∀ b, residualDegree k marked (decide (b = top)) (col b).card)
    (support : ∀ a ≠ top, ∀ b ∈ row a, a.val &&& b.val = a.val)
    (cost : 4 * (1 + ∑ a, if a ≠ top ∧ weight n a % 2 = 1 then
      ((row a).filter fun (b : Fin (2 ^ n)) => weight n b.val % 2 = 1).card else 0) ≤ budget) :
    MaskedFactorWithRows k (0 : Fin (n + 1)) budget
      (fun a b => (maskEquiv n).symm b ∈ row ((maskEquiv n).symm a)) := by
  let E := maskEquiv n
  have ht : E top = axisTop 0 := mask_top n top topWeight
  let mapped (f : Fin (2 ^ n) → Finset (Fin (2 ^ n))) (a : AxisSubset (n + 1) 0) :=
    (f (E.symm a)).map E.toEmbedding
  have hm (f : Fin (2 ^ n) → Finset (Fin (2 ^ n))) (a b : Fin (2 ^ n)) :
      E b ∈ mapped f (E a) ↔ b ∈ f a := by
    simp [mapped, E]
  have mappedScore (a : Fin (2 ^ n)) :
      ((mapped row (E a)).filter fun B => B.val.card % 2 = 1).card =
        ((row a).filter fun (b : Fin (2 ^ n)) => weight n b.val % 2 = 1).card := by
    have heq : (mapped row (E a)).filter (fun B => B.val.card % 2 = 1) =
      (((row a).filter fun (b : Fin (2 ^ n)) => weight n b.val % 2 = 1).map E.toEmbedding) := by
      ext B
      obtain ⟨b, rfl⟩ := E.surjective B
      simp [hm, E, mask_rank]
    rw [heq, card_map]
  have hFactor : MaskedFactorWithRows k (0 : Fin (n + 1)) budget
      (fun a b => b ∈ mapped row a) := by
    apply of_sparse_rows_and_columns 0 k budget (mapped row) (mapped col) marked
    · rw [← ht]
      exact fun h => ends ((hm row top top).mp h)
    · exact mode
    · intro A B
      obtain ⟨a, rfl⟩ := E.surjective A
      obtain ⟨b, rfl⟩ := E.surjective B
      rw [hm row a b, hm col b a]
      exact agree a b
    · intro A
      obtain ⟨a, rfl⟩ := E.surjective A
      simpa [← ht, E.injective.eq_iff, mapped] using rowDegree a
    · intro B
      obtain ⟨b, rfl⟩ := E.surjective B
      simpa [← ht, E.injective.eq_iff, mapped] using colDegree b
    · intro A hA B hB
      obtain ⟨a, rfl⟩ := E.surjective A
      obtain ⟨b, rfl⟩ := E.surjective B
      rw [← ht, E.injective.ne_iff] at hA
      exact (mask_order a b).mpr (support a hA b ((hm row a b).mp hB))
    · let score (A : AxisSubset (n + 1) 0) :=
        if A ≠ axisTop 0 ∧ A.val.card % 2 = 1 then
          ((mapped row A).filter fun B => B.val.card % 2 = 1).card else 0
      change 4 * (1 + ∑ A, score A) ≤ budget
      rw [← E.sum_comp score]
      simpa only [score, ← ht, E.injective.ne_iff, E, mask_rank, mappedScore] using cost
  rcases hFactor with ⟨f, selected, loop, mode', rows, cols, support', charge', read⟩
  refine ⟨f, selected, loop, mode', rows, cols, support', charge', ?_⟩
  intro a b
  obtain ⟨va, rfl⟩ := E.surjective a
  obtain ⟨vb, rfl⟩ := E.surjective b
  simpa only [E, Equiv.symm_apply_apply] using (read (E va) (E vb)).trans (hm row va vb)

namespace ListBridge

private def boundedFinset {limit : ℕ} (entries : List ℕ)
    (bound : ∀ i ∈ entries, i < limit) : Finset (Fin limit) :=
  entries.toFinset.attachFin (fun i hi => bound i (List.mem_toFinset.mp hi))

private theorem mem_boundedFinset {limit : ℕ} (entries : List ℕ)
    (bound : ∀ i ∈ entries, i < limit) (i : Fin limit) :
    i ∈ boundedFinset entries bound ↔ i.val ∈ entries := by
  simp [boundedFinset, Finset.mem_attachFin]

private theorem card_boundedFinset {limit : ℕ} (entries : List ℕ)
    (bound : ∀ i ∈ entries, i < limit) (nodup : entries.Nodup) :
    (boundedFinset entries bound).card = entries.length := by
  rw [boundedFinset, Finset.card_attachFin, List.toFinset_card_of_nodup nodup]

private theorem count_boundedFinset {limit : ℕ} (entries : List ℕ)
    (bound : ∀ i ∈ entries, i < limit) (nodup : entries.Nodup)
    (charged : ℕ → Bool) :
    ((boundedFinset entries bound).filter (fun i => charged i.val)).card =
      entries.countP charged := by
  have heq : (boundedFinset entries bound).filter (fun i => charged i.val) =
      boundedFinset (entries.filter charged) (fun i hi => bound i (List.mem_filter.mp hi).1) := by
    ext i
    simp [mem_boundedFinset]
  rw [heq, card_boundedFinset _ _ (nodup.filter _)]
  exact List.countP_eq_length_filter.symm

/-- Matching bounded lists certify the degrees, support, charge and exact incidence of a factor. -/
theorem list_axis_factor {n : ℕ} (row col : Fin (2 ^ n) → List ℕ) (budget : ℕ)
    (top : Fin (2 ^ n)) (topValue : top.val = 2 ^ n - 1)
    (noTopLoop : top.val ∉ row top)
    (rowBound : ∀ a w, w ∈ row a → w < 2 ^ n)
    (colBound : ∀ b w, w ∈ col b → w < 2 ^ n)
    (rowNodup : ∀ a, (row a).Nodup)
    (colNodup : ∀ b, (col b).Nodup)
    (agree : ∀ a b, b.val ∈ row a ↔ a.val ∈ col b)
    (rowDegree : ∀ a, residualDegree 3 true (decide (a = top)) (row a).length)
    (colDegree : ∀ b, residualDegree 3 true (decide (b = top)) (col b).length)
    (support : ∀ a ≠ top, ∀ w ∈ row a, a.val &&& w = a.val)
    (budgetScore : 4 * (1 + ∑ a, if a ≠ top ∧ weight n a % 2 = 1 then
      (row a).countP (fun w => weight n w % 2 == 1) else 0) ≤ budget) :
    MaskedFactorWithRows 3 (0 : Fin (n + 1)) budget
      (fun a b => ((maskEquiv n).symm b).val ∈ row ((maskEquiv n).symm a)) := by
  let rowSet (a : Fin (2 ^ n)) := boundedFinset (row a) (rowBound a)
  let colSet (a : Fin (2 ^ n)) := boundedFinset (col a) (colBound a)
  have hFactor : MaskedFactorWithRows 3 (0 : Fin (n + 1)) budget
      (fun a b => (maskEquiv n).symm b ∈ rowSet ((maskEquiv n).symm a)) := by
    apply masked_axis_factor rowSet colSet true top
    · exact topValue
    · simpa [rowSet, mem_boundedFinset] using noTopLoop
    · decide
    · intro a b
      simpa [rowSet, colSet, mem_boundedFinset] using agree a b
    · intro a
      simpa [rowSet, card_boundedFinset, rowNodup] using rowDegree a
    · intro b
      simpa [colSet, card_boundedFinset, colNodup] using colDegree b
    · intro a ha b hb
      exact support a ha b ((mem_boundedFinset _ _ _).mp hb)
    · have costs (a : Fin (2 ^ n)) :
          ((rowSet a).filter (fun b => weight n b.val % 2 = 1)).card =
            (row a).countP (fun w => weight n w % 2 == 1) := by
        simpa only [beq_iff_eq] using
          count_boundedFinset (row a) (rowBound a) (rowNodup a) (fun w => weight n w % 2 == 1)
      simpa only [costs] using budgetScore
  rcases hFactor with ⟨f, selected, loop, mode, rows, cols, support', charge', read⟩
  refine ⟨f, selected, loop, mode, rows, cols, support', charge', ?_⟩
  intro a b
  exact (read a b).trans (mem_boundedFinset _ _ _)

end ListBridge

end D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
