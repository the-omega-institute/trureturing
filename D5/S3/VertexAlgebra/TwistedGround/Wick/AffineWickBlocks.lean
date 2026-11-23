/- GID: D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure correction Wick factors over independent covariance blocks. -/

import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution

/-! Corrections supported within separate blocks factor into the
pure Wick evaluation of each ordered subword. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.AffineWickBlocks

open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions wick_add_covariance)

variable {X : Type*}

/-- Wick evaluation only uses entries whose endpoints occur in the word. -/
theorem wick_congr_on (A B : Matrix X X ℂ) (μ : X → ℂ) (l : List X)
    (h : ∀ a ∈ l, ∀ b ∈ l, A a b = B a b) :
    wick A μ l = wick B μ l := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [wick]
    | cons a l =>
      simp only [wick]
      rw [ih l (Nat.lt_succ_self _) (fun i hi j hj =>
        h i (List.mem_cons_of_mem a hi) j (List.mem_cons_of_mem a hj))]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [h a List.mem_cons_self _ (List.mem_cons_of_mem a (List.get_mem _ _)),
        ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))]
      intro i hi b hb
      exact h i (List.mem_cons_of_mem a ((List.eraseIdx_sublist ..).subset hi))
        b (List.mem_cons_of_mem a ((List.eraseIdx_sublist ..).subset hb))

private def restrict (A : Matrix X X ℂ) (p : X → Bool) : Matrix X X ℂ :=
  Matrix.of fun a b => if p a && p b then A a b else 0

private theorem restrict_eq_zero (A : Matrix X X ℂ) (p : X → Bool)
    (l : List X) (a : X) (ha : a ∈ l) (hp : p a = false) :
    wick (restrict A p) 0 l = 0 := by
  induction l using WellFounded.induction (measure List.length).wf generalizing a with
  | h l ih =>
    cases l with
    | nil => simp at ha
    | cons b l =>
      simp only [wick, Pi.zero_apply, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hb : p b = false
      · simp [restrict, hb]
      by_cases hj : p (l.get j) = false
      · simp [restrict, show p l[(j : ℕ)] = false from hj]
      obtain h | h := List.mem_cons.mp ha
      · exact (hb (h ▸ hp)).elim
      have ht : a ∈ l.eraseIdx j := by
        obtain ⟨k, hk⟩ := List.get_of_mem h
        have hkj : (k : ℕ) ≠ (j : ℕ) := by
          intro he
          have he' : k = j := Fin.ext he
          exact hj (he' ▸ (hk ▸ hp))
        exact List.mem_eraseIdx_iff_getElem.mpr ⟨k, k.isLt, hkj, hk⟩
      rw [ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..)) a ht hp,
        mul_zero]

private theorem sum_valid_partition (p : X → Bool) (l : List X) (H : List X × List X → ℂ) :
    (open Classical in ((partitions l).map fun s =>
      if (∀ a ∈ s.1, p a = true) ∧ (∀ a ∈ s.2, p a = false) then H s else 0).sum) =
      H (l.filter p, l.filter fun a => !p a) := by
  classical
  induction l generalizing H with
  | nil => simp [partitions]
  | cons a l ih =>
    cases h : p a <;>
      simp [partitions, List.map_map, Function.comp_def, h, ih]

/-- A block-diagonal covariance with no singleton term factors along the
two ordered words picked by the block predicate. -/
theorem wick_block [Finite X] (A : Matrix X X ℂ) (p : X → Bool)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i j, p i ≠ p j → A i j = 0)
    (l : List X) :
    wick A 0 l = wick A 0 (l.filter p) * wick A 0 (l.filter fun a => !p a) := by
  classical
  let C := restrict A p
  let N := restrict A (fun a => !p a)
  have he : N + C = A := by
    ext i j
    by_cases h : p i = p j
    · cases hi : p i <;> simp [N, C, restrict, ← h, hi]
    · have hzero := hz i j h
      simp [Matrix.add_apply, N, C, restrict, hzero]
  have hC (i j : X) : C i j = C j i := by
    simp only [C, restrict, Matrix.of_apply, Bool.and_comm (p i) (p j), hs i j]
  have hN (i j : X) : N i j = N j i := by
    simp only [N, restrict, Matrix.of_apply, Bool.and_comm (!p i) (!p j), hs i j]
  rw [← he, wick_add_covariance N C 0 hN hC, he]
  calc
    _ = ((partitions l).map fun s =>
      if (∀ a ∈ s.1, p a = true) ∧ (∀ a ∈ s.2, p a = false) then
        wick A 0 s.1 * wick A 0 s.2 else 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro s _
      by_cases h₁ : ∀ a ∈ s.1, p a = true
      · by_cases h₂ : ∀ a ∈ s.2, p a = false
        · rw [if_pos ⟨h₁, h₂⟩]
          rw [wick_congr_on C A 0 _ (fun i hi j hj => by simp [C, restrict, h₁ i hi, h₁ j hj]),
            wick_congr_on N A 0 _ (fun i hi j hj => by simp [N, restrict, h₂ i hi, h₂ j hj])]
        · push_neg at h₂
          obtain ⟨a, ha, hpa⟩ := h₂
          have hzero := restrict_eq_zero A (fun a => !p a) s.2 a ha (by simpa using hpa)
          simp [N, hzero, show ¬ (∀ b ∈ s.2, p b = false) from
            fun h => hpa (h a ha)]
      · push_neg at h₁
        obtain ⟨a, ha, hpa⟩ := h₁
        have hzero := restrict_eq_zero A p s.1 a ha (by simpa using hpa)
        simp [C, hzero, show ¬ (∀ b ∈ s.1, p b = true) from fun h => hpa (h a ha)]
    _ = _ := sum_valid_partition p l (fun s => wick A 0 s.1 * wick A 0 s.2)

/-- Each block of a finite partition contributes independently, in the
order induced by the original occurrence word. -/
theorem wick_blocks [Finite X] {S : Type*} [DecidableEq S]
    (A : Matrix X X ℂ) (slot : X → S)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i j, slot i ≠ slot j → A i j = 0)
    (blocks : Finset S) (l : List X) (hl : ∀ a ∈ l, slot a ∈ blocks) :
    wick A 0 l = ∏ i ∈ blocks, wick A 0 (l.filter fun a => decide (slot a = i)) := by
  induction blocks using Finset.induction_on generalizing l with
  | empty =>
    cases l with
    | nil => simp [wick]
    | cons a l => exact (Finset.notMem_empty (slot a) (hl a List.mem_cons_self)).elim
  | insert i blocks hi ih =>
    rw [Finset.prod_insert hi, wick_block A (fun a => decide (slot a = i)) hs
      (fun a b hab => hz a b (fun e => hab (by simp [e]))) l]
    congr 1
    rw [ih _ (fun a ha => by
      have he := List.mem_filter.mp ha
      exact (Finset.mem_insert.mp (hl a he.1)).resolve_left (by simpa using he.2))]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    by_cases ha : slot a = j
    · have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp [ha, hji]
    · simp [ha]

end D5.S3.VertexAlgebra.TwistedGround.AffineWickBlocks
