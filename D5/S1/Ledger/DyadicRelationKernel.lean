/- GID: D5/S1/Ledger/DyadicRelationKernel
   generality: G
   mirror-B: D5/B/S1/Ledger/DyadicRelationKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic adjacent rows have an exact evaluation kernel and full finite projections. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
namespace D5.S1.Ledger.DyadicRelationKernel
noncomputable section

/-- The group of finitely supported integer coordinate vectors. -/
abbrev V := ℕ →₀ ℤ
/-- The coordinate vector with coefficient one at index `n`. -/
def eps (n : ℕ) : V := Finsupp.single n 1
/-- The adjacent relation between a coordinate and twice its successor. -/
def row (n : ℕ) : V := eps n - (2 : ℤ) • eps (n + 1)
/-- The integer span of the adjacent relations. -/
def H : Submodule ℤ V := Submodule.span ℤ (Set.range row)
/-- Evaluation with reciprocal powers of two as coordinate weights. -/
def ell (u : V) : ℚ := u.sum (fun n z => (z : ℚ) / (2 : ℚ) ^ n)
/-- The endpoint difference between indices `j` and `m`. -/
def t (j m : ℕ) : V := eps j - (2 : ℤ) ^ (m - j) • eps m
/-- The additive subgroup of rational numbers with a power of two as denominator. -/
def Dyadic : AddSubgroup ℚ where
  carrier := {q | ∃ k : ℕ, ∃ z : ℤ, q = (z : ℚ) / (2 : ℚ) ^ k}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, z, rfl⟩ ⟨l, w, rfl⟩
    refine ⟨k + l, z * 2 ^ l + w * 2 ^ k, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  neg_mem' := by
    rintro a ⟨k, z, rfl⟩
    exact ⟨k, -z, by simp [neg_div]⟩

/-- Evaluation as an additive homomorphism into the dyadic rational numbers. -/
def ellDy : V →+ Dyadic where
  toFun u := ⟨ell u, by
    unfold ell Finsupp.sum
    apply Dyadic.sum_mem
    intro n hn
    exact ⟨n, u n, rfl⟩⟩
  map_zero' := Subtype.ext (by simp [ell])
  map_add' v w := by
    apply Subtype.ext
    change ell (v + w) = ell v + ell w
    exact Finsupp.sum_add_index' (by simp) (by intros; simp [Int.cast_add, add_div])

/-- The telescoping row from index `j` to index `m` belongs to the adjacent-row span. -/
theorem telescoping_mem (j d : ℕ) : t j (j + d) ∈ H := by
  let p : ℕ → Prop := fun d => t j (j + d) ∈ H
  have hp : p 0 := by simp [p, t, H]
  have hs : ∀ d, p d → p (d + 1) := by
    intro d ih
    change t j (j + d) ∈ H at ih
    change t j (j + (d + 1)) ∈ H
    rw [show t j (j + (d + 1)) = t j (j + d) + (2 : ℤ) ^ d • row (j + d) by
      simp [t, row, eps, sub_eq_add_neg, smul_add, add_assoc, add_left_comm,
        pow_succ]]
    exact H.add_mem ih (H.smul_mem _ (Submodule.subset_span ⟨j + d, rfl⟩))
  exact Nat.rec hp (fun d ih => hs d ih) d

/-- A vector supported at or below `m` is the sum of its lower telescoping rows and
an integer endpoint coefficient equal to `2^m` times its dyadic evaluation. -/
theorem support_bounded_decomposition (u : V) (m : ℕ)
    (h : u.support ⊆ Finset.range (m + 1)) :
    ∃ z : ℤ, (z : ℚ) = (2 : ℚ) ^ m * (ellDy u : ℚ) ∧
      u = (∑ j ∈ Finset.range m, u j • t j m) + z • eps m := by
  classical
  let z : ℤ := ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ (m - j) * u j
  refine ⟨z, ?_, ?_⟩
  · change (z : ℚ) = (2 : ℚ) ^ m * ell u
    rw [ell, Finsupp.sum_of_support_subset _ h _ (by simp)]
    simp only [z, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [pow_sub₀ (2 : ℚ) (by norm_num) hjm]
    ring
  ext n
  by_cases hn : n < m
  · have hnm : n ∈ Finset.range m := Finset.mem_range.mpr hn
    have hsum : Finset.sum (Finset.range m) (fun j => (u j • t j m) n) = (u n • t n m) n := by
      apply Finset.sum_eq_single_of_mem n hnm
      intro b hb hbn
      simp [t, eps, Finsupp.single_apply, hbn, Nat.ne_of_lt hn]
    have hsum_eval : (Finset.sum (Finset.range m) (fun j => u j • t j m)) n = (u n • t n m) n := by
      calc
        (Finset.sum (Finset.range m) (fun j => u j • t j m)) n =
            (Finset.sum (Finset.range m) (fun j => fun x => (u j • t j m) x)) n :=
          congrFun (Finsupp.coe_finset_sum (Finset.range m) (fun j => u j • t j m)) n
        _ = Finset.sum (Finset.range m) (fun j => (u j • t j m) n) := by
          exact Finset.sum_apply n (Finset.range m) (fun j => fun x => (u j • t j m) x)
        _ = (u n • t n m) n := hsum
    simp only [Finsupp.add_apply, Finsupp.smul_apply]
    rw [hsum_eval]
    simp [t, eps, Finsupp.single_apply, hn, Nat.ne_of_lt hn]
  · by_cases hnm : n = m
    · subst n
      simp [Finset.sum_apply, t, eps, Finsupp.single_apply, z,
        Finset.sum_range_succ, Finset.mem_range]
      have hif : (Finset.sum (Finset.range m) (fun x => u x * if x = m then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxm : x ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hx)
        simp [hxm]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [hif]
      have hrev : (Finset.sum (Finset.range m) (fun x => u x * 2 ^ (m - x))) =
          Finset.sum (Finset.range m) (fun x => 2 ^ (m - x) * u x) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hrev]
      ring
    · have hgt : m < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm hnm)
      have hzero : u n = 0 := by
        by_contra hz
        have hs : n ∈ u.support := by simpa [Finsupp.mem_support_iff, hz]
        have hlt := Finset.mem_range.mp (h hs)
        omega
      simp [Finset.sum_apply, t, eps, Finsupp.single_apply, hzero, Nat.ne_of_gt hgt]

/-- A vector lies in the span of the adjacent relations exactly when
its dyadic evaluation is zero. -/
theorem mem_H_iff_ellDy_eq_zero (u : V) : u ∈ H ↔ ellDy u = 0 := by
  classical
  let f : V →+ ℚ := Dyadic.subtype.comp ellDy
  have heps (n : ℕ) : f (eps n) = 1 / (2 : ℚ) ^ n := by
    change ell (eps n) = _
    simp [ell, eps]
  have hH (v : V) (hv : v ∈ H) : f v = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨n, rfl⟩ := hv
      simp only [row, map_sub, map_zsmul, heps, zsmul_eq_mul, Int.cast_ofNat]
      rw [pow_succ]
      field_simp
      ring
    | zero => exact f.map_zero
    | add v w hv hw ihv ihw => simp [map_add, ihv, ihw]
    | smul a v hv ih => simp only [map_zsmul, ih, smul_zero]
  constructor
  · intro hu
    exact Subtype.ext (hH u hu)
  · intro hu
    let m := u.support.sup id
    have hm : u.support ⊆ Finset.range (m + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hs : (∑ j ∈ Finset.range m, u j • t j m) ∈ H := by
      apply H.sum_mem
      intro j hj
      apply H.smul_mem
      have hjm := Nat.le_of_lt (Finset.mem_range.mp hj)
      simpa only [Nat.add_sub_of_le hjm] using telescoping_mem j (m - j)
    obtain ⟨z, hz, hd⟩ := support_bounded_decomposition u m hm
    have hw : z = 0 := by
      have hc : (z : ℚ) = 0 := by simpa only [hu, AddSubgroup.coe_zero, mul_zero] using hz
      exact_mod_cast hc
    rw [hd, hw, zero_smul, add_zero]
    exact hs

/-- Restriction of the adjacent-row span to any finite coordinate set is surjective. -/
theorem finite_projection_surjective (I : Finset ℕ) :
    Function.Surjective (fun v : H => fun i : I => (v : V) i) := by
  classical
  intro a
  let m := I.sup id + 1
  have hm (i : I) : (i : ℕ) < m :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
  let v : V := ∑ j : I, a j • t j m
  have hv : v ∈ H := by
    apply H.sum_mem
    intro j hj
    apply H.smul_mem
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt (hm j))] using
      telescoping_mem j (m - j)
  refine ⟨⟨v, hv⟩, ?_⟩
  funext i
  change v i = a i
  rw [show v i = ∑ j : I, (a j • t j m) i by exact Finsupp.finsetSum_apply _ _ _]
  rw [Finset.sum_eq_single i]
  · simp [t, eps, (hm i).ne]
  · intro j hj hji
    have hji' : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Subtype.ext h)
    simp [t, eps, hji', (hm i).ne']
  · simp

end
end D5.S1.Ledger.DyadicRelationKernel
