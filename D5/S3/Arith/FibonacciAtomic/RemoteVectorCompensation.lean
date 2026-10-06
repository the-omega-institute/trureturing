/- GID: D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RemoteVectorCompensation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A single finite legal source realizes every prefix and remote two-coordinate residue. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
import Mathlib.Algebra.BigOperators.Finprod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.RemoteVectorCompensation

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step atomicBlock residue)
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.WindowSuccessorGraph (X P)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel (finiteTail)

/-- The sum of the actual Fibonacci block vectors at occupied source addresses.
For an eventually zero address this is a finite sum in the nonnegative lattice,
whose inclusion into the integer lattice preserves both coordinates. -/
noncomputable def sourceComposition (b : LegalDigits) : ℕ × ℕ :=
  ∑ᶠ j : ℕ, if b.val j then atomicBlock j else 0

private theorem residue_atomicBlock (m j : ℕ) :
    residue m (atomicBlock j) = step^[j] (1, 0) := by
  have h : Function.Semiconj (residue m) step step := by
    intro v
    ext <;> simp [residue, step]
  simpa [atomicBlock, residue] using h.iterate_right j (1, 0)

private theorem period_multiple (m : ℕ) (hm : 0 < m) :
    ∃ T : ℕ, 3 ≤ T ∧ ∀ (k : ℕ) (v : ZMod m × ZMod m), step^[T * k] v = v := by
  let Q := (m ^ 2).factorial
  have hQ : 0 < Q := Nat.factorial_pos _
  have hperiod : ∀ v : ZMod m × ZMod m, step^[Q] v = v :=
    (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2 m hm (1, 0)).2.1
  have hid : (step^[Q] : (ZMod m × ZMod m) → ZMod m × ZMod m) = id :=
    funext hperiod
  refine ⟨Q * 3, by omega, ?_⟩
  intro k v
  rw [Nat.mul_assoc, Function.iterate_mul, hid]
  simp

private theorem remote_support (m : ℕ) (hm : 0 < m) (T N : ℕ)
    (hT : 3 ≤ T) (hperiod : ∀ (k : ℕ) (v : ZMod m × ZMod m), step^[T * k] v = v)
    (hN : T ∣ N) (r : ZMod m × ZMod m) :
    ∃ s : Finset ℕ,
      (∀ j ∈ s, N ≤ j) ∧
      (∀ j ∈ s, j + 1 ∉ s) ∧
      (∑ j ∈ s, residue m (atomicBlock j)) = r ∧ s.Nonempty := by
  classical
  have : NeZero m := ⟨by omega⟩
  obtain ⟨n, rfl⟩ := hN
  let A := r.1.val + m
  let C := r.2.val
  let f : ℕ → ℕ := fun i => T * n + i * T + if i < A then 0 else 1
  have separated (i j : ℕ) (hij : i < j) : f i + 2 ≤ f j := by
    have hh := Nat.mul_le_mul_right T (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, one_mul] at hh
    dsimp [f]
    split_ifs <;> omega
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have := separated i j hij
      omega
    · have := separated j i hji
      omega
  let s := (Finset.range (A + C)).image f
  have hfirst (i : ℕ) (hi : i < A) :
      residue m (atomicBlock (f i)) = (1, 0) := by
    have he : f i = T * (n + i) := by simp [f, hi]; ring
    rw [he, residue_atomicBlock, hperiod]
  have hsecond (j : ℕ) : residue m (atomicBlock (f (A + j))) = (0, 1) := by
    have he : f (A + j) = T * (n + (A + j)) + 1 := by simp [f]; ring
    rw [he, residue_atomicBlock, Function.iterate_add_apply, hperiod]
    simp [step]
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    dsimp [f]
    omega
  · intro j hj hj1
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj1
    rcases lt_trichotomy i k with hik | hik | hki
    · have := separated i k hik
      omega
    · subst k
      omega
    · have := separated k i hki
      omega
  · change (∑ j ∈ (Finset.range (A + C)).image f, residue m (atomicBlock j)) = r
    rw [Finset.sum_image (fun i _ j _ he => hinj he), Finset.sum_range_add]
    have ha : (∑ i ∈ Finset.range A, residue m (atomicBlock (f i))) =
        A • ((1, 0) : ZMod m × ZMod m) := by
      rw [Finset.sum_congr rfl (fun i hi => hfirst i (Finset.mem_range.mp hi))]
      simp
    have hc : (∑ j ∈ Finset.range C, residue m (atomicBlock (f (A + j)))) =
        C • ((0, 1) : ZMod m × ZMod m) := by
      simp_rw [hsecond]
      simp
    rw [ha, hc]
    ext <;> simp [A, C, nsmul_eq_mul]
  · refine ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr ?_, rfl⟩⟩
    dsimp [A]
    omega

/-- Every legal low prefix and every complete residue vector have a common
eventually zero legal realization. All new occupied positions lie beyond the
prescribed bound, and at least one such position is occupied. -/
theorem result (L : ℕ) (p : X L) (m : ℕ) (hm : 0 < m)
    (r : ZMod m × ZMod m) (B : ℕ) :
    ∃ b : LegalDigits, finiteTail b ∧ P L b = p ∧
      residue m (sourceComposition b) = r ∧
      (∀ j : ℕ, L ≤ j → b.val j = true → B < j) ∧
      (∃ j : ℕ, L ≤ j ∧ B < j ∧ b.val j = true) := by
  classical
  obtain ⟨T, hT, hperiod⟩ := period_multiple m hm
  let N := T * (L + B + 1)
  have hNL : L + 1 ≤ N := by
    have := Nat.mul_le_mul_right (L + B + 1) (show 1 ≤ T by omega)
    dsimp [N]
    omega
  have hNB : B < N := by
    have := Nat.mul_le_mul_right (L + B + 1) (show 1 ≤ T by omega)
    dsimp [N]
    omega
  let u : Finset ℕ := ((Finset.univ : Finset (Fin L)).filter
    (fun i => p.val i = true)).image Fin.val
  have hu (j : ℕ) : j ∈ u ↔ ∃ h : j < L, p.val ⟨j, h⟩ = true := by
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i.isLt, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨h, hj⟩
      exact Finset.mem_image.mpr ⟨⟨j, h⟩, Finset.mem_filter.mpr ⟨by simp, hj⟩, rfl⟩
  let v := ∑ j ∈ u, residue m (atomicBlock j)
  obtain ⟨s, hsN, hssep, hsum, hsne⟩ := remote_support m hm T N hT hperiod
    ⟨L + B + 1, rfl⟩ (r - v)
  have hdisj : Disjoint u s := by
    apply Finset.disjoint_left.mpr
    intro j hju hjs
    obtain ⟨hj, _⟩ := (hu j).mp hju
    have := hsN j hjs
    omega
  let b : LegalDigits := ⟨fun j => decide (j ∈ u ∪ s), by
    intro j hj
    simp only [decide_eq_true_eq, Finset.mem_union] at hj
    rcases hj with ⟨hju | hjs, hj1u | hj1s⟩
    · obtain ⟨hjuL, hpu⟩ := (hu j).mp hju
      obtain ⟨hj1uL, hpu1⟩ := (hu (j + 1)).mp hj1u
      exact p.property j hj1uL ⟨hpu, hpu1⟩
    · obtain ⟨hjuL, _⟩ := (hu j).mp hju
      have := hsN (j + 1) hj1s
      omega
    · obtain ⟨hj1uL, _⟩ := (hu (j + 1)).mp hj1u
      have := hsN j hjs
      omega
    · exact hssep j hjs hj1s⟩
  have hfinite : finiteTail b := by
    obtain ⟨K, hK⟩ := Finset.exists_nat_subset_range (u ∪ s)
    refine ⟨K, ?_⟩
    intro j hj
    have hnot : j ∉ u ∪ s := by
      intro hjS
      have := Finset.mem_range.mp (hK hjS)
      omega
    simp [b, hnot]
  have hprefix : P L b = p := by
    apply Subtype.ext
    funext i
    change decide (i.val ∈ u ∪ s) = p.val i
    have hnot : i.val ∉ s := by
      intro hi
      have := hsN i.val hi
      have := i.isLt
      omega
    simp only [Finset.mem_union, hnot, or_false]
    have he : i.val ∈ u ↔ p.val i = true := by
      simp [hu, i.isLt]
    simp [he]
  have hcomposition : sourceComposition b = ∑ j ∈ u ∪ s, atomicBlock j := by
    rw [sourceComposition, finsum_eq_sum_of_support_subset _ (s := u ∪ s)]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [b, hj]
    · intro j hj
      by_contra hnot
      have hnot' : j ∉ u ∪ s := hnot
      have hz : (if b.val j then atomicBlock j else (0 : ℕ × ℕ)) = 0 := by
        simp only [b, decide_eq_true_eq, if_neg hnot']
      exact hj hz
  have hresidue : residue m (sourceComposition b) = r := by
    rw [hcomposition]
    have cast_sum (q : Finset ℕ) :
        residue m (∑ j ∈ q, atomicBlock j) = ∑ j ∈ q, residue m (atomicBlock j) := by
      let h : (ℕ × ℕ) →+ (ZMod m × ZMod m) :=
        (Nat.castAddMonoidHom (ZMod m)).prodMap (Nat.castAddMonoidHom (ZMod m))
      exact map_sum h (fun j => atomicBlock j) q
    rw [cast_sum, Finset.sum_union hdisj, hsum]
    change v + (r - v) = r
    abel
  have hremote (j : ℕ) (hj : L ≤ j) (hb : b.val j = true) : B < j := by
    have hjS : j ∈ u ∪ s := by simpa [b] using hb
    rcases Finset.mem_union.mp hjS with hju | hjs
    · obtain ⟨hjuL, _⟩ := (hu j).mp hju
      omega
    · have := hsN j hjs
      omega
  refine ⟨b, hfinite, hprefix, hresidue, hremote, ?_⟩
  obtain ⟨j, hj⟩ := hsne
  have := hsN j hj
  refine ⟨j, by omega, by omega, ?_⟩
  simp [b, Finset.mem_union.mpr (Or.inr hj)]

end D5.S3.Arith.FibonacciAtomic.RemoteVectorCompensation
