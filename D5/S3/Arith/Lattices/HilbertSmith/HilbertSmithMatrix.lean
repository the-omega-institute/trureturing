/- GID: D5/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/HilbertSmith/HilbertSmithMatrix
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exact determinantal divisors and positive Smith factors of the integer Hilbert matrix. -/

import D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
import D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
import D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Positivity

/-! # Determinantal divisors of the unshifted integer Hilbert matrix -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix

open Finset CauchyDeterminant DivisorFormula MinorValuation NestedResidueMatching
open scoped BigOperators

section Products

private theorem prod_orderEmbOfFin {R : Type*} [CommMonoid R] {k : ℕ} (I : Finset ℕ)
    (hI : I.card = k) (f : ℕ → R) :
    (∏ i, f (I.orderEmbOfFin hI i)) = ∏ a ∈ I, f a := by
  calc
    _ = (univ.map (I.orderEmbOfFin hI).toEmbedding).prod f :=
      (Finset.prod_map univ (I.orderEmbOfFin hI).toEmbedding f).symm
    _ = _ := by rw [map_orderEmbOfFin_univ]

private theorem orderedDifferences_enum {k : ℕ} (I : Finset ℕ) (hI : I.card = k) :
    orderedDifferences (fun i => (I.orderEmbOfFin hI i : ℚ)) =
      (positiveDifferences I : ℚ) := by
  let e := I.orderEmbOfFin hI
  have hmap (i : Fin k) : (Ioi i).map e.toEmbedding = I.filter (fun b => e i < b) := by
    have huniv : univ.map e.toEmbedding = I := map_orderEmbOfFin_univ I hI
    rw [← huniv, filter_map]
    apply congrArg (fun s : Finset (Fin k) => s.map e.toEmbedding)
    ext j
    simp only [mem_Ioi, mem_filter, mem_univ, true_and]
    exact e.lt_iff_lt.symm
  have hinner (i : Fin k) :
      (∏ j ∈ Ioi i, ((e j : ℚ) - e i)) =
        ∏ b ∈ I.filter (fun b => e i < b), ((b - e i : ℕ) : ℚ) := by
    rw [← hmap i, Finset.prod_map]
    apply prod_congr rfl
    intro j hj
    exact (Nat.cast_sub (e.strictMono (mem_Ioi.mp hj)).le).symm
  have hfilter : I.offDiag.filter (fun z => z.1 < z.2) =
      (I ×ˢ I).filter (fun z => z.1 < z.2) := by
    ext z
    simp only [mem_filter, mem_offDiag, mem_product]
    exact ⟨fun h => ⟨⟨h.1.1, h.1.2.1⟩, h.2⟩,
      fun h => ⟨⟨h.1.1, h.1.2, h.2.ne⟩, h.2⟩⟩
  change (∏ i, ∏ j ∈ Ioi i, ((e j : ℚ) - e i)) = _
  simp_rw [hinner]
  rw [prod_orderEmbOfFin I hI (fun a => ∏ b ∈ I.filter (fun b => a < b), ((b - a : ℕ) : ℚ)),
    positiveDifferences, hfilter, Nat.cast_prod,
    Finset.prod_filter (s := I ×ˢ I) (fun z => z.1 < z.2) (fun z => ((z.2 - z.1 : ℕ) : ℚ)),
    Finset.prod_product]
  apply prod_congr rfl
  intro a _
  rw [Finset.prod_filter]

private theorem orderedDifferences_enum_add_one {k : ℕ} (J : Finset ℕ) (hJ : J.card = k) :
    orderedDifferences (fun j => (J.orderEmbOfFin hJ j : ℚ) + 1) =
      (positiveDifferences J : ℚ) := by
  simpa only [orderedDifferences, add_sub_add_right_eq_sub] using orderedDifferences_enum J hJ

private theorem cauchyDenominator_enum {k : ℕ} (I J : Finset ℕ)
    (hI : I.card = k) (hJ : J.card = k) :
    cauchyDenominator (fun i => (I.orderEmbOfFin hI i : ℚ))
        (fun j => (J.orderEmbOfFin hJ j : ℚ) + 1) =
      (denominatorProduct I J : ℚ) := by
  rw [cauchyDenominator, denominatorProduct, Nat.cast_prod, Finset.prod_product]
  calc
    _ = ∏ i, ∏ b ∈ J, ((I.orderEmbOfFin hI i : ℚ) + ((b : ℚ) + 1)) := by
      apply prod_congr rfl
      intro i _
      exact prod_orderEmbOfFin J hJ (fun b => (I.orderEmbOfFin hI i : ℚ) + ((b : ℚ) + 1))
    _ = _ := by
      rw [prod_orderEmbOfFin I hI (fun a => ∏ b ∈ J, ((a : ℚ) + ((b : ℚ) + 1)))]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]

end Products

section Minors

/-- The unshifted Hilbert matrix scaled by L, with entries in the integers. -/
def integerHilbert (n L : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((L / (i.val + j.val + 1) : ℕ) : ℤ)

private theorem entryDenominator_dvd {n L : ℕ} (hd : intervalLCM n 1 ∣ L)
    (i j : Fin n) : i.val + j.val + 1 ∣ L := by
  have hi := i.isLt
  have hj := j.isLt
  have hmem : i.val + j.val + 1 ∈ Icc 1 (2 * n - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
  exact (Finset.dvd_lcm (f := id) hmem).trans hd

/-- The actual submatrix with the selected rows and columns in increasing order. -/
noncomputable def integerHilbertMinor {n k : ℕ} (L : ℕ) {I J : Finset ℕ}
    (hI : I ⊆ range n) (hJ : J ⊆ range n) (hIk : I.card = k) (hJk : J.card = k) :
    Matrix (Fin k) (Fin k) ℤ :=
  (integerHilbert n L).submatrix
    (fun i => ⟨I.orderEmbOfFin hIk i, mem_range.mp (hI (orderEmbOfFin_mem I hIk i))⟩)
    (fun j => ⟨J.orderEmbOfFin hJk j, mem_range.mp (hJ (orderEmbOfFin_mem J hJk j))⟩)

/-- The absolute determinant of the selected integer Hilbert minor. -/
noncomputable def integerHilbertMinorAbs {n k : ℕ} (L : ℕ) {I J : Finset ℕ}
    (hI : I ⊆ range n) (hJ : J ⊆ range n) (hIk : I.card = k) (hJk : J.card = k) : ℕ :=
  (integerHilbertMinor L hI hJ hIk hJk).det.natAbs

/-- The actual integer minor determinant is the rational Cauchy product
at any denominator-clearing scale. -/
theorem det_integerHilbertMinor_cast {n k L : ℕ} (hd : intervalLCM n 1 ∣ L)
    {I J : Finset ℕ} (hI : I ⊆ range n) (hJ : J ⊆ range n)
    (hIk : I.card = k) (hJk : J.card = k) :
    ((integerHilbertMinor L hI hJ hIk hJk).det : ℚ) = cauchyMinor L I J := by
  let x : Fin k → ℚ := fun i => I.orderEmbOfFin hIk i
  let y : Fin k → ℚ := fun j => (J.orderEmbOfFin hJk j : ℚ) + 1
  have hs (i j : Fin k) : x i + y j ≠ 0 := by
    dsimp [x, y]
    positivity
  have hsmap : (integerHilbertMinor L hI hJ hIk hJk).map (fun z => (z : ℚ)) =
      (L : ℚ) • cauchyMatrix x y := by
    apply Matrix.ext
    intro i j
    let a : Fin n := ⟨I.orderEmbOfFin hIk i, mem_range.mp (hI (orderEmbOfFin_mem I hIk i))⟩
    let b : Fin n := ⟨J.orderEmbOfFin hJk j, mem_range.mp (hJ (orderEmbOfFin_mem J hJk j))⟩
    change (((L / (a.val + b.val + 1) : ℕ) : ℤ) : ℚ) = (L : ℚ) * (x i + y j)⁻¹
    rw [Int.cast_natCast, Nat.cast_div_charZero (entryDenominator_dvd hd a b)]
    simp only [a, b, x, y, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, add_assoc]
  rw [Int.cast_det, hsmap, Matrix.det_smul, Fintype.card_fin, det_cauchyMatrix x y hs]
  dsimp only [x, y]
  rw [orderedDifferences_enum I hIk, orderedDifferences_enum_add_one J hJk,
    cauchyDenominator_enum I J hIk hJk, cauchyMinor, hIk]
  simp only [div_eq_mul_inv]
  ring

private theorem integerHilbertMinor_natAbs_cast {n k L : ℕ}
    (hL : 0 < L) (hd : intervalLCM n 1 ∣ L)
    {I J : Finset ℕ} (hI : I ⊆ range n) (hJ : J ⊆ range n)
    (hIk : I.card = k) (hJk : J.card = k) :
    (integerHilbertMinorAbs L hI hJ hIk hJk : ℚ) = cauchyMinor L I J := by
  unfold integerHilbertMinorAbs
  have hdet := det_integerHilbertMinor_cast hd hI hJ hIk hJk
  have hpos : 0 < ((integerHilbertMinor L hI hJ hIk hJk).det : ℚ) :=
    hdet.symm ▸ cauchyMinor_pos hL I J
  have hnonneg : 0 ≤ (integerHilbertMinor L hI hJ hIk hJk).det := by exact_mod_cast hpos.le
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnonneg, hdet]

/-- Twice the prime exponent of the absolute determinant of each actual
integer minor, expressed in its prime-power residue layers. -/
theorem integerHilbertMinor_valuation {p n L k : ℕ} (hp : p.Prime) (hL : 0 < L)
    (hd : intervalLCM n 1 ∣ L) {I J : Finset ℕ}
    (hI : I ⊆ range n) (hJ : J ⊆ range n) (hIk : I.card = k) (hJk : J.card = k) :
    2 * (integerHilbertMinorAbs L hI hJ hIk hJk).factorization p =
      2 * k * (L.factorization p - Nat.log p (2 * n - 1)) +
        ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)), residueLoss (p ^ a) I J := by
  have hv := cauchyMinor_valuation hp hL.ne' hI hJ hIk hJk
  rw [← integerHilbertMinor_natAbs_cast hL hd hI hJ hIk hJk, padicValRat.of_nat,
    ← Nat.factorization_def _ hp, ← Nat.cast_sub (height_le_factorization hp hL.ne' hd),
    ← Nat.cast_sum] at hv
  exact_mod_cast hv

/-- All pairs of k-element row and column sets. -/
def minorIndices (n k : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (range n).powersetCard k ×ˢ (range n).powersetCard k

private theorem mem_minorIndices {n k : ℕ} {z : Finset ℕ × Finset ℕ} :
    z ∈ minorIndices n k ↔ (z.1 ⊆ range n ∧ z.1.card = k) ∧
      (z.2 ⊆ range n ∧ z.2.card = k) := by
  simp only [minorIndices, mem_product, mem_powersetCard]

private def squareIndex {n k : ℕ} (hk : k ≤ n) : ↥(minorIndices n k) :=
  ⟨(range k, range k), mem_minorIndices.mpr
    ⟨⟨range_mono hk, card_range k⟩, ⟨range_mono hk, card_range k⟩⟩⟩

private noncomputable def minorWeight {n k : ℕ} (L : ℕ) (z : ↥(minorIndices n k)) : ℕ :=
  let h := mem_minorIndices.mp z.property
  integerHilbertMinorAbs L h.1.1 h.2.1 h.1.2 h.2.2

private theorem minorWeight_ne_zero {n k L : ℕ}
    (hL : 0 < L) (hd : intervalLCM n 1 ∣ L) (z : ↥(minorIndices n k)) :
    minorWeight L z ≠ 0 := by
  obtain ⟨⟨hI, hIk⟩, ⟨hJ, hJk⟩⟩ := mem_minorIndices.mp z.property
  have h : (minorWeight L z : ℚ) = cauchyMinor L z.val.1 z.val.2 :=
    integerHilbertMinor_natAbs_cast hL hd hI hJ hIk hJk
  intro hz
  rw [hz, Nat.cast_zero] at h
  exact (cauchyMinor_pos hL _ _).ne' h.symm

/-- The gcd of the absolute determinants of all actual k by k integer minors. -/
noncomputable def determinantalDivisor (n L k : ℕ) : ℕ :=
  (minorIndices n k).attach.gcd (minorWeight L)

theorem determinantalDivisor_zero (n L : ℕ) : determinantalDivisor n L 0 = 1 := by
  apply Nat.dvd_antisymm _ (one_dvd _)
  let z := squareIndex (n := n) (Nat.zero_le n)
  have hz : minorWeight L z = 1 := by simp [minorWeight, integerHilbertMinorAbs, Matrix.det_isEmpty]
  have h : determinantalDivisor n L 0 ∣ minorWeight L z :=
    Finset.gcd_dvd (f := minorWeight L) (mem_attach _ z)
  rwa [hz] at h

theorem determinantalDivisor_ne_zero {n k L : ℕ} (hk : k ≤ n)
    (hL : 0 < L) (hd : intervalLCM n 1 ∣ L) : determinantalDivisor n L k ≠ 0 := by
  unfold determinantalDivisor
  exact Finset.gcd_ne_zero_iff.mpr
    ⟨squareIndex hk, mem_attach _ _, minorWeight_ne_zero hL hd _⟩

/-- For each prime one actual minor attains the minimum in every layer. -/
theorem exists_integerHilbertMinor_minimizer {p n L k : ℕ} (hp : p.Prime)
    (hL : 0 < L) (hd : intervalLCM n 1 ∣ L) (hk : k ≤ n) :
    ∃ (I J : Finset ℕ) (hI : I ⊆ range n) (hJ : J ⊆ range n)
      (hIk : I.card = k) (hJk : J.card = k),
      (integerHilbertMinorAbs L hI hJ hIk hJk).factorization p =
        divisorExponent p n L k ∧
      ∀ a ≤ Nat.log p (2 * n - 1),
        residueLoss (p ^ a) I J = 2 * (k - commonCapacity n (p ^ a)) := by
  let e := Nat.log p (2 * n - 1)
  obtain ⟨I, hI, J, hJ, hIk, hJk, hopt⟩ := exists_residue_minimizer hp.pos hk e
  refine ⟨I, J, hI, hJ, hIk, hJk, ?_, hopt⟩
  have hval := integerHilbertMinor_valuation hp hL hd hI hJ hIk hJk
  have hsum : (∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J) =
      2 * (∑ a ∈ Icc 1 e, (k - commonCapacity n (p ^ a))) := by
    rw [mul_sum]
    exact sum_congr rfl fun a ha => hopt a (mem_Icc.mp ha).2
  change 2 * _ = 2 * k * (L.factorization p - e) +
    ∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J at hval
  rw [hsum, mul_assoc 2 k, ← mul_add] at hval
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hval

/-- The gcd of the actual minors has the prime exponent attained by the
simultaneous residue minimizer. -/
theorem determinantalDivisor_factorization {p n L k : ℕ} (hp : p.Prime)
    (hL : 0 < L) (hd : intervalLCM n 1 ∣ L) (hk : k ≤ n) :
    (determinantalDivisor n L k).factorization p = divisorExponent p n L k := by
  let e := Nat.log p (2 * n - 1)
  have hmin := residueLoss_sum_minimum hp.pos hk e
  have hval (z : ↥(minorIndices n k)) :
      2 * (minorWeight L z).factorization p =
        2 * k * (L.factorization p - e) +
          ∑ a ∈ Icc 1 e, residueLoss (p ^ a) z.val.1 z.val.2 := by
    obtain ⟨⟨hI, hIk⟩, ⟨hJ, hJk⟩⟩ := mem_minorIndices.mp z.property
    exact integerHilbertMinor_valuation hp hL hd hI hJ hIk hJk
  have hscore : 2 * divisorExponent p n L k =
      2 * k * (L.factorization p - e) +
        2 * (∑ a ∈ Icc 1 e, (k - commonCapacity n (p ^ a))) := by
    change 2 * (k * (L.factorization p - e) + _) = _
    rw [mul_add, mul_assoc]
  have hpow := hp.pow_dvd_iff_le_factorization (determinantalDivisor_ne_zero hk hL hd)
    (k := divisorExponent p n L k)
  apply le_antisymm
  · obtain ⟨I, J, hI, hJ, hIk, hJk, heq, _⟩ :=
      exists_integerHilbertMinor_minimizer hp hL hd hk
    let z : ↥(minorIndices n k) := ⟨(I, J), mem_minorIndices.mpr ⟨⟨hI, hIk⟩, ⟨hJ, hJk⟩⟩⟩
    have hz : determinantalDivisor n L k ∣ minorWeight L z :=
      Finset.gcd_dvd (f := minorWeight L) (mem_attach _ z)
    have hle := (Nat.factorization_le_iff_dvd
      (determinantalDivisor_ne_zero hk hL hd) (minorWeight_ne_zero hL hd z)).mpr hz p
    exact hle.trans_eq heq
  · apply hpow.mp
    unfold determinantalDivisor
    apply Finset.dvd_gcd
    intro z _
    apply (hp.pow_dvd_iff_le_factorization (minorWeight_ne_zero hL hd z)).mpr
    obtain ⟨⟨hI, hIk⟩, ⟨hJ, hJk⟩⟩ := mem_minorIndices.mp z.property
    have hlower := hmin.1 hI hJ hIk hJk
    have hw := hval z
    omega

end Minors

private theorem scale_div_intervalLCM_pos {n k L : ℕ} (hk : 0 < k) (hL : 0 < L)
    (hd : intervalLCM n 1 ∣ L) : 0 < L / intervalLCM n k :=
  Nat.div_pos (Nat.le_of_dvd hL ((intervalLCM_dvd_of_le hk).trans hd))
    (Nat.pos_of_ne_zero (intervalLCM_ne_zero hk))

/-- The exact recurrence of the determinantal divisors of the integer matrix. -/
theorem determinantalDivisor_succ {n L k : ℕ} (hL : 0 < L)
    (hd : intervalLCM n 1 ∣ L) (hk : k + 1 ≤ n) :
    determinantalDivisor n L (k + 1) =
      determinantalDivisor n L k * (L / intervalLCM n (k + 1)) := by
  have hkn : k ≤ n := by omega
  have hD := determinantalDivisor_ne_zero hkn hL hd
  have hQ := (scale_div_intervalLCM_pos (Nat.succ_pos k) hL hd).ne'
  apply Nat.eq_of_factorization_eq (determinantalDivisor_ne_zero hk hL hd) (mul_ne_zero hD hQ)
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hD hQ, Finsupp.add_apply,
      determinantalDivisor_factorization hp hL hd hk,
      determinantalDivisor_factorization hp hL hd hkn]
    exact divisorExponent_succ_eq_intervalLCM hp hL.ne' hd hk
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The kth positive Smith factor as the quotient of actual determinantal divisors. -/
theorem smithFactor_eq_intervalLCM {n L k : ℕ} (hL : 0 < L)
    (hd : intervalLCM n 1 ∣ L) (hk : 0 < k) (hkn : k ≤ n) :
    determinantalDivisor n L k / determinantalDivisor n L (k - 1) =
      L / intervalLCM n k := by
  cases k with
  | zero => omega
  | succ k =>
    have hD := determinantalDivisor_ne_zero (show k ≤ n by omega) hL hd
    change determinantalDivisor n L (k + 1) / determinantalDivisor n L k =
      L / intervalLCM n (k + 1)
    rw [determinantalDivisor_succ hL hd hkn, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hD)]

/-- The exact positive quotients form the Smith divisibility chain. -/
theorem smithFactor_pos_and_dvd {n L k l : ℕ} (hL : 0 < L)
    (hd : intervalLCM n 1 ∣ L) (hk : 0 < k) (hkl : k ≤ l) (hln : l ≤ n) :
    0 < determinantalDivisor n L k / determinantalDivisor n L (k - 1) ∧
    (determinantalDivisor n L k / determinantalDivisor n L (k - 1)) ∣
      (determinantalDivisor n L l / determinantalDivisor n L (l - 1)) := by
  have hl : 0 < l := hk.trans_le hkl
  rw [smithFactor_eq_intervalLCM hL hd hk (hkl.trans hln),
    smithFactor_eq_intervalLCM hL hd hl hln]
  exact ⟨scale_div_intervalLCM_pos hk hL hd,
    Nat.div_dvd_div_left ((intervalLCM_dvd_of_le hk).trans hd) (intervalLCM_dvd_of_le hkl)⟩

end D5.S3.Arith.Lattices.HilbertSmith.HilbertSmithMatrix
