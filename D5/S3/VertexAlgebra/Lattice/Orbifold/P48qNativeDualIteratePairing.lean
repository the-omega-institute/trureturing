/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualIteratePairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualIteratePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual paired BPZ-iterate coefficients and their finite binomial reindexing. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualPairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate
import D5.S3.VertexAlgebra.LatticeActualConformalEnergy
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-! Finite paired coefficients for the BPZ-inverted actual source iterate. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing

open scoped BigOperators in
private theorem restrictedDualJacobi_iterate_reindex
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (m B : ℂ) (N : ℕ) (F : ℕ → V) :
    (∑ j ∈ Finset.range N, Ring.choose m j •
      (∑ u ∈ Finset.range (N - j),
        ((-1 : ℂ) ^ j * Ring.choose (B - (j : ℂ)) u) • F (j + u))) =
      ∑ h ∈ Finset.range N, Ring.choose (B - m) h • F h := by
  have reflect (x : ℂ) (k : ℕ) :
      Ring.choose x k = (-1 : ℂ) ^ k * Ring.choose ((k : ℂ) - 1 - x) k := by
    have hneg := Ring.choose_neg (-x) k
    rw [neg_neg, show -x + (k : ℂ) - 1 = (k : ℂ) - 1 - x by ring] at hneg
    simpa only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast] using hneg
  have diagonal (h : ℕ) :
      (∑ j ∈ Finset.range (h + 1),
        Ring.choose m j * ((-1 : ℂ) ^ j * Ring.choose (B - (j : ℂ)) (h - j))) =
        Ring.choose (B - m) h := by
    let A : ℂ := (h : ℂ) - 1 - B
    have vandermonde := Ring.add_choose_eq (R := ℂ) (r := m) (s := A) h (Commute.all _ _)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
    calc
      _ = (-1 : ℂ) ^ h *
          (∑ j ∈ Finset.range (h + 1), Ring.choose m j * Ring.choose A (h - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjh : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have htop : ((h - j : ℕ) : ℂ) - 1 - (B - (j : ℂ)) = A := by
          dsimp only [A]
          rw [Nat.cast_sub hjh]
          ring
        have hsign : (-1 : ℂ) ^ h = (-1 : ℂ) ^ j * (-1 : ℂ) ^ (h - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjh]
        rw [reflect (B - (j : ℂ)) (h - j), htop, hsign]
        ring
      _ = (-1 : ℂ) ^ h * Ring.choose (m + A) h := by rw [← vandermonde]
      _ = _ := by
        rw [reflect (B - m) h, show m + A = (h : ℂ) - 1 - (B - m) by
          dsimp only [A]
          ring]
  let term (j u : ℕ) : V :=
    (Ring.choose m j * ((-1 : ℂ) ^ j * Ring.choose (B - (j : ℂ)) u)) • F (j + u)
  calc
    _ = ∑ j ∈ Finset.range N, ∑ u ∈ Finset.range (N - j), term j u := by
      simp only [Finset.smul_sum, smul_smul, term]
    _ = ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range (h + 1), term j (h - j) :=
      (Finset.sum_range_diag_flip N term).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      calc
        _ = ∑ j ∈ Finset.range (h + 1),
            (Ring.choose m j * ((-1 : ℂ) ^ j * Ring.choose (B - (j : ℂ)) (h - j))) •
              F h := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [term, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        _ = _ := by rw [← Finset.sum_smul, diagonal]

open scoped BigOperators in
theorem sum_range_iterate_simplex_reindex
    {V : Type*} [AddCommMonoid V] (K : ℕ) (G : ℕ → ℕ → ℕ → ℕ → V) :
    (∑ j ∈ Finset.range K, ∑ r ∈ Finset.range (K - j),
      ∑ i ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r - i + 1),
        G i l j (r - i - l)) =
      ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range (K - i),
        ∑ j ∈ Finset.range (K - i - l), ∑ u ∈ Finset.range (K - i - l - j),
          G i l j u := by
  have commuteTriangle (N : ℕ) (F : ℕ → ℕ → V) :
      (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range (N - a), F a b) =
        ∑ b ∈ Finset.range N, ∑ a ∈ Finset.range (N - b), F a b := by
    apply Finset.sum_comm'
    intro a b
    simp only [Finset.mem_range, Nat.lt_sub_iff_add_lt]
    constructor
    · intro h
      exact ⟨by simpa only [Nat.add_comm] using h.2,
        lt_of_le_of_lt (Nat.le_add_right b a) h.2⟩
    · intro h
      exact ⟨lt_of_le_of_lt (Nat.le_add_right a b) h.1,
        by simpa only [Nat.add_comm] using h.1⟩
  calc
    _ = ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range (K - j),
          ∑ l ∈ Finset.range (K - j - i), ∑ u ∈ Finset.range (K - j - i - l),
            G i l j u := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ i ∈ Finset.range (K - j), ∑ s ∈ Finset.range (K - j - i),
              ∑ l ∈ Finset.range (s + 1), G i l j (s - l) :=
          Finset.sum_range_diag_flip (K - j)
            (fun i s => ∑ l ∈ Finset.range (s + 1), G i l j (s - l))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_range_diag_flip (K - j - i) (fun l u => G i l j u)
    _ = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range (K - i),
          ∑ l ∈ Finset.range (K - i - j), ∑ u ∈ Finset.range (K - i - j - l),
            G i l j u := by
      calc
        _ = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range (K - i),
              ∑ l ∈ Finset.range (K - j - i), ∑ u ∈ Finset.range (K - j - i - l),
                G i l j u :=
          commuteTriangle K (fun j i =>
            ∑ l ∈ Finset.range (K - j - i), ∑ u ∈ Finset.range (K - j - i - l),
              G i l j u)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.sub_right_comm K j i]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ l ∈ Finset.range (K - i), ∑ j ∈ Finset.range (K - i - l),
              ∑ u ∈ Finset.range (K - i - j - l), G i l j u :=
          commuteTriangle (K - i) (fun j l =>
            ∑ u ∈ Finset.range (K - i - j - l), G i l j u)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.sub_right_comm (K - i) j l]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIteratePairing

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeAllStateReconstruction (mu)
open LatticePositiveEnergy (carrierCoeffEquiv chargeEnergy_nonneg energy grade mem_grade_iff)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeDualCoefficients (bpzTerm)
open P48qNativeDualLinearField (dualField)
open P48qNativeInvertedIterate (sourceLOne_divided_inverted_iterate)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (integerBinomial)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private source_grade_iff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField

noncomputable section

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "C" => HVertexOperator.coeff

private theorem sourceMu_energy (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b) (m : ℤ) :
    L₀ (mu lattice a m b) =
      (((d : ℤ) + (e : ℤ) - m - 1 : ℤ) : ℂ) • mu lattice a m b := by
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    (LatticeActualConformalEnergy.fused_eigenstate_energy lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      a b (d : ℂ) (e : ℂ) ha hb m)

/-- A source mode with negative output weight vanishes on the actual carrier. -/
theorem sourceMu_eq_zero_of_weight_lt_mode_succ (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (m : ℤ) (hm : (d : ℤ) + (e : ℤ) < m + 1) :
    mu lattice a m b = 0 := by
  classical
  let n : ℤ := (d : ℤ) + (e : ℤ) - m - 1
  have hGrade : mu lattice a m b ∈ grade lattice n :=
    (source_grade_iff n _).mp (sourceMu_energy a b d e ha hb m)
  apply (carrierCoeffEquiv lattice).injective
  apply Finsupp.ext
  intro x
  rw [map_zero, Finsupp.zero_apply]
  change ((mu lattice a m b) x.1).coeff x.2 = 0
  apply (mem_grade_iff lattice n _).mp hGrade x
  have hx := chargeEnergy_nonneg lattice P48qGramPositivity.nebeGram_posDef x.1
  dsimp only [energy, n]
  omega

set_option maxHeartbeats 1000000 in
/-- The actual dual coefficient of a source iterate pairs as the finite
inverted-iterate expansion of its BPZ readout. -/
theorem gradedPairing_dualField_inverted_iterate_coeff
    (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (m k : ℤ) (hm : m + 1 ≤ (d : ℤ) + (e : ℤ))
    (f : RestrictedDual) (v : State) :
    let D : ℕ := ((d : ℤ) + (e : ℤ) - m - 1).toNat
    gradedPairing (C (dualField (mu lattice a m b)) k f) v =
      (-1 : ℂ) ^ D * ∑ r ∈ Finset.range (D + 1),
        ∑ i ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r - i + 1),
          integerBinomial (2 * (d : ℤ) - m - (i : ℤ) - 2) (r - i - l) *
            gradedPairing f
              (C (nativeField (mu lattice (dividedTranslation L₁ i a)
                (m + (r : ℤ) - (i : ℤ) - (l : ℤ)) (dividedTranslation L₁ l b)))
                (-k - 6 * (D : ℤ) + 3 * (r : ℤ)) v) := by
  classical
  intro D
  have hNonneg : 0 ≤ (d : ℤ) + (e : ℤ) - m - 1 := by omega
  have hD : (D : ℤ) = (d : ℤ) + (e : ℤ) - m - 1 := Int.toNat_of_nonneg hNonneg
  have hWeight : L₀ (mu lattice a m b) = (D : ℂ) • mu lattice a m b := by
    have h := sourceMu_energy a b d e ha hb m
    rw [← hD, Int.cast_natCast] at h
    exact h
  have haInt : L₀ a = ((d : ℤ) : ℂ) • a := by
    simpa only [Int.cast_natCast] using ha
  let readout (r : ℕ) : NativeStates →ₗ[ℂ] ℂ :=
    (gradedPairing f).comp ((LinearMap.applyₗ (R := ℂ) v).comp
      ((LinearMap.proj (-k - 6 * (D : ℤ) + 3 * (r : ℤ))).comp (HVertexOperator.coeff.comp nativeField)))
  have hReadout (r : ℕ) (u : NativeStates) :
      readout r u = gradedPairing f
        (C (nativeField u) (-k - 6 * (D : ℤ) + 3 * (r : ℤ)) v) := by
    simp only [readout, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.proj_apply]
  rw [gradedPairing_dualField_coeff (mu lattice a m b) D hWeight k f v]
  simp only [map_smul, map_sum, smul_eq_mul]
  refine congrArg (fun z : ℂ => (-1 : ℂ) ^ D * z) ?_
  apply Finset.sum_congr rfl
  intro r _
  calc
    (r.factorial : ℂ)⁻¹ * gradedPairing f (bpzTerm (mu lattice a m b) D k r v) =
        readout r (dividedTranslation L₁ r (mu lattice a m b)) := by
      rw [dividedTranslation, LinearMap.smul_apply, map_smul, smul_eq_mul, hReadout, bpzTerm]
    _ = _ := by
      have hr : dividedTranslation L₁ r (mu lattice a m b) =
          ∑ i ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r - i + 1),
            integerBinomial (2 * (d : ℤ) - m - (i : ℤ) - 2) (r - i - l) •
              mu lattice (dividedTranslation L₁ i a)
                (m + (r : ℤ) - (i : ℤ) - (l : ℤ)) (dividedTranslation L₁ l b) := by
        simpa only [mu] using sourceLOne_divided_inverted_iterate a b (d : ℤ) haInt m r
      rw [hr]
      simp only [map_sum, map_smul, smul_eq_mul]
      simp only [hReadout]

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
