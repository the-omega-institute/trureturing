/- GID: D5/S3/Quantum/Hiai/SpectralNonconcavity
   generality: I
   mirror-B: D5/B/S3/Quantum/Hiai/SpectralNonconcavity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Hiai/SpectralNonconcavity.claim; result=D5/S3/Quantum/Hiai/SpectralNonconcavity.result; claim=D5/S3/Quantum/Hiai/SpectralNonconcavity.claim
   digest: Every off-midpoint untilde spectral trace has a strict affine faithful-qubit Jensen violation. -/

import D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
import D5.S3.Quantum.Hiai.InverseGeometricIdentification
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


noncomputable section
-- Matrix and scalar functions are unfolded when inferring their limit types.
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Hiai.SpectralNonconcavity

open _root_.Matrix Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open PsiMeanTraceConcavity InverseGeometricIdentification
  D5.S3.Quantum.Matrix.AlternativeMeanLinearization
local instance : Pow (Matrix (Fin 2) (Fin 2) ℂ) ℝ := ⟨CFC.rpow⟩

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
local instance : Pow Mat NNReal := ⟨CFC.nnrpow⟩

/-- Real symmetric, strictly positive density matrices, represented over the complex scalars. -/
def Density (A : Mat) : Prop :=
  A.PosDef ∧ Matrix.trace A = 1 ∧ (∀ i j, (A i j).im = 0) ∧ A.transpose = A

/-- The original unweighted mean with powered inputs. -/
def nativeMean (p : ℝ) (A B : Mat) : Mat :=
  geometricMean (1 / 2) (A ^ (-p)) (B ^ p)

/-- The UNTILDE functional with the literal outer spectral power. -/
def spectralTrace (α p : ℝ) (A B : Mat) : ℝ :=
  (Matrix.trace ((nativeMean p A B ^ α * A ^ p * nativeMean p A B ^ α) ^ (1 / p))).re

private lemma mean_inverse_base (X Y : Mat) (hX : X.PosDef) :
    geometricMean (1 / 2) (X ^ (-1 : ℝ)) Y =
      CFC.conjSqrt (Ring.inverse X) (CFC.sqrt (CFC.conjSqrt X Y)) := by
  unfold geometricMean
  rw [CFC.rpow_rpow X (-1) (1 / 2) (by norm_num) hX.isStrictlyPositive,
    CFC.rpow_rpow X (-1) (-1 / 2) (by norm_num) hX.isStrictlyPositive]
  norm_num only [neg_mul, one_mul, neg_neg]
  rw [CFC.conjSqrt_apply, CFC.conjSqrt_apply, CFC.sqrt_ringInverse,
    CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one (hX.isStrictlyPositive.rpow X (1 / 2)),
    CFC.rpow_rpow X (1 / 2) (-1) (by norm_num) hX.isStrictlyPositive,
    CFC.sqrt_eq_rpow]
  norm_num

private lemma geometricMean_eq_gmInv (X Y : Mat) (hX : X.PosDef) (hY : Y.PosDef) :
    geometricMean (1 / 2) (X ^ (-1 : ℝ)) Y =
      _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.gmInv X Y := by
  have hS : (X ^ (1 / 2 : ℝ)).PosDef := hX.isStrictlyPositive.rpow X (1 / 2) |>.posDef
  have hM : (X ^ (1 / 2 : ℝ) * Y * X ^ (1 / 2 : ℝ)).PosDef := by
    simpa only [star_eq_conjTranspose, hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hY
  unfold geometricMean _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.gmInv
  rw [CFC.rpow_rpow X (-1) (1 / 2) (by norm_num) hX.isStrictlyPositive,
    CFC.rpow_rpow X (-1) (-1 / 2) (by norm_num) hX.isStrictlyPositive]
  norm_num only [neg_mul, one_mul, neg_neg]
  rw [CFC.rpow_eq_cfc_real hX.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]
  simp only [← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]
  rw [← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg]

private lemma native_riccati (p : ℝ) (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    IsStrictlyPositive (nativeMean p A B) ∧ nativeMean p A B * A ^ p * nativeMean p A B = B ^ p := by
  have he : A ^ (-p) = (A ^ p) ^ (-1 : ℝ) := by
    by_cases hp : p = 0
    · subst p
      simp [CFC.rpow_zero A hA.posSemidef.nonneg]
    · rw [CFC.rpow_rpow A p (-1) hp hA.isStrictlyPositive]
      congr 1
      ring
  unfold nativeMean
  rw [he]
  have hAp : (A ^ p).PosDef := (hA.isStrictlyPositive.rpow A p).posDef
  have hBp : (B ^ p).PosDef := (hB.isStrictlyPositive.rpow B p).posDef
  rw [geometricMean_eq_gmInv (A ^ p) (B ^ p) hAp hBp]
  exact ⟨(_root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati
      hAp hBp).1.isStrictlyPositive,
    (_root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati
      hAp hBp).2⟩

private lemma native_reverse (p : ℝ) (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    nativeMean p B A = Ring.inverse (nativeMean p A B) := by
  obtain ⟨hL, h⟩ := native_riccati p A B hA hB
  have he : Ring.inverse (nativeMean p A B) * B ^ p * Ring.inverse (nativeMean p A B) = A ^ p := by
    rw [← h]
    calc
      _ = (Ring.inverse (nativeMean p A B) * nativeMean p A B) * A ^ p *
          (nativeMean p A B * Ring.inverse (nativeMean p A B)) := by simp only [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hL.isUnit,
        Ring.mul_inverse_cancel _ hL.isUnit, one_mul, mul_one]
  have hu := _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique
    (A := B ^ p) (B := A ^ p) (Y := Ring.inverse (nativeMean p A B))
    (hB.isStrictlyPositive.rpow B p).posDef hL.ringInverse.posDef he
  have hb : B ^ (-p) = (B ^ p) ^ (-1 : ℝ) := by
    by_cases hp : p = 0
    · subst p
      simp [CFC.rpow_zero B hB.posSemidef.nonneg]
    · rw [CFC.rpow_rpow B p (-1) hp hB.isStrictlyPositive]
      congr 1
      ring
  rw [← geometricMean_eq_gmInv (B ^ p) (A ^ p)
    (hB.isStrictlyPositive.rpow B p).posDef (hA.isStrictlyPositive.rpow A p).posDef] at hu
  simpa only [nativeMean, hb] using hu

private lemma complement (α p : ℝ) (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    spectralTrace (1 - α) p B A = spectralTrace α p A B := by
  obtain ⟨hL, h⟩ := native_riccati p A B hA hB
  have he : Ring.inverse (nativeMean p A B) ^ (1 - α) = nativeMean p A B ^ (α - 1) := by
    rw [CFC.inverse_eq_rpow_neg_one hL,
      CFC.rpow_rpow _ (-1) (1 - α) (by norm_num) hL]
    congr 1
    ring
  have hl : nativeMean p A B ^ (α - 1) * nativeMean p A B = nativeMean p A B ^ α := by
    conv_lhs => rhs; rw [← CFC.rpow_one _ hL.nonneg]
    rw [← CFC.rpow_add hL.isUnit]
    congr 1
    ring
  have hr : nativeMean p A B * nativeMean p A B ^ (α - 1) = nativeMean p A B ^ α := by
    conv_lhs => lhs; rw [← CFC.rpow_one _ hL.nonneg]
    rw [← CFC.rpow_add hL.isUnit]
    congr 1
    ring
  unfold spectralTrace
  rw [native_reverse p A B hA hB, he, ← h]
  congr 3
  calc
    _ = (nativeMean p A B ^ (α - 1) * nativeMean p A B) * A ^ p *
        (nativeMean p A B * nativeMean p A B ^ (α - 1)) := by simp only [mul_assoc]
    _ = _ := by rw [hl, hr]

private lemma unitary_power (U : unitary Mat) {X : Mat} (hX : IsStrictlyPositive X) (r : ℝ) :
    ((U : Mat) * X * star (U : Mat)) ^ r = (U : Mat) * X ^ r * star (U : Mat) := by
  change CFC.rpow ((U : Mat) * X * star (U : Mat)) r =
    (U : Mat) * CFC.rpow X r * star (U : Mat)
  exact unitary_rpow U hX r

private lemma unitary_native (p : ℝ) (U : unitary Mat) (A B : Mat)
    (hA : A.PosDef) (hB : B.PosDef) :
    nativeMean p ((U : Mat) * A * star (U : Mat)) ((U : Mat) * B * star (U : Mat)) =
      (U : Mat) * nativeMean p A B * star (U : Mat) := by
  have hAu := (Unitary.isUnit_coe (U := U)).isStrictlyPositive_star_right_conjugate_iff.mpr
    hA.isStrictlyPositive
  have hBu := (Unitary.isUnit_coe (U := U)).isStrictlyPositive_star_right_conjugate_iff.mpr
    hB.isStrictlyPositive
  obtain ⟨hL, h⟩ := native_riccati p A B hA hB
  have hLu := (Unitary.isUnit_coe (U := U)).isStrictlyPositive_star_right_conjugate_iff.mpr hL
  have he : ((U : Mat) * nativeMean p A B * star (U : Mat)) *
      (((U : Mat) * A * star (U : Mat)) ^ p) *
      ((U : Mat) * nativeMean p A B * star (U : Mat)) =
      ((U : Mat) * B * star (U : Mat)) ^ p := by
    rw [unitary_power U hA.isStrictlyPositive, unitary_power U hB.isStrictlyPositive]
    calc
      _ = (U : Mat) * (nativeMean p A B * A ^ p * nativeMean p A B) * star (U : Mat) := by
        simp only [mul_assoc, ← mul_assoc (star (U : Mat)), Unitary.coe_star_mul_self,
          one_mul]
      _ = _ := by rw [h]
  have hu := _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique
    (A := ((U : Mat) * A * star (U : Mat)) ^ p)
    (B := ((U : Mat) * B * star (U : Mat)) ^ p)
    (Y := (U : Mat) * nativeMean p A B * star (U : Mat))
    (hAu.rpow _ p).posDef hLu.posDef he
  have hx : (((U : Mat) * A * star (U : Mat)) ^ p) ^ (-1 : ℝ) =
      ((U : Mat) * A * star (U : Mat)) ^ (-p) := by
    by_cases hp : p = 0
    · subst p
      simp [CFC.rpow_zero _ hAu.nonneg]
    · rw [CFC.rpow_rpow _ p (-1) hp hAu]
      congr 1
      ring
  rw [← geometricMean_eq_gmInv (((U : Mat) * A * star (U : Mat)) ^ p)
    (((U : Mat) * B * star (U : Mat)) ^ p) (hAu.rpow _ p).posDef (hBu.rpow _ p).posDef] at hu
  simpa only [nativeMean, hx] using hu

private lemma unitary_trace (α p : ℝ) (U : unitary Mat) (A B : Mat)
    (hA : A.PosDef) (hB : B.PosDef) :
    spectralTrace α p ((U : Mat) * A * star (U : Mat))
      ((U : Mat) * B * star (U : Mat)) = spectralTrace α p A B := by
  have hL := (native_riccati p A B hA hB).1
  have hW := hL.rpow _ α
  have hX := hA.isStrictlyPositive.rpow A p
  have hQ := (hW.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint (A ^ p)
    (nativeMean p A B ^ α) hW.isSelfAdjoint).2 hX
  unfold spectralTrace
  rw [unitary_native p U A B hA hB, unitary_power U hL α,
    unitary_power U hA.isStrictlyPositive p]
  have he : ((U : Mat) * nativeMean p A B ^ α * star (U : Mat)) *
      ((U : Mat) * A ^ p * star (U : Mat)) *
      ((U : Mat) * nativeMean p A B ^ α * star (U : Mat)) =
      (U : Mat) * (nativeMean p A B ^ α * A ^ p * nativeMean p A B ^ α) * star (U : Mat) := by
    simp only [mul_assoc, ← mul_assoc (star (U : Mat)), Unitary.coe_star_mul_self, one_mul]
  rw [he, unitary_power U hQ (1 / p), Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    one_mul]

private lemma positive_power_limit {ι : Type*} {l : Filter ι} {F : ι → Mat} {T : Mat}
    (hF : ∀ᶠ i in l, 0 ≤ F i) (hT : 0 ≤ T) (h : Tendsto F l (𝓝 T))
    {r : ℝ} (hr : 0 < r) : Tendsto (fun i ↦ F i ^ r) l (𝓝 (T ^ r)) := by
  let q : NNReal := ⟨r, hr.le⟩
  have hq : 0 < q := hr
  have hh := (CFC.continuousOn_nnrpow (A := Mat) q).continuousWithinAt hT
  have hm : Tendsto F l (𝓝[ {x : Mat | 0 ≤ x}] T) := tendsto_nhdsWithin_iff.mpr ⟨h, hF⟩
  have ht := hh.tendsto.comp hm
  change Tendsto (fun i ↦ CFC.nnrpow (F i) q) l (𝓝 (CFC.nnrpow T q)) at ht
  change Tendsto (fun i ↦ CFC.rpow (F i) r) l (𝓝 (CFC.rpow T r))
  have he (M : Mat) : CFC.nnrpow M q = CFC.rpow M r := by
    exact CFC.nnrpow_eq_rpow (a := M) hq
  simp_rw [he] at ht
  exact ht

def diagonalState (t : ℝ) : Mat := Matrix.diagonal ![((1 - t : ℝ) : ℂ), (t : ℂ)]

def balancedState (s : ℝ) : Mat :=
  !![(1 / 2 : ℂ), ((1 / 2 - s : ℝ) : ℂ); ((1 / 2 - s : ℝ) : ℂ), (1 / 2 : ℂ)]

private def sym (u v w : ℝ) : Mat := !![(u : ℂ), (v : ℂ); (v : ℂ), (w : ℂ)]

private def P : Mat := balancedState 0
private def Q : Mat := diagonalState 0
private def J : Mat := D5.S3.Quantum.FiniteDimensional.qubitX
private def Z : Mat := D5.S3.Quantum.FiniteDimensional.qubitZ

private lemma P_nonneg : 0 ≤ P := by
  have he : P = star P * P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, balancedState, Matrix.star_apply, Matrix.mul_apply,
        Fin.sum_univ_two, RCLike.star_def, map_ofNat]
  rw [he]
  exact star_mul_self_nonneg _

private lemma diagonal_density {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : Density (diagonalState t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · change (0 : ℂ) < ((1 - t : ℝ) : ℂ)
      exact_mod_cast sub_pos.mpr ht1
    · change (0 : ℂ) < (t : ℂ)
      exact_mod_cast ht
  · simp [diagonalState, Matrix.trace, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [diagonalState, Matrix.diagonal]
  · exact Matrix.diagonal_transpose _

private lemma balanced_density {s : ℝ} (hs : 0 < s) (hs1 : s < 1 / 2) : Density (balancedState s) := by
  have he : balancedState s = s • (1 : Mat) + (1 - 2 * s) • P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, balancedState, Matrix.smul_apply, Matrix.one_apply] <;> push_cast <;> ring
  have hp : ((1 - 2 * s) • P).PosSemidef :=
    (P_nonneg.posSemidef).smul (show (0 : ℝ) ≤ 1 - 2 * s by linarith)
  have hd : (s • (1 : Mat)).PosDef := Matrix.PosDef.one.smul hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hd.add_posSemidef hp
  · norm_num [balancedState, Matrix.trace, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [balancedState]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [balancedState, Matrix.transpose_apply]

private lemma J_unitary : J ∈ unitary Mat := by
  apply Unitary.mem_iff.mpr
  have hw := D5.S3.Quantum.FiniteDimensional.qubit_weyl_star
  change star J * J = 1 ∧ J * star J = 1
  simpa only [J, hw.2.1, ← pow_two] using And.intro hw.2.2.2.1 hw.2.2.2.1

private lemma J_swap (t s : ℝ) :
    J * diagonalState t * star J = diagonalState (1 - t) ∧
    J * balancedState s * star J = balancedState s := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [J, D5.S3.Quantum.FiniteDimensional.qubitX, diagonalState, balancedState,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.star_apply, Fin.sum_univ_two] <;> ring

private lemma equal_endpoints (α p t s : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hs : 0 < s) (hs1 : s < 1 / 2) :
    spectralTrace α p (diagonalState (1 - t)) (balancedState s) =
      spectralTrace α p (diagonalState t) (balancedState s) := by
  have h := unitary_trace α p ⟨J, J_unitary⟩ (diagonalState t) (balancedState s)
    (diagonal_density ht ht1).1 (balanced_density hs hs1).1
  simpa only [(J_swap t s).1, (J_swap t s).2] using h

private lemma diagonal_power (t r : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    diagonalState t ^ r = Matrix.diagonal ![(((1 - t) ^ r : ℝ) : ℂ), ((t ^ r : ℝ) : ℂ)] := by
  have hz : IsSelfAdjoint Z := by
    exact D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1
  have hzz : Z * Z = 1 := by
    simpa only [Z, ← pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2
  have he : diagonalState t = (1 / 2 : ℝ) • (1 : Mat) + (1 / 2 - t) • Z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalState, Z, D5.S3.Quantum.FiniteDimensional.qubitZ,
        Matrix.one_apply] <;> push_cast <;> ring
  rw [CFC.rpow_eq_cfc_real (diagonal_density ht ht1).1.posSemidef.nonneg, he,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc]
  · have h1 : (1 / 2 : ℝ) + (1 / 2 - t) = 1 - t := by ring
    have h2 : (1 / 2 : ℝ) - (1 / 2 - t) = t := by ring
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Z, D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.one_apply] <;>
      push_cast <;> ring
  · exact hz
  · exact hzz

private lemma balanced_power (s r : ℝ) (hs : 0 < s) (hs1 : s < 1 / 2) :
    balancedState s ^ r = sym (((1 - s) ^ r + s ^ r) / 2)
      (((1 - s) ^ r - s ^ r) / 2) (((1 - s) ^ r + s ^ r) / 2) := by
  have hj : IsSelfAdjoint J := D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.1
  have hjj : J * J = 1 := by
    simpa only [J, ← pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.1
  have he : balancedState s = (1 / 2 : ℝ) • (1 : Mat) + (1 / 2 - s) • J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [balancedState, J, D5.S3.Quantum.FiniteDimensional.qubitX,
        Matrix.one_apply] <;> push_cast <;> ring
  rw [CFC.rpow_eq_cfc_real (balanced_density hs hs1).1.posSemidef.nonneg, he,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc]
  · have h1 : (1 / 2 : ℝ) + (1 / 2 - s) = 1 - s := by ring
    have h2 : (1 / 2 : ℝ) - (1 / 2 - s) = s := by ring
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sym, J, D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.one_apply] <;>
      push_cast <;> ring
  · exact hj
  · exact hjj

private lemma diagonal_mean_formula (x y a b d c : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hY : (sym a b a).PosDef)
    (hd2 : d ^ (2 : ℕ) = x * y * (a ^ (2 : ℕ) - b ^ (2 : ℕ)))
    (hc2 : c ^ (2 : ℕ) = a * (x + y) + 2 * d) :
    geometricMean (1 / 2) ((Matrix.diagonal ![(x : ℂ), (y : ℂ)] : Mat) ^ (-1 : ℝ))
      (sym a b a) = sym ((a + d / x) / c) (b / c) ((a + d / y) / c) := by
  let X : Mat := Matrix.diagonal ![(x : ℂ), (y : ℂ)]
  let R := sym ((a + d / x) / c) (b / c) ((a + d / y) / c)
  have hX : X.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · change (0 : ℂ) < (x : ℂ)
      exact_mod_cast hx
    · change (0 : ℂ) < (y : ℂ)
      exact_mod_cast hy
  have hinv : Ring.inverse X = Matrix.diagonal ![(x⁻¹ : ℂ), (y⁻¹ : ℂ)] := by
    let D : Mat := Matrix.diagonal ![(x⁻¹ : ℂ), (y⁻¹ : ℂ)]
    have hXD : X * D = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [X, D, hx.ne', hy.ne']
    calc
      _ = Ring.inverse X * (X * D) := by rw [hXD, mul_one]
      _ = D := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hX.isUnit, one_mul]
  have he : R = (1 / c) • (sym a b a + d • Ring.inverse X) := by
    rw [hinv]
    ext i j
    change R i j = (1 / c : ℝ) • (sym a b a i j + d • ((Matrix.diagonal ![(x⁻¹ : ℂ), (y⁻¹ : ℂ)] : Mat) i j))
    fin_cases i <;> fin_cases j <;>
      simp [R, sym, Matrix.diagonal, smul_eq_mul] <;> push_cast <;> ring
  have hR : IsStrictlyPositive R := by
    rw [he]
    exact ((hY.add (hX.isStrictlyPositive.ringInverse.posDef.smul hd)).smul
      (show (0 : ℝ) < 1 / c by positivity)).isStrictlyPositive
  have heq : R * X * R = sym a b a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, X, sym, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      norm_cast <;> field_simp [hx.ne', hy.ne', hc.ne']
    · linear_combination hd2 - a * x * hc2
    · linear_combination -b * hc2
    · linear_combination -b * hc2
    · linear_combination hd2 - a * y * hc2
  calc
    geometricMean (1 / 2) (X ^ (-1 : ℝ)) (sym a b a) =
        _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.gmInv X (sym a b a) :=
      geometricMean_eq_gmInv X (sym a b a) hX hY
    _ = R := _root_.D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique hX hR.posDef heq

private lemma root_power (u v w α : ℝ) (hv : 0 < v) (hL : 0 ≤ sym u v w) :
    sym u v w ^ α =
      lowerRoot u v w ^ α • (1 : Mat) +
      ((upperRoot u v w ^ α - lowerRoot u v w ^ α) /
        (upperRoot u v w - lowerRoot u v w)) •
        (sym u v w - lowerRoot u v w • (1 : Mat)) := by
  let a := (u + w) / 2
  let ρ := radius u v w
  let H := ρ⁻¹ • (sym u v w - a • (1 : Mat))
  have hr := (root_algebra u v w hv).1
  have hρ : ρ ≠ 0 := hr.ne'
  have hr2 : ρ ^ (2 : ℕ) = ((u - w) / 2) ^ (2 : ℕ) + v ^ (2 : ℕ) :=
    Real.sq_sqrt (by positivity)
  have hH : IsSelfAdjoint H := by
    change star H = H
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, sym, Matrix.star_apply, Matrix.one_apply]
  have hHH : H * H = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, sym, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      norm_cast <;> field_simp [hρ] <;> dsimp [a] at * <;> nlinarith [hr2]
  have he : sym u v w = a • (1 : Mat) + ρ • H := by
    dsimp [H]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  rw [CFC.rpow_eq_cfc_real hL, he,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc
      (fun x : ℝ ↦ x ^ α) a ρ H hH hHH]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, sym, lowerRoot, upperRoot, a, ρ, Matrix.one_apply] <;>
    push_cast <;> field_simp <;> ring

private lemma affine_coordinate (t τ : ℝ) (ht : 0 ≤ t) (htτ : t < τ) (hτ : τ < 1 / 2) :
    let ell := (τ - t) / (1 - 2 * t)
    0 < ell ∧ ell < 1 / 2 ∧
      diagonalState τ = (1 - ell) • diagonalState t + ell • diagonalState (1 - t) := by
  dsimp
  have hden : 0 < 1 - 2 * t := by linarith
  refine ⟨by positivity, (div_lt_iff₀ hden).mpr (by linarith), ?_⟩
  have hdc : (1 : ℂ) - 2 * (t : ℂ) ≠ 0 := by exact_mod_cast hden.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalState, Matrix.smul_apply] <;> push_cast <;>
      field_simp [show (1 : ℂ) - (t : ℂ) * 2 ≠ 0 by simpa only [mul_comm] using hdc] <;> ring

private lemma genuinely_noncommuting (t s : ℝ) (ht : t ≠ 1 / 2) (hs : s ≠ 1 / 2) :
    diagonalState t * balancedState s ≠ balancedState s * diagonalState t := by
  intro he
  have h01 := congrArg (fun M : Mat ↦ (M 0 1).re) he
  simp [diagonalState, balancedState, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hprod : (1 - 2 * t) * (1 - 2 * s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact ht (by linarith)
  · exact hs (by linarith)

private lemma native_two_scale (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) =
      sym (entryU p s) (entryV p s) (entryW p s) := by
  obtain ⟨hz, hx, ha, hb, he, hc, he2, hab, hc2⟩ := entry_facts p s hp hs hs1
  have ht : 0 < s ^ (2 : ℕ) := sq_pos_of_pos hs
  have ht1 : s ^ (2 : ℕ) < 1 := by nlinarith
  have hY : (sym (entryA p s) (entryB p s) (entryA p s)).PosDef := by
    rw [show sym (entryA p s) (entryB p s) (entryA p s) = balancedState s ^ p by
      rw [balanced_power s p hs hs1]
      simp only [entryA, entryB, scale_square p s hs.le]]
    exact ((balanced_density hs hs1).1.isStrictlyPositive.rpow _ p).posDef
  have hpow : diagonalState (s ^ (2 : ℕ)) ^ p =
      Matrix.diagonal ![(entryX p s : ℂ), ((scale p s ^ (4 : ℕ) : ℝ) : ℂ)] := by
    rw [diagonal_power _ _ ht ht1, scale_fourth p s hs.le]
    rfl
  have hneg : diagonalState (s ^ (2 : ℕ)) ^ (-p) = (diagonalState (s ^ (2 : ℕ)) ^ p) ^ (-1 : ℝ) := by
    rw [CFC.rpow_rpow _ p (-1) hp.ne' (diagonal_density ht ht1).1.isStrictlyPositive]
    congr 1
    ring
  have hd2 : (scale p s ^ (3 : ℕ) * entryE p s) ^ (2 : ℕ) =
      entryX p s * scale p s ^ (4 : ℕ) * (entryA p s ^ (2 : ℕ) - entryB p s ^ (2 : ℕ)) := by
    rw [mul_pow, he2, hab]
    ring
  unfold nativeMean
  rw [hneg, hpow, balanced_power s p hs hs1]
  simp only [← scale_square p s hs.le]
  change geometricMean (1 / 2) ((Matrix.diagonal ![(entryX p s : ℂ), ((scale p s ^ (4 : ℕ) : ℝ) : ℂ)] : Mat) ^ (-1 : ℝ))
    (sym (entryA p s) (entryB p s) (entryA p s)) = _
  rw [diagonal_mean_formula _ _ _ _ _ _ hx (by positivity) (by positivity)
    hc hY hd2 (by simpa only [mul_assoc] using hc2)]
  have hcancel : scale p s ^ (3 : ℕ) * entryE p s / scale p s ^ (4 : ℕ) = entryE p s / scale p s := by
    field_simp
  simp only [entryU, entryV, entryW, hcancel]

private lemma scaled_entries (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    scale p s * entryW p s = scaledW p s ∧
    scale p s * (entryU p s * entryW p s - entryV p s ^ (2 : ℕ)) = entryE p s / entryX p s := by
  obtain ⟨hz, hx, ha, hb, he, hc, he2, hab, hc2⟩ := entry_facts p s hp hs hs1
  constructor
  · dsimp [entryW, scaledW]
    field_simp
  · dsimp [entryU, entryV, entryW]
    field_simp [hz.ne', hx.ne', hc.ne']
    linear_combination -entryE p s * hc2 + (scale p s * entryX p s) * hab -
      scale p s ^ (3 : ℕ) * he2

private lemma actual_roots (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    0 < small p s ∧ 0 < largeScale p s ∧
    lowerRoot (entryU p s) (entryV p s) (entryW p s) = small p s ∧
    upperRoot (entryU p s) (entryV p s) (entryW p s) = largeScale p s / scale p s := by
  obtain ⟨hz, hx, ha, hb, he, hc, _, _, _⟩ := entry_facts p s hp hs hs1
  have hv : 0 < entryV p s := div_pos hb hc
  have hu : 0 < entryU p s := by dsimp [entryU]; positivity
  have hw : 0 < entryW p s := by dsimp [entryW]; positivity
  obtain ⟨hρ, hlt, hdet⟩ := root_algebra (entryU p s) (entryV p s) (entryW p s) hv
  have hM : 0 < upperRoot (entryU p s) (entryV p s) (entryW p s) := by
    dsimp [upperRoot]
    positivity
  have hscaled : scale p s * upperRoot (entryU p s) (entryV p s) (entryW p s) =
      largeScale p s := by
    rw [scaled_upperRoot _ _ _ _ hz.le, (scaled_entries p s hp hs hs1).1]
    rfl
  have hcp : 0 < largeScale p s := hscaled ▸ mul_pos hz hM
  have hmeq : lowerRoot (entryU p s) (entryV p s) (entryW p s) = small p s := by
    dsimp [small]
    apply (eq_div_iff (mul_pos hx hcp).ne').2
    calc
      _ = entryX p s * (scale p s *
        (upperRoot (entryU p s) (entryV p s) (entryW p s) *
          lowerRoot (entryU p s) (entryV p s) (entryW p s))) := by rw [← hscaled]; ring
      _ = entryE p s := by
        rw [hdet, (scaled_entries p s hp hs hs1).2]
        field_simp
  refine ⟨by dsimp [small]; positivity, hcp, hmeq, ?_⟩
  exact (eq_div_iff hz.ne').2 (by simpa [mul_comm] using hscaled)

private lemma actual_power (α p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α =
      small p s ^ α • (1 : Mat) + slope α p s •
        (sym (entryU p s) (entryV p s) (entryW p s) - small p s • (1 : Mat)) := by
  obtain ⟨hz, hx, ha, hb, he, hc, _, _, _⟩ := entry_facts p s hp hs hs1
  obtain ⟨hm, hcs, hlo, hhi⟩ := actual_roots p s hp hs hs1
  have ht : 0 < s ^ (2 : ℕ) := sq_pos_of_pos hs
  have ht1 : s ^ (2 : ℕ) < 1 := by nlinarith
  have hnonneg : 0 ≤ sym (entryU p s) (entryV p s) (entryW p s) := by
    rw [← native_two_scale p s hp hs hs1]
    exact (native_riccati p _ _ (diagonal_density ht ht1).1 (balanced_density hs hs1).1).1.nonneg
  have hlt := (root_algebra (entryU p s) (entryV p s) (entryW p s) (div_pos hb hc)).2.1
  rw [hlo, hhi] at hlt
  have hsf := slope_factor (largeScale p s / scale p s) (small p s) (scale p s)
    (largeScale p s) α (div_pos hcs hz) hm hz (by field_simp) (ne_of_lt hlt)
  have hq : small p s / (largeScale p s / scale p s) = ratio p s := by
    dsimp [ratio]
    field_simp
  rw [hq] at hsf
  rw [native_two_scale p s hp hs hs1, root_power (entryU p s) (entryV p s) (entryW p s) α (show 0 < entryV p s from div_pos hb hc) hnonneg,
    hlo, hhi, hsf]
  rfl

private lemma projection_power (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    (a • P) ^ r = a ^ r • P := by
  have hj : IsSelfAdjoint J := D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.1
  have hjj : J * J = 1 := by
    simpa only [J, ← pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.1
  have hnonneg := (P_nonneg.posSemidef.smul ha).nonneg
  have he (a : ℝ) : a • P = (a / 2) • (1 : Mat) + (a / 2) • J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, balancedState, J, D5.S3.Quantum.FiniteDimensional.qubitX,
        Matrix.smul_apply, Matrix.one_apply] <;> push_cast <;> ring
  rw [CFC.rpow_eq_cfc_real hnonneg, he,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc
      (fun x : ℝ ↦ x ^ r) (a / 2) (a / 2) J hj hjj]
  rw [show a / 2 + a / 2 = a by ring, sub_self, Real.zero_rpow hr.ne',
    add_zero, sub_zero, ← he]

private lemma Q_power (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    (a • Q) ^ r = a ^ r • Q := by
  have hz : IsSelfAdjoint Z := D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1
  have hzz : Z * Z = 1 := by
    simpa only [Z, ← pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2
  have hQ : Q.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Q, diagonalState]
  have he (a : ℝ) : a • Q = (a / 2) • (1 : Mat) + (a / 2) • Z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, diagonalState, Z, D5.S3.Quantum.FiniteDimensional.qubitZ,
        Matrix.smul_apply, Matrix.one_apply] <;> push_cast <;> ring
  rw [CFC.rpow_eq_cfc_real (hQ.smul ha).nonneg, he,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc
      (fun x : ℝ ↦ x ^ r) (a / 2) (a / 2) Z hz hzz]
  rw [show a / 2 + a / 2 = a by ring, sub_self, Real.zero_rpow hr.ne',
    add_zero, sub_zero, ← he]

private lemma native_sqrt_form (p : ℝ) (A B : Mat) (hp : p ≠ 0) (hA : A.PosDef) :
    nativeMean p A B =
      CFC.conjSqrt (Ring.inverse (A ^ p)) (CFC.sqrt (CFC.conjSqrt (A ^ p) (B ^ p))) := by
  have he : A ^ (-p) = (A ^ p) ^ (-1 : ℝ) := by
    rw [CFC.rpow_rpow A p (-1) hp hA.isStrictlyPositive]
    congr 1
    ring
  unfold nativeMean
  rw [he, mean_inverse_base _ _ (hA.isStrictlyPositive.rpow A p).posDef]

private lemma balanced_limit : Tendsto balancedState (𝓝[>] 0) (𝓝 P) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [balancedState, P, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;> first
    | exact tendsto_const_nhds
    | exact (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_const_nhds.sub (show Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds))

private lemma trace_continuous : Continuous (fun M : Mat ↦ (Matrix.trace M).re) := by
  unfold Matrix.trace
  fun_prop

private def rankMass (X : Mat) : ℝ := ((X 0 0 + X 0 1 + X 1 0 + X 1 1).re) / 2

private lemma rank_one_compression (X : Mat) (hX : X.PosDef) :
    0 < rankMass X ∧ P * X * P = rankMass X • P := by
  have hvec : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    norm_num at h0
  have hs : (0 : ℂ) < X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    have h := hX.dotProduct_mulVec_pos hvec
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, add_assoc] using h
  have hm : 0 < rankMass X := by
    have h := (Complex.lt_def.mp hs).1
    change 0 < (X 0 0 + X 0 1 + X 1 0 + X 1 1).re at h
    exact div_pos h (by norm_num)
  have hreal : (((X 0 0 + X 0 1 + X 1 0 + X 1 1).re : ℝ) : ℂ) =
      X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im, Complex.zero_im] using (Complex.lt_def.mp hs).2
  have hcast : (rankMass X : ℂ) = (X 0 0 + X 0 1 + X 1 0 + X 1 1) / 2 := by
    dsimp only [rankMass]
    rw [Complex.ofReal_div, Complex.ofReal_ofNat, hreal]
  refine ⟨hm, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, balancedState, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, smul_eq_mul, hcast] <;> ring

private lemma fixed_rank_one_limit {ι : Type*} {l : Filter ι}
    (α p : ℝ) (A : Mat) (hα : 0 < α) (hp : 0 < p) (hA : A.PosDef)
    (F : ι → Mat) (hF : ∀ᶠ i in l, (F i).PosDef) (hFP : Tendsto F l (𝓝 P)) :
    Tendsto (fun i ↦ spectralTrace α p A (F i)) l
      (𝓝 (rankMass (A ^ p) ^ ((1 - α) / p))) := by
  let X := A ^ p
  let m := rankMass X
  have hX : X.PosDef := (hA.isStrictlyPositive.rpow _ p).posDef
  have hm : 0 < m := (rank_one_compression X hX).1
  have hPp : P ^ p = P := by simpa using projection_power 1 p (by norm_num) hp
  have hBP : Tendsto (fun i ↦ F i ^ p) l (𝓝 P) := by
    rw [← hPp]
    apply positive_power_limit _ P_nonneg hFP hp
    filter_upwards [hF] with i hi
    exact hi.posSemidef.nonneg
  have hC : Tendsto (fun s ↦ CFC.conjSqrt X (F s ^ p)) l
      (𝓝 (CFC.conjSqrt X P)) := (CFC.conjSqrt X).continuous.tendsto _ |>.comp hBP
  have hCP : 0 ≤ CFC.conjSqrt X P := by
    simpa using CFC.conjSqrt_monotone (c := X) P_nonneg
  have hsqrt : Tendsto (fun s ↦ CFC.sqrt (CFC.conjSqrt X (F s ^ p)))
      l (𝓝 (CFC.sqrt (CFC.conjSqrt X P))) := by
    simp only [CFC.sqrt_eq_rpow]
    apply positive_power_limit _ hCP hC (by norm_num)
    filter_upwards [hF] with s hs
    have hb := (hs.isStrictlyPositive.rpow _ p)
    exact ((CFC.isStrictlyPositive_conjSqrt_iff X _ hX.isStrictlyPositive).2 hb).nonneg
  have hPXP : P * X * P = m • P := (rank_one_compression X hX).2
  have hroot : CFC.sqrt (CFC.conjSqrt X P) = (1 / Real.sqrt m) • CFC.conjSqrt X P := by
    apply CFC.sqrt_unique _ ((hCP.posSemidef.smul (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt m)).nonneg)
    have hsq : CFC.conjSqrt X P * CFC.conjSqrt X P = m • CFC.conjSqrt X P := by
      simp only [CFC.conjSqrt_apply]
      calc
        _ = CFC.sqrt X * (P * (CFC.sqrt X * CFC.sqrt X) * P) * CFC.sqrt X := by
          simp only [mul_assoc]
        _ = _ := by rw [CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg, hPXP]; simp
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hsq]
    rw [show (1 / Real.sqrt m) * ((1 / Real.sqrt m) * m) = (1 : ℝ) by
      field_simp
      nlinarith [Real.sq_sqrt hm.le]]
    exact one_smul _ _
  have hlimL : Tendsto (fun s ↦ nativeMean p (A) (F s)) l
      (𝓝 ((1 / Real.sqrt m) • P)) := by
    have h := (CFC.conjSqrt (Ring.inverse X)).continuous.tendsto _ |>.comp hsqrt
    rw [hroot, map_smul, CFC.conjSqrt_ringInverse_conjSqrt X P hX.isStrictlyPositive] at h
    simpa only [Function.comp_def, native_sqrt_form p _ _ hp.ne' hA, X] using h
  have hlimW : Tendsto (fun s ↦ nativeMean p (A) (F s) ^ α) l
      (𝓝 ((1 / Real.sqrt m) ^ α • P)) := by
    rw [← projection_power _ _ (by positivity) hα]
    apply positive_power_limit _ (by exact (P_nonneg.posSemidef.smul (by positivity)).nonneg) hlimL hα
    filter_upwards [hF] with s hs
    exact (native_riccati p _ _ hA hs).1.nonneg
  have hout : Tendsto (fun s ↦ nativeMean p (A) (F s) ^ α * X *
      nativeMean p (A) (F s) ^ α) l
      (𝓝 (((1 / Real.sqrt m) ^ α * (1 / Real.sqrt m) ^ α * m) • P)) := by
    have h := (hlimW.mul (tendsto_const_nhds (x := X))).mul hlimW
    simpa only [smul_mul_assoc, mul_smul_comm, hPXP, smul_smul, mul_assoc] using h
  have hco : (1 / Real.sqrt m) ^ α * (1 / Real.sqrt m) ^ α * m = m ^ (1 - α) := by
    have he : (1 / Real.sqrt m) ^ α = m ^ (-α / 2) := by
      rw [Real.div_rpow (by norm_num) (Real.sqrt_nonneg _), Real.one_rpow,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hm.le, one_div, ← Real.rpow_neg hm.le]
      congr 1
      ring
    rw [he, ← Real.rpow_add hm]
    conv_lhs => rhs; rw [← Real.rpow_one m]
    rw [← Real.rpow_add hm]
    congr 1
    ring
  rw [hco] at hout
  have hpow : Tendsto (fun s ↦ (nativeMean p (A) (F s) ^ α * X *
      nativeMean p (A) (F s) ^ α) ^ (1 / p)) l
      (𝓝 ((m ^ (1 - α)) ^ (1 / p) • P)) := by
    rw [← projection_power _ _ (Real.rpow_nonneg hm.le _) (by positivity)]
    apply positive_power_limit _ (P_nonneg.posSemidef.smul (Real.rpow_nonneg hm.le _)).nonneg
      hout (by positivity)
    filter_upwards [hF] with s hs
    have hW := (native_riccati p _ _ hA hs).1.rpow _ α
    exact ((hW.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint X _ hW.isSelfAdjoint).2
      hX.isStrictlyPositive).nonneg
  have h := trace_continuous.tendsto _ |>.comp hpow
  have htr : Matrix.trace P = (1 : ℂ) := by
    norm_num [P, balancedState, Matrix.trace, Fin.sum_univ_two]
  simp only [Function.comp_def, Matrix.trace_smul, htr, Complex.smul_re,
    Complex.one_re, smul_eq_mul, mul_one] at h
  rw [← Real.rpow_mul hm.le, show (1 - α) * (1 / p) = (1 - α) / p by ring] at h
  exact h

private lemma fixed_diagonal_limit (α p t : ℝ) (hα : 0 < α) (hp : 0 < p)
    (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun s ↦ spectralTrace α p (diagonalState t) (balancedState s)) (𝓝[>] 0)
      (𝓝 ((((1 - t) ^ p + t ^ p) / 2) ^ ((1 - α) / p))) := by
  have hF : ∀ᶠ s : ℝ in 𝓝[>] 0, (balancedState s).PosDef := by
    filter_upwards [small_interval] with s hs
    exact (balanced_density hs.1 hs.2).1
  have h := fixed_rank_one_limit α p (diagonalState t) hα hp
    (diagonal_density ht ht1).1 balancedState hF balanced_limit
  have hm : rankMass (diagonalState t ^ p) = ((1 - t) ^ p + t ^ p) / 2 := by
    rw [diagonal_power t p ht ht1]
    simp [rankMass, Matrix.diagonal]
  simpa only [hm] using h

private def weightedColumns (α p s : ℝ) : Mat :=
  let d0 := (1 - s ^ (2 : ℕ)) ^ (p / 2)
  !![((d0 * (small p s ^ α + slope α p s * (entryU p s - small p s)) : ℝ) : ℂ),
      ((scale p s ^ (2 : ℕ) * slope α p s * entryV p s : ℝ) : ℂ);
    ((d0 * slope α p s * entryV p s : ℝ) : ℂ),
      ((scale p s ^ (2 : ℕ) * small p s ^ α + scale p s * slope α p s *
        (scaledW p s - scale p s * small p s) : ℝ) : ℂ)]

private lemma weightedColumns_exact (α p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hs1 : s < 1 / 2) :
    weightedColumns α p s =
      nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α *
        diagonalState (s ^ (2 : ℕ)) ^ (p / 2) := by
  have ht : 0 < s ^ (2 : ℕ) := sq_pos_of_pos hs
  have ht1 : s ^ (2 : ℕ) < 1 := by nlinarith
  rw [actual_power α p s hp hs hs1, diagonal_power _ _ ht ht1]
  have hy : (s ^ (2 : ℕ)) ^ (p / 2) = scale p s ^ (2 : ℕ) :=
    (Real.rpow_pow_comm hs.le (p / 2) 2).symm
  rw [hy]
  unfold weightedColumns
  rw [← (scaled_entries p s hp hs hs1).1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.smul_apply,
      Fin.sum_univ_two, Matrix.one_apply] <;> push_cast <;> ring

private lemma weightedColumns_limit (α p : ℝ) (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    Tendsto (weightedColumns α p) (𝓝[>] 0) (𝓝 (k ^ α • Q)) := by
  obtain ⟨hz, hx, he, hc, hu, hv, hw⟩ := entry_limits p hp
  obtain ⟨hl, hm, hq, hg⟩ := finite_factor_limits α p hα hα1 hp
  have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have hd : Tendsto (fun s : ℝ ↦ (1 - s ^ (2 : ℕ)) ^ (p / 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hone.sub (hid.pow 2)).rpow_const (Or.inr (by positivity : 0 ≤ p / 2))
  have hmα : Tendsto (fun s ↦ small p s ^ α) (𝓝[>] 0) (𝓝 (k ^ α)) :=
    hm.rpow_const (Or.inr hα.le)
  have h00 := hd.mul (hmα.add (hg.mul (hu.sub hm)))
  have h01 := ((hz.pow 2).mul hg).mul hv
  have h10 := (hd.mul hg).mul hv
  have h11 := ((hz.pow 2).mul hmα).add ((hz.mul hg).mul (hw.sub (hz.mul hm)))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [Function.comp_def, weightedColumns, Q, diagonalState, Matrix.smul_apply] using
      (Complex.continuous_ofReal.tendsto _).comp h00
  · simpa [Function.comp_def, weightedColumns, Q, diagonalState, Matrix.smul_apply] using
      (Complex.continuous_ofReal.tendsto _).comp h01
  · simpa [Function.comp_def, weightedColumns, Q, diagonalState, Matrix.smul_apply] using
      (Complex.continuous_ofReal.tendsto _).comp h10
  · simpa [Function.comp_def, weightedColumns, Q, diagonalState, Matrix.smul_apply] using
      (Complex.continuous_ofReal.tendsto _).comp h11

private lemma two_scale_matrix_limit (α p : ℝ) (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    Tendsto (fun s ↦ nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α *
      diagonalState (s ^ (2 : ℕ)) ^ p * nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α)
      (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ (-α) • Q)) := by
  have hE := weightedColumns_limit α p hα hα1 hp
  have h := hE.mul hE.star
  have hQ : (k ^ α • Q) * star (k ^ α • Q) = (k ^ α * k ^ α) • Q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, diagonalState, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.star_apply, Matrix.smul_apply, Fin.sum_univ_two] <;> ring
  rw [hQ, k_square_power] at h
  apply h.congr'
  filter_upwards [small_interval] with s hs
  rw [weightedColumns_exact α p s hp hs.1 hs.2]
  have hA := (diagonal_density (sq_pos_of_pos hs.1) (by nlinarith : s ^ (2 : ℕ) < 1)).1
  have hW := (native_riccati p _ _ hA (balanced_density hs.1 hs.2).1).1.rpow _ α
  have hD := hA.isStrictlyPositive.rpow _ (p / 2)
  rw [star_mul, hW.isSelfAdjoint.star_eq, hD.isSelfAdjoint.star_eq]
  have hDD : diagonalState (s ^ (2 : ℕ)) ^ (p / 2) * diagonalState (s ^ (2 : ℕ)) ^ (p / 2) =
      diagonalState (s ^ (2 : ℕ)) ^ p := by
    rw [← CFC.rpow_add hA.isUnit]
    congr 1
    ring
  calc
    _ = nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α *
      (diagonalState (s ^ (2 : ℕ)) ^ (p / 2) * diagonalState (s ^ (2 : ℕ)) ^ (p / 2)) *
      nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α := by simp only [mul_assoc]
    _ = _ := by rw [hDD]

private lemma two_scale_trace_limit (α p : ℝ) (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    Tendsto (fun s ↦ spectralTrace α p (diagonalState (s ^ (2 : ℕ))) (balancedState s))
      (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ (-α / p))) := by
  have h := two_scale_matrix_limit α p hα hα1 hp
  have hQ : 0 ≤ Q := by
    apply Matrix.PosSemidef.nonneg
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Q, diagonalState]
  have hc : 0 ≤ (2 : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
  have hpow : Tendsto (fun s ↦ (nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α *
      diagonalState (s ^ (2 : ℕ)) ^ p * nativeMean p (diagonalState (s ^ (2 : ℕ))) (balancedState s) ^ α) ^
        (1 / p)) (𝓝[>] 0) (𝓝 (((2 : ℝ) ^ (-α)) ^ (1 / p) • Q)) := by
    rw [← Q_power _ _ hc (by positivity)]
    apply positive_power_limit _ (hQ.posSemidef.smul hc).nonneg h (by positivity)
    filter_upwards [small_interval] with s hs
    have hA := (diagonal_density (sq_pos_of_pos hs.1) (by nlinarith : s ^ (2 : ℕ) < 1)).1
    have hW := (native_riccati p _ _ hA (balanced_density hs.1 hs.2).1).1.rpow _ α
    exact ((hW.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
      (diagonalState (s ^ (2 : ℕ)) ^ p) _ hW.isSelfAdjoint).2 (hA.isStrictlyPositive.rpow _ p)).nonneg
  have hscalar : ((2 : ℝ) ^ (-α)) ^ (1 / p) = (2 : ℝ) ^ (-α / p) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have ht := trace_continuous.tendsto _ |>.comp hpow
  have htr : Matrix.trace Q = (1 : ℂ) := by
    norm_num [Q, diagonalState, Matrix.trace, Fin.sum_univ_two]
  simp only [Function.comp_def, Matrix.trace_smul, htr, Complex.smul_re,
    Complex.one_re, smul_eq_mul, mul_one] at ht
  rw [hscalar] at ht
  exact ht

private lemma lower_half_witness (α p : ℝ) (hα : 0 < α) (hαh : α < 1 / 2) (hp : 0 < p) :
    ∃ s ell : ℝ, 0 < s ∧ s < 1 / 2 ∧ s ^ (2 : ℕ) < interior α p ∧ 0 < ell ∧ ell < 1 / 2 ∧
      diagonalState (interior α p) = (1 - ell) • diagonalState (s ^ (2 : ℕ)) +
        ell • diagonalState (1 - s ^ (2 : ℕ)) ∧
      spectralTrace α p (diagonalState (interior α p)) (balancedState s) <
        (1 - ell) * spectralTrace α p (diagonalState (s ^ (2 : ℕ))) (balancedState s) +
        ell * spectralTrace α p (diagonalState (1 - s ^ (2 : ℕ))) (balancedState s) := by
  obtain ⟨hτ, hτ1, hgap⟩ := interior_gap α p hα hαh hp
  have hτlt : interior α p < 1 := by linarith
  have hlim := (two_scale_trace_limit α p hα (by linarith) hp).sub
    (fixed_diagonal_limit α p (interior α p) hα hp hτ hτlt)
  have hg : ∀ᶠ s : ℝ in 𝓝[>] 0,
      0 < spectralTrace α p (diagonalState (s ^ (2 : ℕ))) (balancedState s) -
        spectralTrace α p (diagonalState (interior α p)) (balancedState s) :=
    hlim.eventually (Ioi_mem_nhds (sub_pos.mpr hgap))
  have hsqt : ∀ᶠ s : ℝ in 𝓝[>] 0, s ^ (2 : ℕ) < interior α p :=
    (show Tendsto (fun s : ℝ ↦ s ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 0) by
      simpa using (show Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).pow 2).eventually
        (Iio_mem_nhds hτ)
  obtain ⟨s, ⟨hs, hst⟩, hsg⟩ := ((small_interval.and hsqt).and hg).exists
  let ell := (interior α p - s ^ (2 : ℕ)) / (1 - 2 * s ^ (2 : ℕ))
  obtain ⟨hell, hell1, he⟩ := affine_coordinate (s ^ (2 : ℕ)) (interior α p) (sq_nonneg s) hst (by linarith)
  refine ⟨s, ell, hs.1, hs.2, hst, hell, hell1, he, ?_⟩
  rw [equal_endpoints α p (s ^ (2 : ℕ)) s (sq_pos_of_pos hs.1) (by nlinarith) hs.1 hs.2]
  nlinarith

/-- Literal real, faithful density witnesses with the exact affine coordinates. -/
def WitnessGeometry (τ s ell : ℝ) : Prop :=
  0 < τ ∧ τ < 1 / 2 ∧ 0 < s ∧ s < 1 / 2 ∧ s ^ (2 : ℕ) < τ ∧ 0 < ell ∧ ell < 1 / 2 ∧
    Density (diagonalState (s ^ (2 : ℕ))) ∧ Density (diagonalState (1 - s ^ (2 : ℕ))) ∧
    Density (diagonalState τ) ∧ Density (balancedState s) ∧
    diagonalState τ = (1 - ell) • diagonalState (s ^ (2 : ℕ)) + ell • diagonalState (1 - s ^ (2 : ℕ)) ∧
    diagonalState (s ^ (2 : ℕ)) * balancedState s ≠ balancedState s * diagonalState (s ^ (2 : ℕ)) ∧
    diagonalState (1 - s ^ (2 : ℕ)) * balancedState s ≠ balancedState s * diagonalState (1 - s ^ (2 : ℕ)) ∧
    diagonalState τ * balancedState s ≠ balancedState s * diagonalState τ

private lemma witness_geometry (τ s ell : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1 / 2) (hst : s ^ (2 : ℕ) < τ) (hell : 0 < ell) (hell1 : ell < 1 / 2)
    (he : diagonalState τ = (1 - ell) • diagonalState (s ^ (2 : ℕ)) + ell • diagonalState (1 - s ^ (2 : ℕ))) :
    WitnessGeometry τ s ell := by
  have ht : 0 < s ^ (2 : ℕ) := sq_pos_of_pos hs
  have ht1 : s ^ (2 : ℕ) < 1 := by nlinarith
  refine ⟨hτ, hτ1, hs, hs1, hst, hell, hell1, diagonal_density ht ht1,
    diagonal_density (by linarith) (by linarith), diagonal_density hτ (by linarith),
    balanced_density hs hs1, he, ?_, ?_, ?_⟩
  · exact genuinely_noncommuting _ _ (by linarith) (by linarith)
  · exact genuinely_noncommuting _ _ (by linarith) (by linarith)
  · exact genuinely_noncommuting _ _ (by linarith) (by linarith)

/-- Every off-midpoint parameter has a strict affine violation with the required fixed argument. -/
theorem off_midpoint_violation (α p : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hαne : α ≠ 1 / 2) (hp : 0 < p) :
    ∃ τ s ell : ℝ, WitnessGeometry τ s ell ∧
      (α < 1 / 2 → spectralTrace α p (diagonalState τ) (balancedState s) <
        (1 - ell) * spectralTrace α p (diagonalState (s ^ (2 : ℕ))) (balancedState s) +
          ell * spectralTrace α p (diagonalState (1 - s ^ (2 : ℕ))) (balancedState s)) ∧
      (1 / 2 < α → spectralTrace α p (balancedState s) (diagonalState τ) <
        (1 - ell) * spectralTrace α p (balancedState s) (diagonalState (s ^ (2 : ℕ))) +
          ell * spectralTrace α p (balancedState s) (diagonalState (1 - s ^ (2 : ℕ)))) := by
  rcases lt_or_gt_of_ne hαne with hlo | hhi
  · obtain ⟨s, ell, hs, hs1, hst, hell, hell1, he, hv⟩ := lower_half_witness α p hα hlo hp
    obtain ⟨hτ, hτ1, _⟩ := interior_gap α p hα hlo hp
    exact ⟨interior α p, s, ell,
      witness_geometry _ _ _ hτ (by linarith) hs hs1 hst hell hell1 he,
      fun _ ↦ hv, fun h ↦ (not_lt_of_ge hlo.le h).elim⟩
  · let β := 1 - α
    have hβ : 0 < β := by dsimp [β]; linarith
    have hβh : β < 1 / 2 := by dsimp [β]; linarith
    obtain ⟨s, ell, hs, hs1, hst, hell, hell1, he, hv⟩ := lower_half_witness β p hβ hβh hp
    obtain ⟨hτ, hτ1, _⟩ := interior_gap β p hβ hβh hp
    have hg := witness_geometry _ _ _ hτ (by linarith) hs hs1 hst hell hell1 he
    refine ⟨interior β p, s, ell, hg, fun h ↦ (not_lt_of_ge hhi.le h).elim, fun _ ↦ ?_⟩
    have hd0 := (diagonal_density (sq_pos_of_pos hs) (by nlinarith : s ^ (2 : ℕ) < 1)).1
    have hd1 := (diagonal_density (by nlinarith : 0 < 1 - s ^ (2 : ℕ))
      (by nlinarith : 1 - s ^ (2 : ℕ) < 1)).1
    have hdτ := (diagonal_density hτ (by linarith : interior β p < 1)).1
    have hb := (balanced_density hs hs1).1
    simpa only [β, complement α p (balancedState s) (diagonalState (interior β p)) hb hdτ,
      complement α p (balancedState s) (diagonalState (s ^ (2 : ℕ))) hb hd0,
      complement α p (balancedState s) (diagonalState (1 - s ^ (2 : ℕ))) hb hd1] using hv

/-- Existence of any off-midpoint pair with joint concavity on the specified density domain. -/
def claim : Prop := ∃ α p : ℝ, 0 < α ∧ α < 1 ∧ α ≠ 1 / 2 ∧ 0 < p ∧
  GeneralizedPerspectiveFunction.JointlyConcaveOn {A : Mat | Density A} {B : Mat | Density B}
    (spectralTrace α p)

/-- The existential off-midpoint joint-concavity claim is false. -/
theorem result : ¬ claim := by
  rintro ⟨α, p, hα, hα1, hαne, hp, hc⟩
  obtain ⟨τ, s, ell, hg, hlo, hhi⟩ := off_midpoint_violation α p hα hα1 hαne hp
  rcases hg with ⟨hτ, hτ1, hs, hs1, hst, hell, hell1, hd0, hd1, hdτ, hb, he, hn0, hn1, hnτ⟩
  have hmix (M : Mat) : (1 - ell) • M + ell • M = M := by
    rw [← add_smul, show (1 - ell) + ell = (1 : ℝ) by ring, one_smul]
  rcases lt_or_gt_of_ne hαne with hαh | hhα
  · have h := hc (θ := ell) hd0 hd1 hb hb hell.le (by linarith : ell ≤ 1)
    rw [hmix, ← he] at h
    exact not_lt_of_ge h (hlo hαh)
  · have h := hc (θ := ell) hb hb hd0 hd1 hell.le (by linarith : ell ≤ 1)
    rw [hmix, ← he] at h
    exact not_lt_of_ge h (hhi hhα)

#check claim
#check result
#print axioms off_midpoint_violation
#print axioms result

end D5.S3.Quantum.Hiai.SpectralNonconcavity
