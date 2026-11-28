/- GID: D5/S3/Geometry/Lorentz/ADMHamiltonianGravity4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/ADMHamiltonianGravity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ADM splitting, the gravitational kinetic form, and exact conformal mass identities. -/

import OmegaBuild.Commands
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
import D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
import D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
import D5.S3.Analysis.InverseDistanceRays

/-! The ADM metric is a congruence of the temporal and spatial blocks.
The Legendre map acts by a different scalar on the trace and shear directions. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D

private abbrev timeSpace : Fin 1 ⊕ Fin 3 ≃ Fin 4 := finSumFinEquiv
private abbrev toFinFour := Matrix.reindexRingEquiv ℝ timeSpace
private abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
private abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

private def timeBlock (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![t]

private def shiftColumn (β : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  Matrix.of fun i _ => β i

private def shiftBlocks (β : Fin 3 → ℝ) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fromBlocks 1 0 (shiftColumn β) 1

/-- The change from coordinate components to normal and spatial components. -/
def admShiftMatrix (β : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  toFinFour (shiftBlocks β)

def admMetric (N : ℝ) (β : Fin 3 → ℝ) (γ : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let B := shiftColumn β
  toFinFour (fromBlocks (timeBlock (-(N ^ 2)) + Bᵀ * γ * B) (Bᵀ * γ) (γ * B) γ)

def admInvMetric (N : ℝ) (β : Fin 3 → ℝ) (γInv : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let S := admShiftMatrix (-β)
  S * toFinFour (fromBlocks (timeBlock (-(N ^ 2)⁻¹)) 0 0 γInv) * Sᵀ

theorem admMetric_congruence_factorization (N : ℝ) (β : Fin 3 → ℝ) (γ : Mat3) :
    admMetric N β γ =
      (admShiftMatrix β)ᵀ *
        (fromBlocks (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 γ).reindex
          finSumFinEquiv finSumFinEquiv *
        admShiftMatrix β := by
  change toFinFour _ =
    toFinFour (shiftBlocks β)ᵀ * toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) *
      toFinFour (shiftBlocks β)
  rw [← map_mul, ← map_mul]
  congr 1
  simp [shiftBlocks, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_assoc]

private theorem shift_inverse (β : Fin 3 → ℝ) :
    admShiftMatrix β * admShiftMatrix (-β) = 1 := by
  have hc : shiftColumn (-β) = -(shiftColumn β) := rfl
  rw [admShiftMatrix, admShiftMatrix, ← map_mul, ← map_one toFinFour]
  simp [shiftBlocks, fromBlocks_multiply, hc, fromBlocks_one]

private theorem timeBlock_mul (x y : ℝ) : timeBlock x * timeBlock y = timeBlock (x * y) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hi, hj, timeBlock, Matrix.mul_apply]

private theorem timeBlock_one : timeBlock 1 = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hi, hj, timeBlock, Matrix.one_apply]

private theorem diagonal_mul (x y : ℝ) (G H : Mat3) (ht : x * y = 1) (hg : G * H = 1) :
    toFinFour (fromBlocks (timeBlock x) 0 0 G) *
      toFinFour (fromBlocks (timeBlock y) 0 0 H) = 1 := by
  rw [← map_mul, fromBlocks_multiply]
  simp [timeBlock_mul, ht, hg, timeBlock_one, fromBlocks_one]

theorem admMetric_mul_inv {N : ℝ} (hN : N ≠ 0) (β : Fin 3 → ℝ) {γ γInv : Mat3}
    (hRight : γ * γInv = 1) (hLeft : γInv * γ = 1) :
    admMetric N β γ * admInvMetric N β γInv = 1 ∧
      admInvMetric N β γInv * admMetric N β γ = 1 := by
  have hS := shift_inverse β
  have hT : admShiftMatrix (-β) * admShiftMatrix β = 1 := by
    simpa using shift_inverse (-β)
  have hST := congrArg Matrix.transpose hS
  have hTS := congrArg Matrix.transpose hT
  rw [transpose_mul, transpose_one] at hST hTS
  have htime : (-(N ^ 2)) * (-(N ^ 2)⁻¹) = 1 := by
    rw [neg_mul_neg, mul_inv_cancel₀ (pow_ne_zero 2 hN)]
  have hd := diagonal_mul _ _ γ γInv htime hRight
  have he := diagonal_mul (-(N ^ 2)⁻¹) (-(N ^ 2)) γInv γ
    ((mul_comm ..).trans htime) hLeft
  rw [admMetric_congruence_factorization, admInvMetric]
  change (_ * toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) * _) * (_ * _ * _) = 1 ∧
    (_ * _ * _) * (_ * toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) * _) = 1
  constructor
  · rw [mul_assoc (_ * _), ← mul_assoc (admShiftMatrix β), ← mul_assoc (admShiftMatrix β),
      hS, one_mul, ← mul_assoc, mul_assoc (admShiftMatrix β)ᵀ, hd, mul_one, hTS]
  · rw [mul_assoc (_ * _), ← mul_assoc (_ᵀ), ← mul_assoc (_ᵀ), hST, one_mul,
      ← mul_assoc, mul_assoc (admShiftMatrix (-β)), he, mul_one, hT]

theorem admMetric_det_and_volume (N : ℝ) (β : Fin 3 → ℝ) (γ : Mat3) :
    (admMetric N β γ).det = -(N ^ 2) * γ.det ∧
      (0 < N → 0 ≤ γ.det → Real.sqrt (-(admMetric N β γ).det) = N * Real.sqrt γ.det) := by
  have hS : (admShiftMatrix β).det = 1 := by
    change (Matrix.reindex timeSpace timeSpace (shiftBlocks β)).det = 1
    rw [det_reindex_self, shiftBlocks, det_fromBlocks_zero₁₂, det_one, det_one, mul_one]
  have hd : (admMetric N β γ).det = -(N ^ 2) * γ.det := by
    rw [admMetric_congruence_factorization, det_mul, det_mul, det_transpose, hS,
      det_reindex_self, det_fromBlocks_zero₂₁, det_fin_one_of, one_mul, mul_one]
  exact ⟨hd, fun hN _ => by
    rw [hd, neg_mul, neg_neg, Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]⟩

def nUp (N : ℝ) (β : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cons (1 / N) (fun i => -β i / N)

def eSpatial (i : Fin 3) : Fin 4 → ℝ := Fin.cons 0 (Pi.single i 1)

@[simp] private theorem timeSpace_inl (i : Fin 1) : timeSpace (Sum.inl i) = 0 := by
  rw [show i = 0 from Subsingleton.elim _ _]
  rfl

@[simp] private theorem timeSpace_inr (i : Fin 3) : timeSpace (Sum.inr i) = i.succ := by
  apply Fin.ext
  exact Nat.add_comm 1 i.val

@[simp] private theorem timeSpace_zero : timeSpace.symm 0 = Sum.inl 0 :=
  timeSpace.symm_apply_eq.mpr (timeSpace_inl _).symm

@[simp] private theorem timeSpace_succ (i : Fin 3) : timeSpace.symm i.succ = Sum.inr i :=
  timeSpace.symm_apply_eq.mpr (timeSpace_inr _).symm

private theorem toFinFour_mulVec (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (v : Fin 4 → ℝ) : toFinFour M *ᵥ v = (M *ᵥ (v ∘ timeSpace)) ∘ timeSpace.symm :=
  Matrix.submatrix_mulVec_equiv M v timeSpace.symm timeSpace.symm

private theorem shift_mulVec (β : Fin 3 → ℝ) (v : Fin 4 → ℝ) :
    admShiftMatrix β *ᵥ v = Fin.cons (v 0) (fun i => v i.succ + v 0 * β i) := by
  rw [admShiftMatrix, toFinFour_mulVec, shiftBlocks, fromBlocks_mulVec]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Function.comp_def]
  · simp [Function.comp_def, mulVec, dotProduct, shiftColumn, add_comm, mul_comm]

private theorem diagonal_mulVec (t : ℝ) (γ : Mat3) (v : Fin 4 → ℝ) :
    toFinFour (fromBlocks (timeBlock t) 0 0 γ) *ᵥ v =
      Fin.cons (t * v 0) (γ *ᵥ fun i => v i.succ) := by
  rw [toFinFour_mulVec, fromBlocks_mulVec]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Function.comp_def, dotProduct, timeBlock]
  · simp [Function.comp_def]

private theorem shift_transpose_time (β : Fin 3 → ℝ) (t : ℝ) :
    (admShiftMatrix β)ᵀ *ᵥ Fin.cons t (fun _ => 0) = Fin.cons t (fun _ => 0) := by
  change toFinFour (shiftBlocks β)ᵀ *ᵥ _ = _
  rw [toFinFour_mulVec, shiftBlocks, fromBlocks_transpose, fromBlocks_mulVec]
  have hz : ((Fin.cons t (fun _ : Fin 3 => 0) : Fin 4 → ℝ) ∘ timeSpace) ∘ Sum.inr = 0 := by
    funext i
    simp [Function.comp_def]
  rw [hz]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Function.comp_def]

private theorem shift_normal (N : ℝ) (β : Fin 3 → ℝ) :
    admShiftMatrix β *ᵥ nUp N β = Fin.cons (1 / N) (fun _ => 0) := by
  rw [shift_mulVec]
  congr 1
  funext i
  simp [nUp, div_eq_mul_inv, mul_comm]

theorem adm_unit_timelike_normal {N : ℝ} (hN : N ≠ 0) (β : Fin 3 → ℝ) (γ : Mat3) :
    nUp N β ⬝ᵥ (admMetric N β γ *ᵥ nUp N β) = -1 ∧
      (∀ i : Fin 3, nUp N β ⬝ᵥ (admMetric N β γ *ᵥ eSpatial i) = 0) ∧
      admMetric N β γ *ᵥ nUp N β = Fin.cons (-N) (fun _ => 0) := by
  have hc : admMetric N β γ *ᵥ nUp N β = Fin.cons (-N) (fun _ => 0) := by
    rw [admMetric_congruence_factorization, ← mulVec_mulVec, ← mulVec_mulVec, shift_normal]
    change (admShiftMatrix β)ᵀ *ᵥ (toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) *ᵥ _) = _
    rw [diagonal_mulVec]
    let v : Fin 4 → ℝ := Fin.cons (1 / N) (fun _ : Fin 3 => 0)
    have hz : (fun i : Fin 3 => v i.succ) = 0 := by
      funext i
      simp [v]
    change (admShiftMatrix β)ᵀ *ᵥ Fin.cons (_ * v 0) (γ *ᵥ fun i => v i.succ) = _
    rw [hz, mulVec_zero]
    have ht : (-(N ^ 2)) * v 0 = -N := by
      simp only [v, Fin.cons_zero]
      field_simp
    rw [ht]
    exact shift_transpose_time β (-N)
  refine ⟨?_, ?_, hc⟩
  · rw [hc, dotProduct, Fin.sum_univ_succ]
    simp [nUp, hN]
  · intro i
    rw [admMetric_congruence_factorization, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_transpose_mulVec, shift_normal, shift_mulVec]
    change (toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) *ᵥ _) ⬝ᵥ
      Fin.cons (1 / N) (fun _ : Fin 3 => 0) = _
    rw [diagonal_mulVec, dotProduct, Fin.sum_univ_succ]
    simp [eSpatial]

theorem adm_lorentzian_signature {N : ℝ} (hN : 0 < N) (β : Fin 3 → ℝ) (γ : Mat3)
    (hSym : γᵀ = γ)
    (hγ : ∀ w : Fin 3 → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (γ *ᵥ w)) :
    (∀ v : Fin 4 → ℝ,
      let w := fun i : Fin 3 => v i.succ + v 0 * β i
      v ⬝ᵥ (admMetric N β γ *ᵥ v) = -(N * v 0) ^ 2 + w ⬝ᵥ (γ *ᵥ w)) ∧
      nUp N β ⬝ᵥ (admMetric N β γ *ᵥ nUp N β) < 0 ∧
      (∀ v : Fin 4 → ℝ, v 0 = 0 → v ≠ 0 → 0 < v ⬝ᵥ (admMetric N β γ *ᵥ v)) ∧
      (admMetric N β γ)ᵀ = admMetric N β γ := by
  have hq (v : Fin 4 → ℝ) :
      let w := fun i : Fin 3 => v i.succ + v 0 * β i
      v ⬝ᵥ (admMetric N β γ *ᵥ v) = -(N * v 0) ^ 2 + w ⬝ᵥ (γ *ᵥ w) := by
    rw [admMetric_congruence_factorization, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_transpose_mulVec, shift_mulVec]
    dsimp only
    rw [dotProduct_comm]
    change _ ⬝ᵥ (toFinFour (fromBlocks (timeBlock (-(N ^ 2))) 0 0 γ) *ᵥ _) = _
    simp only [diagonal_mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring
  refine ⟨hq, ?_, ?_, ?_⟩
  · rw [(adm_unit_timelike_normal hN.ne' β γ).1]
    norm_num
  · intro v h0 hv
    have hs : (fun i : Fin 3 => v i.succ) ≠ 0 := by
      intro hs
      apply hv
      funext i
      refine Fin.cases h0 (fun j => congrFun hs j) i
    simpa [hq v, h0] using hγ (fun i : Fin 3 => v i.succ) hs
  · have hD : (fromBlocks (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 γ)ᵀ =
        fromBlocks (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 γ := by
      have hT : (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = !![-(N ^ 2)] := by
        ext i j
        rw [show i = j from Subsingleton.elim _ _]
        rfl
      rw [fromBlocks_transpose, transpose_zero, transpose_zero, hSym, hT]
    have he : ∀ A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ,
        (toFinFour A)ᵀ = toFinFour Aᵀ := fun _ => rfl
    rw [admMetric_congruence_factorization, transpose_mul, transpose_mul, transpose_transpose]
    change (admShiftMatrix β)ᵀ *
      ((toFinFour (fromBlocks (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 γ))ᵀ *
        admShiftMatrix β) = _
    rw [he, hD, ← mul_assoc]
    rfl

def admMomentum (sdetγ : ℝ) (K : Mat3) : Mat3 :=
  sdetγ • (K - K.trace • 1)

def admExtrinsicFromMomentum (sdetγ : ℝ) (P : Mat3) : Mat3 :=
  (1 / sdetγ) • (P - ((1 / 2 : ℝ) * P.trace) • 1)

def dewittKinetic (P : Mat3) : ℝ := (P * P).trace - (1 / 2) * P.trace ^ 2

private theorem trace_one_three : (1 : Mat3).trace = (3 : ℝ) := by
  norm_num [Matrix.trace_one]

private theorem trace_shift_sq (P : Mat3) (b : ℝ) :
    ((P - b • 1) * (P - b • 1)).trace =
      (P * P).trace - 2 * b * P.trace + 3 * b ^ 2 := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.mul_one, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, trace_one_three]
  ring

private theorem trace_momentum (s : ℝ) (K : Mat3) :
    (admMomentum s K).trace = -2 * s * K.trace := by
  simp [admMomentum, Matrix.trace_sub]
  ring

theorem adm_legendre_transform_involution {sdetγ : ℝ} (hs : sdetγ ≠ 0) (K P : Mat3) :
    admExtrinsicFromMomentum sdetγ (admMomentum sdetγ K) = K ∧
      admMomentum sdetγ (admExtrinsicFromMomentum sdetγ P) = P ∧
      (admMomentum sdetγ K).trace = -2 * sdetγ * K.trace ∧
      (K * K).trace - K.trace ^ 2 = (1 / sdetγ ^ 2) * dewittKinetic (admMomentum sdetγ K) := by
  have htrace : (admExtrinsicFromMomentum sdetγ P).trace = -(1 / (2 * sdetγ)) * P.trace := by
    simp only [admExtrinsicFromMomentum, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul,
      trace_one_three]
    ring
  refine ⟨?_, ?_, trace_momentum _ _, ?_⟩
  · rw [admExtrinsicFromMomentum, trace_momentum, admMomentum]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp [hs]
    ring
  · rw [admMomentum, htrace, admExtrinsicFromMomentum]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp [hs]
    ring
  · rw [dewittKinetic, trace_momentum, admMomentum]
    simp only [smul_mul_assoc, mul_smul_comm,
      smul_smul, Matrix.trace_smul, smul_eq_mul, trace_shift_sq]
    field_simp
    ring

private theorem trace_mul_self_pos (P : Mat3) (hP : Pᵀ = P) (hn : P ≠ 0) :
    0 < (P * P).trace := by
  have hs (i j : Fin 3) : P j i = P i j :=
    congrArg (fun A : Mat3 => A i j) hP
  have hsum : (P * P).trace = ∑ i, ∑ j, (P i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs i j, pow_two]
  obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra! h
    exact hn (Matrix.ext fun i j => by simp [h])
  rw [hsum]
  apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (P i j))
  exact ⟨i, Finset.mem_univ i, Finset.sum_pos' (fun j _ => sq_nonneg (P i j))
    ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hij⟩⟩

theorem dewitt_supermetric_lorentzian_signature :
    (∀ P : Mat3, Pᵀ = P →
      let Ptf := P - (P.trace / 3) • 1
      P = (P.trace / 3) • 1 + Ptf ∧ Ptf.trace = 0 ∧ Ptfᵀ = Ptf ∧
        dewittKinetic P = -(1 / 6) * P.trace ^ 2 + (Ptf * Ptf).trace) ∧
      (∀ μ : ℝ, μ ≠ 0 → dewittKinetic (μ • (1 : Mat3)) = -(3 / 2) * μ ^ 2 ∧
        dewittKinetic (μ • (1 : Mat3)) < 0) ∧
      (∀ P : Mat3, Pᵀ = P → P.trace = 0 → P ≠ 0 →
        dewittKinetic P = (P * P).trace ∧ 0 < (P * P).trace) ∧
      (∀ P : Mat3, Pᵀ = P → P.trace = 0 → ∃! v : Fin 5 → ℝ,
        P = !![v 0, v 2, v 3; v 2, v 1, v 4; v 3, v 4, -v 0 - v 1]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    dsimp
    refine ⟨by abel, ?_, by rw [transpose_sub, transpose_smul, transpose_one, hP], ?_⟩
    · simp only [Matrix.trace_sub, Matrix.trace_smul, trace_one_three, smul_eq_mul]
      ring
    · unfold dewittKinetic
      rw [trace_shift_sq]
      ring
  · intro μ hμ
    have h : dewittKinetic (μ • (1 : Mat3)) = -(3 / 2) * μ ^ 2 := by
      simp only [dewittKinetic, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_one,
        Matrix.trace_smul, trace_one_three, smul_eq_mul]
      ring
    exact ⟨h, h ▸ mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero hμ)⟩
  · intro P hP htr hn
    exact ⟨by simp [dewittKinetic, htr], trace_mul_self_pos P hP hn⟩
  · intro P hP htr
    have hsym (i j : Fin 3) : P i j = P j i := (congrArg (fun A : Mat3 => A i j) hP).symm
    refine ⟨![P 0 0, P 1 1, P 0 1, P 0 2, P 1 2], ?_, ?_⟩
    · rw [Matrix.trace_fin_three] at htr
      ext i j
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact hsym _ _
      | change P 2 2 = -P 0 0 - P 1 1; linarith
    · intro v hv
      funext i
      fin_cases i <;> first
      | exact (congrArg (fun A : Mat3 => A 0 0) hv).symm
      | exact (congrArg (fun A : Mat3 => A 1 1) hv).symm
      | exact (congrArg (fun A : Mat3 => A 0 1) hv).symm
      | exact (congrArg (fun A : Mat3 => A 0 2) hv).symm
      | exact (congrArg (fun A : Mat3 => A 1 2) hv).symm

theorem adm_hamiltonian_constraint_reproduces_friedmann {a : ℝ → ℝ} {t : ℝ}
    (ha : 0 < a t) (k Λ G ρ : ℝ) :
    let γInv : Mat3 := (1 / a t ^ 2) • 1
    let K : Mat3 := (a t * deriv a t) • 1
    let Kmixed := γInv * K
    let H := FLRWCosmologyFriedmann4D.hubble a t
    (Kmixed * Kmixed).trace - Kmixed.trace ^ 2 - 6 * k / a t ^ 2 + 2 * Λ +
        16 * Real.pi * G * ρ = 0 ↔
      3 * H ^ 2 = 8 * Real.pi * G * ρ + Λ - 3 * k / a t ^ 2 := by
  dsimp only
  have hK : ((1 / a t ^ 2) • (1 : Mat3)) * ((a t * deriv a t) • 1) =
      (FLRWCosmologyFriedmann4D.hubble a t) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
    congr 1
    unfold FLRWCosmologyFriedmann4D.hubble
    field_simp
  rw [hK]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.one_mul,
    Matrix.trace_smul, trace_one_three, smul_eq_mul]
  constructor
  · intro h
    linear_combination -(1 / 2 : ℝ) * h
  · intro h
    linear_combination -2 * h

section Radial

open Filter OmegaMath.InverseDistanceThree
open PenroseHawkingSingularityBPS4D (mpPotential r3 majumdar_papapetrou_harmonic)
open scoped BigOperators Topology

/-- The flat three-dimensional Laplacian on radial profiles away from the origin. -/
def radialLaplacian (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv ψ) r + (2 / r) * deriv ψ r

/-- The scalar curvature expression for a radial conformal factor in dimension three. -/
def conformalScalarCurvature (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -8 * ψ r ^ (-5 : ℤ) * radialLaplacian ψ r

def schwPsi (M r : ℝ) : ℝ := 1 + M / (2 * r)

private theorem schwPsi_hasDerivAt (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwPsi M) (-(M / 2) / r ^ 2) r := by
  convert (hasDerivAt_inv hr).const_mul (M / 2) |>.const_add 1 using 1
  · funext s
    rw [schwPsi, div_mul_eq_div_div, div_eq_mul_inv]
  · ring

theorem lichnerowicz_radial_harmonic_vanishing (M : ℝ) {r : ℝ} (hr : 0 < r) :
    radialLaplacian (schwPsi M) r = 0 ∧ conformalScalarCurvature (schwPsi M) r = 0 := by
  have hfirst := (schwPsi_hasDerivAt M hr.ne').deriv
  have hd : HasDerivAt (fun s : ℝ => -(M / 2) / s ^ 2) (M / r ^ 3) r := by
    convert (((hasDerivAt_id' r).pow 2).inv (pow_ne_zero 2 hr.ne')).const_mul (-(M / 2)) using 1
    · funext s
      rfl
    · simp only [Pi.pow_apply]
      field_simp [hr.ne']
      ring
  have hsecond : HasDerivAt (deriv (schwPsi M)) (M / r ^ 3) r := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hr.ne'] with s hs
    exact (schwPsi_hasDerivAt M hs).deriv
  have hzero : radialLaplacian (schwPsi M) r = 0 := by
    rw [radialLaplacian, hsecond.deriv, hfirst]
    field_simp [hr.ne']
    ring
  exact ⟨hzero, by simp [conformalScalarCurvature, hzero]⟩

def isotropicArealRadius (M r : ℝ) : ℝ := r * (schwPsi M r) ^ 2

def isotropicInversion (M r : ℝ) : ℝ := M ^ 2 / (4 * r)

private theorem inversion_hasDerivAt (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (isotropicInversion M) (-(M ^ 2 / 4) / r ^ 2) r := by
  convert (hasDerivAt_inv hr).const_mul (M ^ 2 / 4) using 1
  · funext s
    rw [isotropicInversion, div_mul_eq_div_div, div_eq_mul_inv]
  · ring

theorem isotropic_schwarzschild_throat_and_inversion_isometry {M r : ℝ}
    (hM : 0 < M) (hr : 0 < r) :
    isotropicArealRadius M (isotropicInversion M r) = isotropicArealRadius M r ∧
    (schwPsi M (isotropicInversion M r)) ^ 4 * (deriv (isotropicInversion M) r) ^ 2 =
      (schwPsi M r) ^ 4 ∧
    isotropicInversion M (isotropicInversion M r) = r ∧
    (isotropicInversion M r < M / 2 ↔ M / 2 < r) ∧
    (r < M / 2 ↔ M / 2 < isotropicInversion M r) ∧
    2 * M ≤ isotropicArealRadius M r ∧ (isotropicArealRadius M r = 2 * M ↔ r = M / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold isotropicArealRadius schwPsi isotropicInversion
    field_simp [hM.ne', hr.ne']
    ring
  · rw [(inversion_hasDerivAt M hr.ne').deriv]
    unfold schwPsi isotropicInversion
    field_simp [hM.ne', hr.ne']
    ring
  · unfold isotropicInversion
    field_simp [hM.ne', hr.ne']
  · rw [isotropicInversion, div_lt_iff₀ (by positivity : 0 < 4 * r)]
    rw [show M ^ 2 = (2 * M) * (M / 2) by ring,
      show M / 2 * (4 * r) = (2 * M) * r by ring, mul_lt_mul_iff_right₀ (by positivity : 0 < 2 * M)]
  · rw [isotropicInversion, lt_div_iff₀ (by positivity : 0 < 4 * r),
      show M / 2 * (4 * r) = (2 * M) * r by ring,
      show M ^ 2 = (2 * M) * (M / 2) by ring, mul_lt_mul_iff_right₀ (by positivity : 0 < 2 * M)]
  · have he : isotropicArealRadius M r - 2 * M = (r - M / 2) ^ 2 / r := by
      unfold isotropicArealRadius schwPsi
      field_simp [hr.ne']
      ring
    linarith [show 0 ≤ (r - M / 2) ^ 2 / r by positivity]
  · have he : isotropicArealRadius M r - 2 * M = (r - M / 2) ^ 2 / r := by
      unfold isotropicArealRadius schwPsi
      field_simp [hr.ne']
      ring
    rw [← sub_eq_zero, he, div_eq_zero_iff, or_iff_left hr.ne', pow_eq_zero_iff (by decide)]
    exact sub_eq_zero

def conformalADMMass (ψ : ℝ → ℝ) (R : ℝ) : ℝ :=
  -2 * R ^ 2 * (ψ R) ^ 3 * deriv ψ R

def komarSchwarzschildMass (M R : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * (4 * Real.pi * R ^ 2) * (M / R ^ 2)

theorem schwarzschild_adm_mass_limit_and_komar_invariance (M : ℝ) :
    (∀ R > 0, conformalADMMass (schwPsi M) R = M * (1 + M / (2 * R)) ^ 3) ∧
    Tendsto (conformalADMMass (schwPsi M)) atTop (𝓝 M) ∧
    (∀ R > 0, komarSchwarzschildMass M R = M) := by
  have hmass (R : ℝ) (hR : 0 < R) :
      conformalADMMass (schwPsi M) R = M * (1 + M / (2 * R)) ^ 3 := by
    rw [conformalADMMass, (schwPsi_hasDerivAt M hR.ne').deriv, schwPsi]
    field_simp [hR.ne']
  refine ⟨hmass, ?_, ?_⟩
  · have hp : Tendsto (schwPsi M) atTop (𝓝 1) := by
      change Tendsto (fun R : ℝ => 1 + M / (2 * R)) atTop (𝓝 1)
      simp_rw [div_mul_eq_div_div]
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul (M / 2)).const_add 1
    have ht := (hp.pow 3).const_mul M
    simp only [one_pow, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (hmass R hR).symm
  · intro R hR
    unfold komarSchwarzschildMass
    field_simp [Real.pi_ne_zero, hR.ne']

def blPsi {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) (x : Point) : ℝ :=
  1 + ∑ a, m a / (2 * r3 x (c a))

def blADMMass {N : ℕ} (m : Fin N → ℝ) : ℝ := ∑ a, m a

def blBareMass {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) (a : Fin N) : ℝ :=
  m a * (1 + ∑ b ∈ Finset.univ.erase a, m b / (2 * r3 (c a) (c b)))

private theorem blPsi_eq_mpPotential {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) :
    blPsi m c = mpPotential (fun a => m a / 2) c := by
  funext x
  simp only [blPsi, mpPotential, div_mul_eq_div_div]

private theorem bl_scaled_deriv_limit {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point)
    {u : Point} (hu : r3 u 0 = 1) :
    Tendsto (fun R : ℝ => (-2 * R ^ 2) * deriv (fun s : ℝ => blPsi m c (s • u)) R)
      atTop (𝓝 (blADMMass m)) := by
  have ht := tendsto_finsetSum (s := Finset.univ)
    fun a _ => (tendsto_scaled_inverse_deriv hu (c a)).const_mul (m a)
  simp only [mul_one, blADMMass] at ht ⊢
  refine ht.congr' ?_
  have hpos : ∀ᶠ R : ℝ in atTop, ∀ a, 0 < r3 (R • u) (c a) :=
    Filter.eventually_all.mpr fun a =>
      (tendsto_radius_atTop hu (c a)).eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hpos] with R hR
  have hnone (a : Fin N) : R • u ≠ c a := by
    intro he
    have hp := hR a
    change 0 < radius (R • u) (c a) at hp
    rw [he] at hp
    simp [radius, squareDistance] at hp
  have hs (a : Fin N) := hasDerivAt_inverse_ray u (c a) (hnone a)
  have hd : HasDerivAt (fun s : ℝ => blPsi m c (s • u))
      (∑ a, m a / 2 * deriv (fun s : ℝ => 1 / r3 (s • u) (c a)) R) R := by
    unfold blPsi
    apply HasDerivAt.const_add
    apply HasDerivAt.fun_sum
    intro a _
    rw [(hs a).deriv]
    simpa only [mul_one_div, div_mul_eq_div_div] using (hs a).const_mul (m a / 2)
  rw [hd.deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem bl_binding_difference {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) :
    blADMMass m - ∑ a, blBareMass m c a =
      -(1 / 2 : ℝ) * ∑ a, ∑ b ∈ Finset.univ.erase a, (m a * m b) / r3 (c a) (c b) := by
  simp only [blADMMass, blBareMass, mul_add, mul_one, Finset.sum_add_distrib, sub_add_cancel_left]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem brill_lindquist_harmonic_positive_mass_and_binding_energy {N : ℕ}
    (m : Fin N → ℝ) (c : Fin N → Point) :
    (∀ x, (∀ a, x ≠ c a) → laplacian (blPsi m c) x = 0) ∧
    (0 < N → (∀ a, 0 < m a) → 0 < blADMMass m) ∧
    (∀ u, r3 u 0 = 1 →
      Tendsto (fun R : ℝ => -2 * R ^ 2 * (blPsi m c (R • u)) ^ 3 *
        deriv (fun s : ℝ => blPsi m c (s • u)) R) atTop (𝓝 (blADMMass m))) ∧
    blADMMass m - ∑ a, blBareMass m c a =
      -(1 / 2 : ℝ) * ∑ a, ∑ b ∈ Finset.univ.erase a, (m a * m b) / r3 (c a) (c b) ∧
    (2 ≤ N → (∀ a, 0 < m a) → Function.Injective c →
      blADMMass m < ∑ a, blBareMass m c a) := by
  have hMP := majumdar_papapetrou_harmonic (fun a => m a / 2) c
  refine ⟨by simpa only [blPsi_eq_mpPotential] using hMP.1, ?_, ?_,
    bl_binding_difference m c, ?_⟩
  · intro hN hm
    unfold blADMMass
    exact Finset.sum_pos (fun a _ => hm a) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  · intro u hu
    have hp : Tendsto (fun R : ℝ => blPsi m c (R • u)) atTop (𝓝 1) := by
      simpa only [blPsi_eq_mpPotential] using hMP.2.2 u hu
    have h := (hp.pow 3).mul (bl_scaled_deriv_limit m c hu)
    simp only [one_pow, one_mul] at h
    apply h.congr
    intro R
    ring
  · intro hN hm hc
    have hterm (a b : Fin N) (hab : b ∈ Finset.univ.erase a) :
        0 < m a * m b / r3 (c a) (c b) :=
      div_pos (mul_pos (hm a) (hm b)) (radius_pos (fun he =>
        (Finset.ne_of_mem_erase hab) (hc he).symm))
    have hsum : 0 < ∑ a : Fin N, ∑ b ∈ Finset.univ.erase a, m a * m b / r3 (c a) (c b) := by
      let a : Fin N := ⟨0, by omega⟩
      let b : Fin N := ⟨1, by omega⟩
      have hab : b ≠ a := by
        intro he
        have he' := congrArg Fin.val he
        change (1 : ℕ) = 0 at he'
        omega
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j hj => (hterm i j hj).le) ?_
      exact ⟨a, Finset.mem_univ _,
        Finset.sum_pos (hterm a) ⟨b, Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩⟩⟩
    linarith [bl_binding_difference m c]

theorem riemannian_penrose_inequality_schwarzschild_saturation {M : ℝ} (hM : 0 < M) :
    let A := 4 * Real.pi * (isotropicArealRadius M (M / 2)) ^ 2
    A = 16 * Real.pi * M ^ 2 ∧ Real.sqrt (A / (16 * Real.pi)) = M ∧
    (∀ U V : ℝ, (V + U) / 2 = 0 →
      U * V = PenroseCarterCausalCompactification4D.kruskalF M
        (isotropicArealRadius M (M / 2)) → (V - U) / 2 = 0) := by
  dsimp
  have hr : 0 < M / 2 := by positivity
  have hthroat := (isotropic_schwarzschild_throat_and_inversion_isometry hM hr).2.2.2.2.2.2.mpr rfl
  rw [hthroat]
  refine ⟨by ring, ?_, ?_⟩
  · rw [show 4 * Real.pi * (2 * M) ^ 2 / (16 * Real.pi) = M ^ 2 by
      field_simp [Real.pi_ne_zero]; ring, Real.sqrt_sq hM.le]
  · intro U V hT he
    exact (PenroseCarterCausalCompactification4D.einstein_rosen_bridge_minimal_throat hM hT he).2.mp rfl

end Radial

end D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
