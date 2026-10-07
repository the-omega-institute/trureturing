/- GID: D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation
   generality: I
   mirror-B: D5/B/S3/Estimation/GaussianThermometryJointMeasurementRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.claim; result=D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.result; claim=D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.claim
   digest: A two-mode unequal-frequency Gaussian measurement beats the local thermometry bound. -/

/-
proof_shape: result: content; single_mode_local_bound: content
escape_witness: v2, single_mode_local_bound: Loewner monotonicity, physical-to-pure
domination and rotation-independent rational bounds at ν = 2 and ν = 5/4,
used by the additive local supremum bound on the live path of result.
admission_basis: open-problem-resolution (#11666; Refuted)
Registration is paused under CLAUDE.md §3.9 (information-escape registration pause).
Direct frozen dependencies: D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.coth;
D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef.
-/

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.SymplecticGroup
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

namespace D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

/-- The temperature derivative ν' = (ω / 2T²)(ν² − 1). -/
def thermalNuDeriv (ω T : ℝ) : ℝ := (ω / (2 * T ^ 2)) * (coth (ω / (2 * T)) ^ 2 - 1)

/-- The block-diagonal covariance σ = ⊕ νₖ I₂. -/
def thermalCov {m : ℕ} (ω : Fin m → ℝ) (T : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun i j => if i = j then coth (ω ((Fin.cast (Nat.mul_comm 2 m) i).divNat) / (2 * T)) else 0

/-- The derivative ∂Tσ = ⊕ νₖ' I₂. -/
def thermalCovDeriv {m : ℕ} (ω : Fin m → ℝ) (T : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun i j => if i = j then thermalNuDeriv (ω ((Fin.cast (Nat.mul_comm 2 m) i).divNat)) T else 0

/-- A Gaussian measurement covariance obeys σᴹ + iΩ ⪰ 0. -/
def IsGaussianMeasurementCov {m : ℕ}
    (σM : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Prop :=
  σM.IsSymm ∧ ((σM.map Complex.ofReal) + Complex.I • ((-Matrix.J (Fin m) ℂ).submatrix
    (fun i : Fin (2 * m) => if i.val % 2 = 0 then
      Sum.inl ((Fin.cast (Nat.mul_comm 2 m) i).divNat)
    else Sum.inr ((Fin.cast (Nat.mul_comm 2 m) i).divNat))
    (fun i : Fin (2 * m) => if i.val % 2 = 0 then
      Sum.inl ((Fin.cast (Nat.mul_comm 2 m) i).divNat)
    else Sum.inr ((Fin.cast (Nat.mul_comm 2 m) i).divNat)))).PosSemidef

/-- The covariance Fisher information, Eq. (36) with zero displacement. -/
def fisherC {n : ℕ}
    (σ d σM : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2) * Matrix.trace (((σ + σM)⁻¹ * d) ^ 2)

/-- The direct sum of arbitrary single-mode measurement covariances. -/
def localCov {m : ℕ} (M : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun i j => if (Fin.cast (Nat.mul_comm 2 m) i).divNat =
      (Fin.cast (Nat.mul_comm 2 m) j).divNat then
    M ((Fin.cast (Nat.mul_comm 2 m) i).divNat)
      ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
  else 0

/-- The supremum over block-diagonal covariances with physical single-mode blocks. -/
def localFisher {m : ℕ} (ω : Fin m → ℝ) (T : ℝ) : ℝ :=
  sSup {f | ∃ M : Fin m → Matrix (Fin 2) (Fin 2) ℝ,
    (∀ k, IsGaussianMeasurementCov (m := 1) (M k)) ∧
      f = fisherC (thermalCov ω T) (thermalCovDeriv ω T) (localCov M)}

/-- Eq. (47), upper-bound direction: every joint value is bounded by the local optimum. -/
def claim : Prop :=
  ∀ m (ω : Fin m → ℝ) (T : ℝ), (∀ k, 0 < ω k) → 0 < T →
    ∀ σM : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ, IsGaussianMeasurementCov σM →
      fisherC (thermalCov ω T) (thermalCovDeriv ω T) σM ≤ localFisher ω T

/-- Escape witness v2: physical single-mode local bounds at the two witness values. -/
private theorem single_mode_local_bound (ν d : ℝ)
    (hν : ν = 2 ∨ ν = 5 / 4) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : IsGaussianMeasurementCov (m := 1) M) :
    (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M).PosDef ∧
    fisherC (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (d • 1) M ≤
      d ^ 2 * (if ν = 2 then 1 / 8 else 8 / 25) := by
  have inverse_antitone : ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosDef → B.PosDef → (B-A).PosSemidef → (A⁻¹-B⁻¹).PosSemidef := by
    intro A B hA hB hBA
    have hAid := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    have hBid := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)
    have hAi := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    have hfactor : B * (A⁻¹-B⁻¹) * B =
        (B-A) * A⁻¹ * (B-A) + (B-A) := by
      noncomm_ring [hAid, hBid, hAi]
    have hpsd := (hA.inv.posSemidef.mul_mul_conjTranspose_same (B-A)).add hBA
    rw [hBA.1.eq, ← hfactor] at hpsd
    apply hB.isUnit.posSemidef_star_left_conjugate_iff.mp
    simpa only [star_eq_conjTranspose, hB.1.eq] using hpsd
  have fisher_scalar : ∀ (v e : ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ),
      fisherC (v • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (e • 1) N =
        (e ^ 2 / 2) * trace ((v • 1 + N)⁻¹ ^ 2) := by
    intro v e N
    simp [fisherC, pow_two]
    ring
  have fisher_monotone : ∀ (v e : ℝ) (P N : Matrix (Fin 2) (Fin 2) ℝ),
      0 < v → P.PosSemidef → N.PosSemidef → (N-P).PosSemidef →
      fisherC (v • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (e • 1) N ≤
        fisherC (v • 1) (e • 1) P := by
    intro v e P N hv hP hN hNP
    have hV : (v • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef :=
      Matrix.PosDef.one.smul hv
    have hA := hV.add_posSemidef hP
    have hB := hV.add_posSemidef hN
    have hi := inverse_antitone _ _ hA hB (by simpa using hNP)
    have ht : 0 ≤ trace (((v • 1 + P)⁻¹ - (v • 1 + N)⁻¹) *
        ((v • 1 + P)⁻¹ + (v • 1 + N)⁻¹)) := by
      simpa only [RCLike.re_to_real] using
        RHLinalg.trace_mul_nonneg_of_posSemidef hi
          (hA.inv.posSemidef.add hB.inv.posSemidef)
    have hid : trace (((v • 1 + P)⁻¹ - (v • 1 + N)⁻¹) *
        ((v • 1 + P)⁻¹ + (v • 1 + N)⁻¹)) =
        trace ((v • 1 + P)⁻¹ ^ 2) - trace ((v • 1 + N)⁻¹ ^ 2) := by
      simp only [sub_mul, mul_add, trace_sub, trace_add, pow_two]
      rw [trace_mul_comm (v • 1 + N)⁻¹ (v • 1 + P)⁻¹]
      ring
    rw [hid] at ht
    rw [fisher_scalar, fisher_scalar]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have physical_data : ∀ N : Matrix (Fin 2) (Fin 2) ℝ,
      IsGaussianMeasurementCov (m := 1) N → N.PosSemidef ∧ 1 ≤ N.det := by
    intro N hN
    have hsym : N 1 0 = N 0 1 := congrArg (fun A => A 0 1) hN.1
    have hcomplex : (!![(N 0 0 : ℂ), (N 0 1 : ℂ) + Complex.I;
        (N 0 1 : ℂ) - Complex.I, (N 1 1 : ℂ)]).PosSemidef := by
      convert hN.2 using 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
          Matrix.one_apply, hsym, sub_eq_add_neg]
    have hdet : 1 ≤ N.det := by
      have h := (RCLike.nonneg_iff.mp hcomplex.det_nonneg).1
      norm_num [Matrix.det_fin_two] at h
      simp only [Matrix.det_fin_two, hsym]
      nlinarith
    have hpsd : N.PosSemidef := by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hN.1)
      intro x
      have h := hcomplex.re_dotProduct_nonneg (fun i => (x i : ℂ))
      simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hsym] using h
    exact ⟨hpsd, hdet⟩
  obtain ⟨hpsd, hdet⟩ := physical_data M hM
  have hdef : M.PosDef := hpsd.posDef_iff_det_ne_zero.mpr (by linarith)
  let s := Real.sqrt M.det
  have hs : 1 ≤ s := by
    dsimp [s]
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hdet)
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hs2 : s ^ 2 = M.det := Real.sq_sqrt (by linarith)
  let P : Matrix (Fin 2) (Fin 2) ℝ := s⁻¹ • M
  have hP : P.PosDef := hdef.smul (inv_pos.mpr hspos)
  have hPdet : P.det = 1 := by
    dsimp [P]
    rw [Matrix.det_smul]
    norm_num
    rw [← hs2]
    field_simp
  have hdom : (M-P).PosSemidef := by
    have hid : M-P = (1-s⁻¹) • M := by dsimp [P]; module
    rw [hid]
    exact hpsd.smul (by have := (inv_le_one₀ hspos).mpr hs; linarith)
  have hPphysical : IsGaussianMeasurementCov (m := 1) P := by
    refine ⟨by simpa using hP.1, ?_⟩
    have hx := hP.diag_pos (i := 0)
    have hsymP : P 1 0 = P 0 1 := congrArg (fun A => A 0 1) hP.1
    have hd : P 0 0 * P 1 1 - P 0 1 ^ 2 = 1 := by
      simpa [Matrix.det_fin_two, hsymP, pow_two] using hPdet
    let C : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(P 0 0 : ℂ), 0; (P 0 1 : ℂ) - Complex.I, 0]
    have hfactor : (P.map Complex.ofReal) + Complex.I •
        ((-Matrix.J (Fin 1) ℂ).submatrix
          (fun i : Fin (2*1) => if i.val % 2 = 0 then
            Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))
          (fun i : Fin (2*1) => if i.val % 2 = 0 then
            Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))) =
          (P 0 0)⁻¹ • (C * Cᴴ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        norm_num [C, Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
          Matrix.one_apply, hsymP, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.star_def, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      all_goals field_simp [hx.ne']
      all_goals nlinarith [hd]
    rw [hfactor]
    exact (Matrix.posSemidef_self_mul_conjTranspose C).smul (inv_nonneg.mpr hx.le)
  have hPpsd := (physical_data P hPphysical).1
  -- The spectral parameter r covers every orientation of the pure covariance.
  have hpure_trace : ∃ r : ℝ, 1 ≤ r ∧ P.trace = r + r⁻¹ := by
    let x := hP.1.eigenvalues 0
    let y := hP.1.eigenvalues 1
    have hx : 0 < x := hP.eigenvalues_pos 0
    have hy : 0 < y := hP.eigenvalues_pos 1
    have hxy : x*y = 1 := by
      have h := hP.1.det_eq_prod_eigenvalues
      rw [hPdet, Fin.prod_univ_two] at h
      exact h.symm
    have hsum : P.trace = x+y := by
      simpa [x, y, Fin.sum_univ_two] using hP.1.trace_eq_sum_eigenvalues
    rcases le_total x y with h | h
    · refine ⟨y, ?_, ?_⟩
      · have := mul_le_mul_of_nonneg_right h hy.le
        nlinarith
      · rw [hsum]
        field_simp [hy.ne']
        nlinarith [hxy]
    · refine ⟨x, ?_, ?_⟩
      · have := mul_le_mul_of_nonneg_right h hx.le
        nlinarith
      · rw [hsum]
        field_simp [hx.ne']
        nlinarith [hxy]
  have ht : 2 ≤ P.trace := by
    obtain ⟨r, hr, htr⟩ := hpure_trace
    rw [htr]
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hi : 2-r ≤ 1/r := (le_div_iff₀ hrpos).mpr (by nlinarith [sq_nonneg (r-1)])
    rw [one_div] at hi
    linarith
  have pure_formula : ∀ v : ℝ, 0 < v →
      trace ((v • (1 : Matrix (Fin 2) (Fin 2) ℝ) + P)⁻¹ ^ 2) =
        ((2*v + P.trace)^2 - 2*(v^2 + v*P.trace + 1)) /
          (v^2 + v*P.trace + 1)^2 := by
    intro v hv
    let D := v^2 + v*P.trace + 1
    have hD : 0 < D := by dsimp [D]; positivity
    have hsymP : P 1 0 = P 0 1 := congrArg (fun A => A 0 1) hP.1
    have hdetP : P 0 0 * P 1 1 - P 0 1 ^ 2 = 1 := by
      simpa [Matrix.det_fin_two, hsymP, pow_two] using hPdet
    have hinv : (v • (1 : Matrix (Fin 2) (Fin 2) ℝ) + P)⁻¹ =
        !![(v+P 1 1)/D, -P 0 1/D; -P 0 1/D, (v+P 0 0)/D] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hsymP]
      all_goals field_simp [hD.ne']
      all_goals dsimp [D]; simp only [trace, Fin.sum_univ_two, Matrix.diag_apply]
      all_goals nlinarith [hdetP]
    change trace ((v • 1 + P)⁻¹ ^ 2) = ((2*v+P.trace)^2-2*D)/D^2
    rw [hinv]
    simp [pow_two, trace, Fin.sum_univ_two]
    field_simp [hD.ne']
    dsimp [D]
    simp only [trace, Fin.sum_univ_two, Matrix.diag_apply]
    nlinarith [hdetP]
  have pure_bound : fisherC (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (d • 1) P ≤
      d ^ 2 * (if ν = 2 then 1 / 8 else 8 / 25) := by
    rw [fisher_scalar, pure_formula ν (by rcases hν with rfl | rfl <;> norm_num)]
    rcases hν with rfl | rfl
    · simp only [ite_true]
      have hD : 0 < (2 : ℝ)^2 + 2*P.trace + 1 := by positivity
      have hb : ((2*(2:ℝ)+P.trace)^2 - 2*((2:ℝ)^2+2*P.trace+1)) /
          ((2:ℝ)^2+2*P.trace+1)^2 ≤ 1/4 := by
        apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg d)]
    · norm_num
      have hD : 0 < (5/4 : ℝ)^2 + (5/4)*P.trace + 1 := by positivity
      have hb : ((2*(5/4:ℝ)+P.trace)^2 - 2*((5/4:ℝ)^2+(5/4)*P.trace+1)) /
          ((5/4:ℝ)^2+(5/4)*P.trace+1)^2 ≤ 16/25 := by
        apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg d)]
  constructor
  · exact (Matrix.PosDef.one.smul (show 0 < ν by rcases hν with rfl | rfl <;> norm_num)).add_posSemidef hpsd
  · exact (fisher_monotone ν d P M (by rcases hν with rfl | rfl <;> norm_num)
      hPpsd hpsd hdom).trans pure_bound

private def witnessM : Matrix (Fin 4) (Fin 4) ℝ :=
  !![313 / 25, 0, 312 / 25, 0;
     0, 313 / 25, 0, -312 / 25;
     312 / 25, 0, 313 / 25, 0;
     0, -312 / 25, 0, 313 / 25]

private def witnessSc : Matrix (Fin 4) (Fin 4) ℂ :=
  (!![13 / 5, 0, 12 / 5, 0;
      0, 13 / 5, 0, -12 / 5;
      12 / 5, 0, 13 / 5, 0;
      0, -12 / 5, 0, 13 / 5] : Matrix (Fin 4) (Fin 4) ℝ).map Complex.ofReal

private def witnessB : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0; -Complex.I, 0; 0, 1; 0, -Complex.I]

private def witnessCov : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 0, 0, 0;
     0, 2, 0, 0;
     0, 0, 5 / 4, 0;
     0, 0, 0, 5 / 4]

private def witnessDeriv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3, 0, 0, 0;
     0, 3, 0, 0;
     0, 0, 9 / 8, 0;
     0, 0, 0, 9 / 8]

private def witnessInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![153 / 491, 0, -416 / 1473, 0;
     0, 153 / 491, 0, 416 / 1473;
     -416 / 1473, 0, 484 / 1473, 0;
     0, 416 / 1473, 0, 484 / 1473]

/-- The conjectured equality fails for two unequal-frequency modes. -/
theorem result : ¬ claim := by
  have blocks_additive : ∀ (M₀ M₁ : Matrix (Fin 2) (Fin 2) ℝ) (v₀ v₁ d₀ d₁ : ℝ),
      (v₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M₀).PosDef →
      (v₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M₁).PosDef →
      fisherC (localCov ![v₀ • 1, v₁ • 1]) (localCov ![d₀ • 1, d₁ • 1])
        (localCov ![M₀, M₁]) =
      fisherC (v₀ • 1) (d₀ • 1) M₀ + fisherC (v₁ • 1) (d₁ • 1) M₁ := by
    intro M₀ M₁ v₀ v₁ d₀ d₁ hA hB
    let A := v₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M₀
    let B := v₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M₁
    have hsum : localCov ![v₀ • 1, v₁ • 1] + localCov ![M₀, M₁] = localCov ![A, B] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [localCov, Fin.divNat, A, B]
    have hAid := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
    have hBid := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)
    have hinv : (localCov ![A, B])⁻¹ = localCov ![A⁻¹, B⁻¹] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [localCov, Fin.divNat, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_four, Matrix.one_apply]
      all_goals first
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 0 0) hAid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 0 1) hAid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 1 0) hAid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 1 1) hAid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 0 0) hBid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 0 1) hBid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 1 0) hBid
        | simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrArg (fun N => N 1 1) hBid
    unfold fisherC
    rw [hsum, hinv]
    norm_num [localCov, Fin.divNat, pow_two, trace, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.sum_univ_four, Fin.sum_univ_two, Matrix.one_apply, A, B]
    ring

  let a : ℝ := Real.artanh (1 / 2 : ℝ)
  let ω : Fin 2 → ℝ := ![2 * a, 4 * a]
  have ha : 0 < a := by
    dsimp [a]
    exact Real.artanh_pos (by norm_num)
  have hω : ∀ k, 0 < ω k := by
    intro k
    fin_cases k <;> dsimp [ω] <;> positivity
  have witness_physical : IsGaussianMeasurementCov (m := 2) witnessM := by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [witnessM, Matrix.IsSymm]
    · have hfactor : (witnessM.map Complex.ofReal) + Complex.I • ((-Matrix.J (Fin 2) ℂ).submatrix
    (fun i : Fin (2 * 2) => if i.val % 2 = 0 then
      Sum.inl ((Fin.cast (Nat.mul_comm 2 2) i).divNat)
    else Sum.inr ((Fin.cast (Nat.mul_comm 2 2) i).divNat))
    (fun i : Fin (2 * 2) => if i.val % 2 = 0 then
      Sum.inl ((Fin.cast (Nat.mul_comm 2 2) i).divNat)
    else Sum.inr ((Fin.cast (Nat.mul_comm 2 2) i).divNat))) =
          (witnessSc * witnessB) * (witnessSc * witnessB)ᴴ := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          apply Complex.ext <;>
          norm_num [witnessM, witnessSc, witnessB, Matrix.J, Matrix.fromBlocks, Matrix.submatrix,
            Fin.divNat, Matrix.one_apply,
            map_div₀ (starRingEnd ℂ), Complex.conj_ofReal, Matrix.map_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Complex.star_def, Fin.sum_univ_two, Fin.sum_univ_four, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring
      rw [hfactor]
      exact Matrix.posSemidef_self_mul_conjTranspose _

  have witness_inverse :
      (witnessCov + witnessM)⁻¹ = witnessInv := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witnessCov, witnessM, witnessInv, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.one_apply, Matrix.cons_val_four, Matrix.vecHead,
        Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

  have coth_half_identity :
      Real.cosh (Real.artanh (1 / 2 : ℝ)) /
          Real.sinh (Real.artanh (1 / 2 : ℝ)) = 2 := by
    let a := Real.artanh (1 / 2 : ℝ)
    have hx : (1 / 2 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
    have ht := Real.tanh_artanh hx
    rw [Real.tanh_eq_sinh_div_cosh] at ht
    have hs : Real.sinh a ≠ 0 := by
      intro hs
      change Real.sinh a = 0 at hs
      change Real.sinh a / Real.cosh a = 1 / 2 at ht
      rw [hs, zero_div] at ht
      norm_num at ht
    have hc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos _)
    change Real.cosh a / Real.sinh a = 2
    have ht' : 2 * Real.sinh a = Real.cosh a := by
      dsimp [a]
      field_simp at ht
      linarith
    rw [← ht']
    field_simp [hs]

  have coth_double_half_identity :
      Real.cosh (2 * Real.artanh (1 / 2 : ℝ)) /
          Real.sinh (2 * Real.artanh (1 / 2 : ℝ)) = 5 / 4 := by
    let a := Real.artanh (1 / 2 : ℝ)
    have hx : (1 / 2 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
    have ht := Real.tanh_artanh hx
    rw [Real.tanh_eq_sinh_div_cosh] at ht
    have hs : Real.sinh a ≠ 0 := by
      intro hs
      change Real.sinh a = 0 at hs
      change Real.sinh a / Real.cosh a = 1 / 2 at ht
      rw [hs, zero_div] at ht
      norm_num at ht
    have hc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have ht' : 2 * Real.sinh a = Real.cosh a := by
      dsimp [a]
      field_simp at ht
      linarith
    change Real.cosh (2 * a) / Real.sinh (2 * a) = 5 / 4
    rw [Real.sinh_two_mul, Real.cosh_two_mul, ht']
    field_simp [hs]
    rw [← ht']
    ring_nf

  have hnu1 : coth ((ω 0) / (2 * 1)) = 2 := by
    change Real.cosh (2 * a / (2 * 1)) / Real.sinh (2 * a / (2 * 1)) = 2
    norm_num
    simpa [a] using coth_half_identity
  have hnu2 : coth ((ω 1) / (2 * 1)) = 5 / 4 := by
    change Real.cosh (4 * a / (2 * 1)) / Real.sinh (4 * a / (2 * 1)) = 5 / 4
    norm_num
    convert coth_double_half_identity using 1 <;> dsimp [a] <;> ring
  have hnu1' : coth ((2 * a) / (2 * 1)) = 2 := by simpa [ω] using hnu1
  have hnu2' : coth ((4 * a) / (2 * 1)) = 5 / 4 := by simpa [ω] using hnu2
  have hderiv1' : thermalNuDeriv (2 * a) 1 = 3 * a := by
    unfold thermalNuDeriv
    change (2 * a) / (2 * 1 ^ 2) * (coth ((2 * a) / (2 * 1)) ^ 2 - 1) = 3 * a
    rw [hnu1']
    norm_num
    ring
  have hderiv2' : thermalNuDeriv (4 * a) 1 = (9 / 8 : ℝ) * a := by
    unfold thermalNuDeriv
    change (4 * a) / (2 * 1 ^ 2) * (coth ((4 * a) / (2 * 1)) ^ 2 - 1) = (9 / 8 : ℝ) * a
    rw [hnu2']
    norm_num
    ring
  have hderiv1 : thermalNuDeriv (ω 0) 1 = 3 * a := by simpa [ω] using hderiv1'
  have hderiv2 : thermalNuDeriv (ω 1) 1 = (9 / 8 : ℝ) * a := by simpa [ω] using hderiv2'
  have hcov : thermalCov ω 1 = witnessCov := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thermalCov, Fin.divNat, witnessCov, ω]
    all_goals first | simpa using hnu1' | simpa using hnu2'
  have hdcov : thermalCovDeriv ω 1 = a • witnessDeriv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thermalCovDeriv, Fin.divNat, witnessDeriv, ω]
    all_goals first | simpa [mul_comm] using hderiv1' | simpa [mul_comm] using hderiv2'
  have identity_physical : IsGaussianMeasurementCov (m := 1)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine ⟨by simp [Matrix.IsSymm], ?_⟩
    let C : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; -Complex.I,0]
    have hf : (1 : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal + Complex.I •
        ((-Matrix.J (Fin 1) ℂ).submatrix
          (fun i : Fin (2*1) => if i.val % 2 = 0 then
            Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))
          (fun i : Fin (2*1) => if i.val % 2 = 0 then
            Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))) = C*Cᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        norm_num [C, Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
          Matrix.one_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.star_def, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [hf]
    exact Matrix.posSemidef_self_mul_conjTranspose C
  have hlocal : localFisher ω 1 ≤ (153/100 : ℝ) * a^2 := by
    unfold localFisher
    apply csSup_le
    · refine ⟨_, ![1,1], ?_, rfl⟩
      intro k
      fin_cases k <;> exact identity_physical
    · rintro f ⟨M, hM, rfl⟩
      have h₀ := single_mode_local_bound 2 (3*a) (Or.inl rfl) (M 0) (hM 0)
      have h₁ := single_mode_local_bound (5/4) ((9/8)*a) (Or.inr rfl) (M 1) (hM 1)
      have hcblocks : witnessCov = localCov ![(2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ),
          (5/4:ℝ) • 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [witnessCov, localCov, Fin.divNat, Matrix.one_apply]
      have hdblocks : a • witnessDeriv = localCov ![(3*a) • (1 : Matrix (Fin 2) (Fin 2) ℝ),
          ((9/8)*a) • 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [witnessDeriv, localCov, Fin.divNat, Matrix.one_apply] <;> ring
      have hMeq : M = ![M 0, M 1] := by ext k; fin_cases k <;> rfl
      rw [hcov, hdcov, hcblocks, hdblocks, hMeq]
      rw [blocks_additive _ _ _ _ _ _ h₀.1 h₁.1]
      have hb₀ := h₀.2
      have hb₁ := h₁.2
      norm_num at hb₀ hb₁
      nlinarith
  intro hc
  have hbound := (hc 2 ω 1 hω (by norm_num) witnessM witness_physical).trans hlocal
  rw [hcov, hdcov] at hbound
  unfold fisherC at hbound
  rw [witness_inverse] at hbound
  norm_num [witnessCov, witnessDeriv, witnessM, witnessInv,
    Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, Fin.sum_univ_four, Matrix.one_apply, pow_two,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at hbound
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  nlinarith

#print axioms result

end D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation
