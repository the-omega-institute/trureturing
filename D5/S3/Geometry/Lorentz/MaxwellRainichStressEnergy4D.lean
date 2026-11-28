/- GID: D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Covariant electromagnetic invariants, the Maxwell stress tensor, and the Rainich identity with causal flux. -/

import D5.S3.Geometry.Lorentz.SL2CLorentzCover4D
import Mathlib.Tactic.LinearCombination

/-! The time-positive metric and the orientation with dual coordinates
`(−B, E)` fix all signs in the field contractions and energy flux. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D

abbrev V3 := Fin 3 → ℝ
abbrev V4 := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev eta4 : M4 := SL2CLorentzCover4D.eta
abbrev minkowskiNormSq := SL2CLorentzCover4D.minkowskiNormSq

def fieldTensor (E B : V3) : M4 :=
  !![0, E 0, E 1, E 2;
     -E 0, 0, -B 2, B 1;
     -E 1, B 2, 0, -B 0;
     -E 2, -B 1, B 0, 0]

def dualFieldTensor (E B : V3) : M4 := fieldTensor (-B) E

def fieldOfTensor (F : M4) : V3 × V3 :=
  (![F 0 1, F 0 2, F 0 3], ![-F 2 3, F 1 3, -F 1 2])

def spatialNormSq (x : V3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

def spatialDot (x y : V3) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def spatialCross (x y : V3) : V3 :=
  ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

def energyDensity (E B : V3) : ℝ := (spatialNormSq E + spatialNormSq B) / 2

theorem fieldTensor_antisym (E B : V3) : (fieldTensor E B)ᵀ = -fieldTensor E B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldTensor]

theorem dualFieldTensor_sq (E B : V3) :
    dualFieldTensor (-B) E = -fieldTensor E B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dualFieldTensor, fieldTensor]

private theorem fieldOfTensor_leftInverse (E B : V3) :
    fieldOfTensor (fieldTensor E B) = (E, B) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [fieldOfTensor, fieldTensor]

private theorem fieldOfTensor_rightInverse (F : M4) (h : Fᵀ = -F) :
    fieldTensor (fieldOfTensor F).1 (fieldOfTensor F).2 = F := by
  have skew (i j : Fin 4) : F j i = -F i j := congrFun (congrFun h i) j
  have diag (i : Fin 4) : F i i = 0 := by linarith [skew i i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldOfTensor, fieldTensor, diag] <;>
    exact (skew _ _).symm

theorem fieldTensor_bijective :
    Function.Bijective (fun EB : V3 × V3 =>
      (⟨fieldTensor EB.1 EB.2, fieldTensor_antisym EB.1 EB.2⟩ :
        {F : M4 // Fᵀ = -F})) := by
  constructor
  · intro a b h
    have he := congrArg fieldOfTensor (congrArg Subtype.val h)
    simpa only [fieldOfTensor_leftInverse] using he
  · intro F
    exact ⟨fieldOfTensor F.1, Subtype.ext (fieldOfTensor_rightInverse F.1 F.2)⟩

def fieldTensorUp (E B : V3) : M4 := eta4 * fieldTensor E B * eta4

def maxwellInv1 (F : M4) : ℝ := (1 / 2 : ℝ) * (Fᵀ * (eta4 * F * eta4)).trace

def maxwellInv2 (E B : V3) : ℝ :=
  (1 / 4 : ℝ) * ((fieldTensor E B)ᵀ * (eta4 * dualFieldTensor E B * eta4)).trace

private theorem eta4_transpose : eta4ᵀ = eta4 := diagonal_transpose _

private theorem eta4_sq : eta4 * eta4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SL2CLorentzCover4D.eta, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
      Matrix.one_apply]

theorem maxwell_invariants_explicit (E B : V3) :
    maxwellInv1 (fieldTensor E B) = spatialNormSq B - spatialNormSq E ∧
    maxwellInv2 E B = spatialDot E B := by
  constructor <;>
    simp [maxwellInv1, maxwellInv2, dualFieldTensor, fieldTensor, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_four, SL2CLorentzCover4D.eta, Matrix.diagonal_apply,
      spatialNormSq, spatialDot] <;> ring

private theorem det4_expand (A : M4) :
    A.det = A 0 0 * (!![A 1 1, A 1 2, A 1 3;
                         A 2 1, A 2 2, A 2 3; A 3 1, A 3 2, A 3 3]).det -
            A 0 1 * (!![A 1 0, A 1 2, A 1 3;
                         A 2 0, A 2 2, A 2 3; A 3 0, A 3 2, A 3 3]).det +
            A 0 2 * (!![A 1 0, A 1 1, A 1 3;
                         A 2 0, A 2 1, A 2 3; A 3 0, A 3 1, A 3 3]).det -
            A 0 3 * (!![A 1 0, A 1 1, A 1 2;
                         A 2 0, A 2 1, A 2 2; A 3 0, A 3 1, A 3 2]).det := by
  have minors : ∀ j : Fin 4, A.submatrix Fin.succ j.succAbove =
      Matrix.of (fun i k : Fin 3 => A i.succ (j.succAbove k)) := fun _ => rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [minors]
  have entry (j : Fin 4) (M : Matrix (Fin 3) (Fin 3) ℝ)
      (h : ∀ i k : Fin 3, A i.succ (j.succAbove k) = M i k) :
      (Matrix.of fun i k : Fin 3 => A i.succ (j.succAbove k)).det = M.det :=
    congrArg Matrix.det (Matrix.ext h)
  rw [entry 0 (!![A 1 1, A 1 2, A 1 3; A 2 1, A 2 2, A 2 3; A 3 1, A 3 2, A 3 3])
        (by intro i k; fin_cases i <;> fin_cases k <;> rfl),
      entry 1 (!![A 1 0, A 1 2, A 1 3; A 2 0, A 2 2, A 2 3; A 3 0, A 3 2, A 3 3])
        (by intro i k; fin_cases i <;> fin_cases k <;> rfl),
      entry 2 (!![A 1 0, A 1 1, A 1 3; A 2 0, A 2 1, A 2 3; A 3 0, A 3 1, A 3 3])
        (by intro i k; fin_cases i <;> fin_cases k <;> rfl),
      entry 3 (!![A 1 0, A 1 1, A 1 2; A 2 0, A 2 1, A 2 2; A 3 0, A 3 1, A 3 2])
        (by intro i k; fin_cases i <;> fin_cases k <;> rfl)]
  norm_num
  ring

theorem fieldTensor_det (E B : V3) :
    (fieldTensor E B).det = (spatialDot E B) ^ 2 := by
  simp [det4_expand, Matrix.det_fin_three, fieldTensor, spatialDot]
  ring

private theorem lorentz_metric_reverse (Λ : M4) (hΛ : Λᵀ * eta4 * Λ = eta4) :
    Λ * eta4 * Λᵀ = eta4 := by
  have h : (eta4 * Λᵀ * eta4) * Λ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Λᵀ, hΛ, eta4_sq]
  have hr := mul_eq_one_comm.mp h
  calc
    Λ * eta4 * Λᵀ = (Λ * (eta4 * Λᵀ * eta4)) * eta4 := by
      simp [Matrix.mul_assoc, eta4_sq]
    _ = eta4 := by rw [hr, one_mul]

private def pfaffian4 (F : M4) : ℝ :=
  F 0 1 * F 2 3 - F 0 2 * F 1 3 + F 0 3 * F 1 2

private theorem pfaffian4_field (E B : V3) : pfaffian4 (fieldTensor E B) = -spatialDot E B := by
  simp [pfaffian4, fieldTensor, spatialDot]
  ring

/-- The Pfaffian is the signed coefficient of the exterior square. -/
private theorem pfaffian4_pullback (Λ : M4) (E B : V3) :
    pfaffian4 (Λᵀ * fieldTensor E B * Λ) = Λ.det * pfaffian4 (fieldTensor E B) := by
  simp [det4_expand, pfaffian4, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.det_fin_three, fieldTensor]
  ring

theorem maxwell_invariants_lorentz_invariant (Λ : M4) (E B : V3)
    (hΛ : Λᵀ * eta4 * Λ = eta4) (hor : Λ.det = 1) :
    let F' := Λᵀ * fieldTensor E B * Λ
    let EB' := fieldOfTensor F'
    maxwellInv1 F' = maxwellInv1 (fieldTensor E B) ∧
    spatialNormSq EB'.2 - spatialNormSq EB'.1 = spatialNormSq B - spatialNormSq E ∧
    maxwellInv2 EB'.1 EB'.2 = maxwellInv2 E B ∧
    spatialDot EB'.1 EB'.2 = spatialDot E B := by
  dsimp only
  let F := fieldTensor E B
  let F' := Λᵀ * F * Λ
  let EB' := fieldOfTensor F'
  have hskew : F'ᵀ = -F' := by
    simp [F', F, Matrix.transpose_mul, fieldTensor_antisym, Matrix.mul_assoc]
  have hrep : fieldTensor EB'.1 EB'.2 = F' := fieldOfTensor_rightInverse F' hskew
  have hback := lorentz_metric_reverse Λ hΛ
  have hcontract : maxwellInv1 F' = maxwellInv1 F := by
    unfold maxwellInv1
    congr 1
    calc
      (F'ᵀ * (eta4 * F' * eta4)).trace =
          (Λᵀ * (Fᵀ * (Λ * eta4 * Λᵀ) * F) * (Λ * eta4)).trace := by
        simp [F', Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((Fᵀ * eta4 * F) * (Λ * eta4 * Λᵀ)).trace := by
        rw [hback, Matrix.mul_assoc Λᵀ, Matrix.trace_mul_comm]
        simpa only [Matrix.mul_assoc] using congrArg
          (fun M : M4 => ((Fᵀ * eta4 * F) * M).trace) hback
      _ = (Fᵀ * (eta4 * F * eta4)).trace := by rw [hback]; simp [Matrix.mul_assoc]
  have hp : spatialDot EB'.1 EB'.2 = spatialDot E B := by
    have h := pfaffian4_pullback Λ E B
    change pfaffian4 F' = _ at h
    rw [← hrep, hor, one_mul, pfaffian4_field, pfaffian4_field] at h
    exact neg_injective h
  refine ⟨hcontract, ?_, ?_, hp⟩
  · change spatialNormSq EB'.2 - spatialNormSq EB'.1 = _
    rw [← (maxwell_invariants_explicit EB'.1 EB'.2).1, hrep, hcontract]
    exact (maxwell_invariants_explicit E B).1
  · change maxwellInv2 EB'.1 EB'.2 = _
    rw [(maxwell_invariants_explicit EB'.1 EB'.2).2, (maxwell_invariants_explicit E B).2]
    exact hp

private def stressFrom (F : M4) : M4 :=
  let Q := eta4 * F * eta4 * F
  Q - ((1 / 4 : ℝ) * Q.trace) • (1 : M4)

def maxwellStressMixed (E B : V3) : M4 := stressFrom (fieldTensor E B)

def maxwellStressCov (E B : V3) : M4 := eta4 * maxwellStressMixed E B

def maxwellStressContra (E B : V3) : M4 := maxwellStressMixed E B * eta4

private theorem stress_cov_formula (F : M4) :
    eta4 * stressFrom F =
      F * eta4 * F - ((1 / 4 : ℝ) * (eta4 * F * eta4 * F).trace) • eta4 := by
  simp [stressFrom, Matrix.mul_sub, ← Matrix.mul_assoc, eta4_sq]

theorem maxwell_stress_symmetric (E B : V3) :
    (maxwellStressCov E B)ᵀ = maxwellStressCov E B := by
  unfold maxwellStressCov maxwellStressMixed
  rw [stress_cov_formula]
  simp [Matrix.transpose_sub, Matrix.transpose_mul, fieldTensor_antisym,
    eta4_transpose, Matrix.mul_assoc]

theorem maxwell_stress_traceless (E B : V3) : (maxwellStressMixed E B).trace = 0 := by
  simp [maxwellStressMixed, stressFrom, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  ring

private def stressComponents (E B : V3) : M4 :=
  Matrix.of fun i j =>
    Fin.cases
      (Fin.cases (energyDensity E B) (fun k => -spatialCross E B k) j)
      (fun l => Fin.cases (spatialCross E B l)
        (fun k => E l * E k + B l * B k -
          if l = k then energyDensity E B else 0) j) i

private theorem fin4_cases_one {α : Type*} (a : α) (f : Fin 3 → α) :
    Fin.cases a f (1 : Fin 4) = f 0 := rfl

private theorem fin4_cases_two {α : Type*} (a : α) (f : Fin 3 → α) :
    Fin.cases a f (2 : Fin 4) = f 1 := rfl

private theorem fin4_cases_three {α : Type*} (a : α) (f : Fin 3 → α) :
    Fin.cases a f (3 : Fin 4) = f 2 := rfl

attribute [local simp] fin4_cases_one fin4_cases_two fin4_cases_three

private theorem stress_components (E B : V3) : maxwellStressMixed E B = stressComponents E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [maxwellStressMixed, stressFrom, stressComponents, fieldTensor, Matrix.mul_apply,
      Matrix.trace, Matrix.diag, Fin.sum_univ_four, SL2CLorentzCover4D.eta, Matrix.diagonal_apply,
      Matrix.one_apply, energyDensity, spatialNormSq, spatialCross] <;> ring

theorem maxwell_energy_and_poynting (E B : V3) :
    maxwellStressMixed E B 0 0 = energyDensity E B ∧
    (∀ i : Fin 3, maxwellStressMixed E B 0 i.succ = -spatialCross E B i) ∧
    (∀ i : Fin 3, maxwellStressContra E B 0 i.succ = spatialCross E B i) ∧
    ∀ i j : Fin 3, maxwellStressContra E B i.succ j.succ =
      -E i * E j - B i * B j + if i = j then energyDensity E B else 0 := by
  rw [stress_components]
  refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [maxwellStressContra, stress_components, stressComponents, Matrix.mul_diagonal,
        SL2CLorentzCover4D.eta]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [maxwellStressContra, stress_components, stressComponents, Matrix.mul_diagonal,
        SL2CLorentzCover4D.eta] <;> ring

theorem maxwell_stress_lorentz_covariant (Λ : M4) (E B : V3)
    (hΛ : Λᵀ * eta4 * Λ = eta4) :
    let EB' := fieldOfTensor (Λᵀ * fieldTensor E B * Λ)
    maxwellStressCov EB'.1 EB'.2 = Λᵀ * maxwellStressCov E B * Λ := by
  dsimp only
  let F := fieldTensor E B
  let F' := Λᵀ * F * Λ
  let EB' := fieldOfTensor F'
  have hskew : F'ᵀ = -F' := by
    simp [F', F, Matrix.transpose_mul, fieldTensor_antisym, Matrix.mul_assoc]
  have hrep : fieldTensor EB'.1 EB'.2 = F' := fieldOfTensor_rightInverse F' hskew
  have hback := lorentz_metric_reverse Λ hΛ
  have hquad : F' * eta4 * F' = Λᵀ * (F * eta4 * F) * Λ := by
    calc
      F' * eta4 * F' = Λᵀ * (F * (Λ * eta4 * Λᵀ) * F) * Λ := by
        simp [F', Matrix.mul_assoc]
      _ = _ := by rw [hback]
  have htrace : (eta4 * F' * eta4 * F').trace = (eta4 * F * eta4 * F).trace := by
    simp only [Matrix.mul_assoc eta4]
    rw [hquad]
    calc
      (eta4 * (Λᵀ * (F * eta4 * F) * Λ)).trace =
          ((Λ * eta4 * Λᵀ) * (F * eta4 * F)).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hback]
  change eta4 * stressFrom (fieldTensor EB'.1 EB'.2) =
    Λᵀ * (eta4 * stressFrom F) * Λ
  rw [hrep, stress_cov_formula, stress_cov_formula, hquad, htrace]
  simp [Matrix.mul_sub, Matrix.sub_mul, hΛ]

theorem maxwell_duality_rotation_invariant (E B : V3) (θ : ℝ) :
    let E' : V3 := Real.cos θ • E + Real.sin θ • B
    let B' : V3 := -Real.sin θ • E + Real.cos θ • B
    maxwellStressMixed E' B' = maxwellStressMixed E B ∧
    maxwellStressCov E' B' = maxwellStressCov E B := by
  dsimp only
  have hnorm (i j : Fin 3) :
      (Real.cos θ * E i + Real.sin θ * B i) * (Real.cos θ * E j + Real.sin θ * B j) +
      (-Real.sin θ * E i + Real.cos θ * B i) * (-Real.sin θ * E j + Real.cos θ * B j) =
      E i * E j + B i * B j := by
    linear_combination (E i * E j + B i * B j) * Real.sin_sq_add_cos_sq θ
  have hcross (i j : Fin 3) :
      (Real.cos θ * E i + Real.sin θ * B i) * (-Real.sin θ * E j + Real.cos θ * B j) -
      (Real.cos θ * E j + Real.sin θ * B j) * (-Real.sin θ * E i + Real.cos θ * B i) =
      E i * B j - E j * B i := by
    linear_combination (E i * B j - E j * B i) * Real.sin_sq_add_cos_sq θ
  let E' : V3 := Real.cos θ • E + Real.sin θ • B
  let B' : V3 := -Real.sin θ • E + Real.cos θ • B
  have henergy : energyDensity E' B' = energyDensity E B := by
    change ((E' 0 ^ 2 + E' 1 ^ 2 + E' 2 ^ 2) +
      (B' 0 ^ 2 + B' 1 ^ 2 + B' 2 ^ 2)) / 2 = _
    unfold energyDensity spatialNormSq
    have h (i : Fin 3) : E' i ^ 2 + B' i ^ 2 = E i ^ 2 + B i ^ 2 := by
      simpa only [E', B', Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two] using hnorm i i
    linear_combination (h 0 + h 1 + h 2) / 2
  have hp : spatialCross E' B' = spatialCross E B := by
    funext i
    fin_cases i
    · exact hcross 1 2
    · exact hcross 2 0
    · exact hcross 0 1
  have hmixed : maxwellStressMixed E' B' = maxwellStressMixed E B := by
    rw [stress_components, stress_components]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [stressComponents, henergy, hp]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [stressComponents, hp]
      · change E' i * E' j + B' i * B' j - (if i = j then energyDensity E' B' else 0) =
          E i * E j + B i * B j - (if i = j then energyDensity E B else 0)
        rw [henergy]
        exact congrArg (fun s : ℝ => s - (if i = j then energyDensity E B else 0)) (hnorm i j)
  exact ⟨hmixed, congrArg (fun T : M4 => eta4 * T) hmixed⟩

private theorem spatialNormSq_nonneg (x : V3) : 0 ≤ spatialNormSq x := by
  unfold spatialNormSq
  positivity

private theorem spatial_lagrange (x y : V3) :
    spatialNormSq (spatialCross x y) =
      spatialNormSq x * spatialNormSq y - spatialDot x y ^ 2 := by
  simp [spatialNormSq, spatialCross, spatialDot]
  ring

private def rainichScalar (E B : V3) : ℝ :=
  ((spatialNormSq B - spatialNormSq E) ^ 2 + 4 * spatialDot E B ^ 2) / 4

private theorem rainichScalar_nonneg (E B : V3) : 0 ≤ rainichScalar E B := by
  unfold rainichScalar
  positivity

private theorem rainichScalar_eq_zero (E B : V3) :
    rainichScalar E B = 0 ↔ spatialNormSq E = spatialNormSq B ∧ spatialDot E B = 0 := by
  unfold rainichScalar
  constructor
  · intro h
    have hdiff : spatialNormSq B - spatialNormSq E = 0 := by nlinarith
    have hdot : spatialDot E B = 0 := by nlinarith
    exact ⟨(sub_eq_zero.mp hdiff).symm, hdot⟩
  · rintro ⟨h, hdot⟩
    simp [h, hdot]

private theorem poynting_gap (E B : V3) :
    energyDensity E B ^ 2 - spatialNormSq (spatialCross E B) = rainichScalar E B := by
  rw [spatial_lagrange]
  unfold energyDensity rainichScalar
  ring

theorem poynting_le_energy_density (E B : V3) :
    Real.sqrt (spatialNormSq (spatialCross E B)) ≤ energyDensity E B ∧
    (Real.sqrt (spatialNormSq (spatialCross E B)) = energyDensity E B ↔
      spatialNormSq E = spatialNormSq B ∧ spatialDot E B = 0) := by
  have hu : 0 ≤ energyDensity E B :=
    div_nonneg (add_nonneg (spatialNormSq_nonneg E) (spatialNormSq_nonneg B)) (by norm_num)
  have hsq := Real.sq_sqrt (spatialNormSq_nonneg (spatialCross E B))
  have hgap := poynting_gap E B
  have hnonneg := rainichScalar_nonneg E B
  constructor
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) hu).mp
    linarith
  · rw [← rainichScalar_eq_zero, ← hgap, sub_eq_zero]
    exact (sq_eq_sq₀ (Real.sqrt_nonneg _) hu).symm.trans
      (by constructor <;> intro h <;> linarith)

theorem maxwell_rainich_square_identity (E B : V3) :
    maxwellStressMixed E B * maxwellStressMixed E B =
      ((1 / 4 : ℝ) * ((spatialNormSq B - spatialNormSq E) ^ 2 +
        4 * spatialDot E B ^ 2)) • (1 : M4) := by
  rw [stress_components]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stressComponents, energyDensity, spatialNormSq, spatialCross, spatialDot,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem maxwell_stress_nilpotent_iff_null (E B : V3) :
    maxwellStressMixed E B * maxwellStressMixed E B = 0 ↔
      spatialNormSq E = spatialNormSq B ∧ spatialDot E B = 0 := by
  rw [maxwell_rainich_square_identity, ← rainichScalar_eq_zero]
  have hcoeff : (1 / 4 : ℝ) * ((spatialNormSq B - spatialNormSq E) ^ 2 +
      4 * spatialDot E B ^ 2) = rainichScalar E B := by unfold rainichScalar; ring
  rw [hcoeff]
  constructor
  · intro h
    simpa using congrArg (fun M : M4 => M 0 0) h
  · intro h
    rw [h, zero_smul]

private def spatialPart (u : V4) : V3 := fun i => u i.succ

private theorem metric_norm (u : V4) : u ⬝ᵥ (eta4 *ᵥ u) = minkowskiNormSq u := by
  simp [SL2CLorentzCover4D.eta, SL2CLorentzCover4D.minkowskiNormSq, Matrix.mulVec_diagonal,
    dotProduct, Fin.sum_univ_four]
  ring

private theorem cone_spatial_bound (u : V4) (ht : 0 ≤ u 0) (hu : 0 ≤ minkowskiNormSq u) :
    Real.sqrt (spatialNormSq (spatialPart u)) ≤ u 0 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) ht).mp
  rw [Real.sq_sqrt (spatialNormSq_nonneg _)]
  exact sub_nonneg.mp hu

private theorem spatial_dot_le (x y : V3) :
    spatialDot x y ≤ Real.sqrt (spatialNormSq x) * Real.sqrt (spatialNormSq y) := by
  have hprod : 0 ≤ Real.sqrt (spatialNormSq x) * Real.sqrt (spatialNormSq y) := by positivity
  calc
    spatialDot x y ≤ |spatialDot x y| := le_abs_self _
    _ ≤ Real.sqrt (spatialNormSq x) * Real.sqrt (spatialNormSq y) := by
      apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
      rw [sq_abs, mul_pow, Real.sq_sqrt (spatialNormSq_nonneg x),
        Real.sq_sqrt (spatialNormSq_nonneg y)]
      linarith [spatial_lagrange x y, spatialNormSq_nonneg (spatialCross x y)]

private theorem flux_time (E B : V3) (u : V4) :
    (maxwellStressMixed E B *ᵥ u) 0 =
      energyDensity E B * u 0 - spatialDot (spatialCross E B) (spatialPart u) := by
  rw [stress_components]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, stressComponents, spatialDot,
    spatialPart]
  ring

theorem maxwell_dominant_energy_condition (E B : V3) (u : V4)
    (ht : 0 ≤ u 0) (hu : 0 ≤ minkowskiNormSq u) :
    let j := maxwellStressMixed E B *ᵥ u
    0 ≤ u ⬝ᵥ (maxwellStressCov E B *ᵥ u) ∧ 0 ≤ j 0 ∧ 0 ≤ minkowskiNormSq j ∧
    minkowskiNormSq j =
      ((maxwellInv1 (fieldTensor E B) ^ 2 + 4 * maxwellInv2 E B ^ 2) / 4) *
        minkowskiNormSq u := by
  dsimp only
  let T := maxwellStressMixed E B
  let j := T *ᵥ u
  have hself : Tᵀ * eta4 = eta4 * T := by
    simpa [maxwellStressCov, Matrix.transpose_mul, eta4_transpose, T] using
      maxwell_stress_symmetric E B
  have hnorm : minkowskiNormSq j = rainichScalar E B * minkowskiNormSq u := by
    have hT : T * T = rainichScalar E B • (1 : M4) := by
      simpa [rainichScalar, div_eq_mul_inv, mul_comm] using maxwell_rainich_square_identity E B
    calc
      minkowskiNormSq j = u ⬝ᵥ ((Tᵀ * eta4 * T) *ᵥ u) := by
        rw [← metric_norm]
        calc
          j ⬝ᵥ (eta4 *ᵥ j) = u ⬝ᵥ (Tᵀ *ᵥ (eta4 *ᵥ j)) :=
            (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec T u (eta4 *ᵥ j)).symm
          _ = _ := by simp only [j, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      _ = rainichScalar E B * minkowskiNormSq u := by
        rw [hself, Matrix.mul_assoc, hT, Matrix.mul_smul, mul_one, Matrix.smul_mulVec,
          dotProduct_smul, metric_norm]
        rfl
  have hj : 0 ≤ minkowskiNormSq j := hnorm ▸ mul_nonneg (rainichScalar_nonneg E B) hu
  have hj0 : 0 ≤ j 0 := by
    change 0 ≤ (maxwellStressMixed E B *ᵥ u) 0
    rw [flux_time]
    apply sub_nonneg.mpr
    calc
      _ ≤ Real.sqrt (spatialNormSq (spatialCross E B)) *
          Real.sqrt (spatialNormSq (spatialPart u)) := spatial_dot_le _ _
      _ ≤ energyDensity E B * u 0 :=
        mul_le_mul (poynting_le_energy_density E B).1 (cone_spatial_bound u ht hu)
          (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (poynting_le_energy_density E B).1)
  have hpair : u ⬝ᵥ (maxwellStressCov E B *ᵥ u) =
      u 0 * j 0 - spatialDot (spatialPart u) (spatialPart j) := by
    rw [maxwellStressCov, ← Matrix.mulVec_mulVec]
    change u ⬝ᵥ (eta4 *ᵥ j) = _
    simp [SL2CLorentzCover4D.eta, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four,
      spatialDot, spatialPart]
    ring
  refine ⟨?_, hj0, hj, ?_⟩
  · rw [hpair]
    apply sub_nonneg.mpr
    exact (spatial_dot_le _ _).trans (mul_le_mul (cone_spatial_bound u ht hu)
      (cone_spatial_bound j hj0 hj) (Real.sqrt_nonneg _) ht)
  · simpa only [(maxwell_invariants_explicit E B).1, (maxwell_invariants_explicit E B).2,
      rainichScalar] using hnorm

end D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D
