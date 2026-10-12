/- GID: D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim; result=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result; claim=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim
   digest: Nonuniformity of the recycled-coin walk at a nonexceptional memory parameter. -/

import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.Real.GoldenRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators Topology Matrix
namespace D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity


def angle (φ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then Real.pi / 4 else Real.pi * (1 + φ) / 4

def coinFlip {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ∑ b : Fin 2, (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3
    (angle φ c.1) c.2 b : ℂ) * ψ n (c.1, b)

def shift {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ (n + (if c.2 = 0 then 1 else -1)) c

def swap {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ n (c.2, c.1)

def U {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  swap (shift (coinFlip φ ψ))

def initial {d : ℕ} (α : Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => if n = 0 then α c else 0

def p {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (t : ℕ) : ℝ :=
  ∑ c : Fin 2 × Fin 2, Complex.normSq
    (((U φ)^[t]) (initial (d := d) α) n c)

def avg {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, p φ α n (t + 1)) / (T : ℝ)

def exceptional (d : ℕ) : Set ℝ :=
  if 12 ∣ d then {0, 1, 2, 4, 5, 6} else {0, 2, 4, 6}

def unitCoin (α : Fin 2 × Fin 2 → ℂ) : Prop :=
  (∑ c : Fin 2 × Fin 2, Complex.normSq (α c)) = 1

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ φ : ℝ, φ ∈ Set.Ico 0 8 → φ ∉ exceptional d →
      ∀ α : Fin 2 × Fin 2 → ℂ, unitCoin α →
        ∀ n : ZMod d,
          Filter.Tendsto (avg φ α n) Filter.atTop
            (nhds (1 / (d : ℝ)))

private def a : ℝ := Real.sqrt 2 / 2
private def kappa : ℝ := (Real.sqrt 5 - 1) / 2
private def c : ℝ := a * kappa
private def theta : ℝ := Real.arccos c
private def s : ℝ := Real.sin theta
private def phiStar : ℝ :=
  4 * Real.arccos ((Real.sqrt 2 / 2) * ((Real.sqrt 5 - 1) / 2)) / Real.pi - 1

private theorem a_facts : 2 * a ^ 2 = 1 ∧ 0 < a ∧ a < 1 := by
  unfold a
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  constructor
  · nlinarith only [hsq]
  constructor <;> nlinarith only [hsq, hpos]

private theorem kappa_facts : 0 < kappa ∧ kappa < 1 ∧ kappa ^ 2 + kappa = 1 := by
  have hk : kappa = -Real.goldenConj := by unfold kappa Real.goldenConj; ring
  rw [hk]
  refine ⟨neg_pos.mpr Real.goldenConj_neg, ?_, ?_⟩
  · linarith only [Real.neg_one_lt_goldenConj]
  · nlinarith only [Real.goldenConj_sq]

private theorem c_bounds : 0 < c ∧ c < a := by
  unfold c
  exact ⟨mul_pos a_facts.2.1 kappa_facts.1,
    mul_lt_of_lt_one_right a_facts.2.1 kappa_facts.2.1⟩

private theorem theta_facts : Real.pi / 4 < theta ∧ theta < Real.pi / 2 ∧
    Real.cos theta = c := by
  have ha : Real.arccos a = Real.pi / 4 := by
    unfold a
    rw [← Real.cos_pi_div_four]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc1 : c ≤ 1 := le_trans c_bounds.2.le a_facts.2.2.le
  have hlo := Real.arccos_lt_arccos (by linarith [c_bounds.1]) c_bounds.2 a_facts.2.2.le
  have hhi := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 0) c_bounds.1 hc1
  rw [ha] at hlo
  rw [Real.arccos_zero] at hhi
  exact ⟨hlo, hhi, Real.cos_arccos (by linarith [c_bounds.1]) hc1⟩

private theorem phi_facts : 0 < phiStar ∧ phiStar < 1 ∧
    Real.pi * (1 + phiStar) / 4 = theta := by
  change 0 < 4 * theta / Real.pi - 1 ∧ 4 * theta / Real.pi - 1 < 1 ∧
    Real.pi * (1 + (4 * theta / Real.pi - 1)) / 4 = theta
  have hlo : 1 < 4 * theta / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by linarith [theta_facts.1])
  have hhi : 4 * theta / Real.pi < 2 :=
    (div_lt_iff₀ Real.pi_pos).mpr (by linarith [theta_facts.2.1])
  refine ⟨by linarith only [hlo], by linarith only [hhi], ?_⟩
  field_simp [ne_of_gt Real.pi_pos]
  ring

private theorem phi_nonexceptional : phiStar ∉ exceptional 12 := by
  unfold exceptional
  rw [if_pos (dvd_refl 12)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  intro h
  rcases h with h | h | h | h | h | h <;> linarith [phi_facts.1, phi_facts.2.1]

private theorem scalar_resonance : c ^ 2 + a * c = 1 / 2 := by
  calc
    c ^ 2 + a * c = a ^ 2 * (kappa ^ 2 + kappa) := by unfold c; ring
    _ = 1 / 2 := by rw [kappa_facts.2.2]; nlinarith only [a_facts.1]

private theorem sin_sq : s ^ 2 + c ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq theta
  rw [theta_facts.2.2] at h
  exact h

private theorem scalar_reductions : c * (a + c) = a ^ 2 ∧ kappa * s ^ 2 = a ^ 2 := by
  constructor
  · nlinarith only [scalar_resonance, a_facts.1]
  · have hkc : kappa * c ^ 2 = kappa - a ^ 2 := by
      unfold c
      linear_combination a ^ 2 * (kappa - 1) * kappa_facts.2.2 + kappa * a_facts.1
    linear_combination kappa * sin_sq - hkc

private def chi : AddChar (ZMod 12) ℂ := (ZMod.stdAddChar (N := 12)).mulShift 2
private def z : ℂ := chi 1

private theorem chi_norm (n : ZMod 12) : ‖chi n‖ = 1 := by
  unfold chi
  rw [AddChar.mulShift_apply, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem z_exp : z = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  change ZMod.stdAddChar (2 : ZMod 12) = _
  have h := ZMod.stdAddChar_coe (N := 12) (2 : ℤ)
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at h
  rw [h]
  congr 1
  push_cast
  ring

private theorem z_norm : ‖z‖ = 1 := chi_norm 1

private theorem z_re : z.re = 1 / 2 := by
  rw [z_exp, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]

private theorem z_conj : starRingEnd ℂ z = 1 - z := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
    linarith only [z_re]
  · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
    ring

private theorem z_unit : z * starRingEnd ℂ z = 1 := by
  rw [Complex.mul_conj', z_norm]
  norm_num

private theorem z_poly : z ^ 2 - z + 1 = 0 := by
  have h := z_unit
  rw [z_conj] at h
  linear_combination -h

private theorem z_ne_zero : z ≠ 0 := by
  intro h
  have hn := z_norm
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

private theorem z_ne_one : z ≠ 1 := by
  intro h
  have hr := z_re
  rw [h, Complex.one_re] at hr
  norm_num at hr

private theorem chi_sum : ∑ n : ZMod 12, chi n = 0 :=
  AddChar.sum_eq_zero_of_ne_one (AddChar.ne_one_iff.mpr ⟨1, z_ne_one⟩)

private theorem chi_neg_one : chi (-1) = starRingEnd ℂ z := by
  rw [chi.map_neg_eq_inv]
  exact Complex.inv_eq_conj z_norm

private def lam : ℂ := ((a : ℂ) + (c : ℂ)) * z - (c : ℂ)

private theorem resonance : lam * starRingEnd ℂ lam = 1 ∧
    lam ^ 2 + ((c : ℂ) - (a : ℂ)) * lam + 1 = 0 ∧
    lam * ((c : ℂ) + (a : ℂ) * z) = z - 1 := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hc := congrArg Complex.ofReal scalar_resonance
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
  constructor
  · unfold lam
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, z_conj]
    linear_combination -((a : ℂ) + (c : ℂ)) ^ 2 * z_poly + (1 / 2 : ℂ) * ha + hc
  constructor
  · unfold lam
    linear_combination ((a : ℂ) + (c : ℂ)) ^ 2 * z_poly - (1 / 2 : ℂ) * ha - hc
  · unfold lam
    linear_combination (a : ℂ) * ((a : ℂ) + (c : ℂ)) * z_poly +
      ((z - 1) / 2) * ha + (z - 1) * hc

private def B (q : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if i.1 = 0 then
    if i.2 = 0 then if j.1 = 0 then (a : ℂ) * q else 0
    else if j.1 = 0 then 0 else if j.2 = 0 then (c : ℂ) * q else (s : ℂ) * q
  else if i.2 = 0 then
    if j.1 = 0 then
      if j.2 = 0 then (a : ℂ) * starRingEnd ℂ q else -(a : ℂ) * starRingEnd ℂ q
    else 0
  else if j.1 = 0 then 0
  else if j.2 = 0 then (s : ℂ) * starRingEnd ℂ q else -(c : ℂ) * starRingEnd ℂ q

private theorem B_apply (q : ℂ) (u : Fin 2 × Fin 2 → ℂ) (i : Fin 2 × Fin 2) :
    (B q *ᵥ u) i =
      if i.1 = 0 then
        if i.2 = 0 then (a : ℂ) * q * (u (0, 0) + u (0, 1))
        else q * ((c : ℂ) * u (1, 0) + (s : ℂ) * u (1, 1))
      else if i.2 = 0 then (a : ℂ) * starRingEnd ℂ q * (u (0, 0) - u (0, 1))
      else starRingEnd ℂ q * ((s : ℂ) * u (1, 0) - (c : ℂ) * u (1, 1)) := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  all_goals
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    dsimp only [B]
    simp only [Fin.ext_iff, Fin.val_zero, one_ne_zero, ite_true, ite_false]
    ring

private theorem mode_step (η : AddChar (ZMod 12) ℂ)
    (hη : η (-1) = starRingEnd ℂ (η 1)) (u : Fin 2 × Fin 2 → ℂ) :
    U phiStar (fun n i => η n * u i) = fun n i => η n * (B (η 1) *ᵥ u) i := by
  funext n i
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  all_goals
    rw [B_apply]
    unfold U swap shift coinFlip
    rw [Fin.sum_univ_two]
  · change (Real.cos (Real.pi / 4) : ℂ) * (η (n + 1) * u (0, 0)) +
      (Real.sin (Real.pi / 4) : ℂ) * (η (n + 1) * u (0, 1)) =
        η n * ((a : ℂ) * η 1 * (u (0, 0) + u (0, 1)))
    rw [show Real.cos (Real.pi / 4) = a from Real.cos_pi_div_four,
      show Real.sin (Real.pi / 4) = a from Real.sin_pi_div_four, η.map_add_eq_mul]
    ring
  · change (Real.cos (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + 1) * u (1, 0)) +
      (Real.sin (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + 1) * u (1, 1)) =
        η n * (η 1 * ((c : ℂ) * u (1, 0) + (s : ℂ) * u (1, 1)))
    rw [phi_facts.2.2, theta_facts.2.2, show Real.sin theta = s from rfl,
      η.map_add_eq_mul]
    ring
  · change (Real.sin (Real.pi / 4) : ℂ) * (η (n + -1) * u (0, 0)) +
      ((-Real.cos (Real.pi / 4) : ℝ) : ℂ) * (η (n + -1) * u (0, 1)) =
        η n * ((a : ℂ) * starRingEnd ℂ (η 1) * (u (0, 0) - u (0, 1)))
    rw [show Real.sin (Real.pi / 4) = a from Real.sin_pi_div_four,
      show Real.cos (Real.pi / 4) = a from Real.cos_pi_div_four,
      Complex.ofReal_neg, η.map_add_eq_mul, hη]
    ring
  · change (Real.sin (Real.pi * (1 + phiStar) / 4) : ℂ) * (η (n + -1) * u (1, 0)) +
      ((-Real.cos (Real.pi * (1 + phiStar) / 4) : ℝ) : ℂ) * (η (n + -1) * u (1, 1)) =
        η n * (starRingEnd ℂ (η 1) * ((s : ℂ) * u (1, 0) - (c : ℂ) * u (1, 1)))
    rw [phi_facts.2.2, theta_facts.2.2, show Real.sin theta = s from rfl,
      Complex.ofReal_neg, η.map_add_eq_mul, hη]
    ring

private theorem character_mode (u : Fin 2 × Fin 2 → ℂ) :
    U phiStar (fun n i => chi n * u i) = fun n i => chi n * (B z *ᵥ u) i :=
  mode_step chi chi_neg_one u

private theorem trivial_mode (u : Fin 2 × Fin 2 → ℂ) :
    U (d := 12) phiStar (fun _ i => u i) = fun _ i => (B 1 *ᵥ u) i := by
  simpa only [AddChar.one_apply, one_mul] using
    mode_step (1 : AddChar (ZMod 12) ℂ) (by simp only [AddChar.one_apply, map_one]) u

end D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity
