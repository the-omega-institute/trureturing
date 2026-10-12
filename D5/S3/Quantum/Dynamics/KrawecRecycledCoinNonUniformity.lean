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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.LinearAlgebra.Matrix.Trace

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


private def v (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then a else lam - a
  else if i.2 = 0 then -lam - c else -s

private def w (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then a else (c : ℂ) * z
  else if i.2 = 0 then -c else (kappa : ℂ) * s * z

private theorem eigenvectors : B 1 *ᵥ v = lam • v ∧ B z *ᵥ w = lam • w := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hs : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast sin_sq
  have hc : (c : ℂ) * ((a : ℂ) + c) = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.1
  have hk : (kappa : ℂ) * (s : ℂ) ^ 2 = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.2
  have hca : (c : ℂ) = (a : ℂ) * kappa := by unfold c; push_cast; rfl
  constructor
  · ext ⟨i, j⟩
    rw [B_apply]
    fin_cases i <;> fin_cases j
    all_goals
      simp only [v, Pi.smul_apply, smul_eq_mul, Fin.ext_iff, Fin.val_zero,
        one_ne_zero, ite_true, ite_false, map_one, mul_one, one_mul]
    · ring
    · linear_combination -resonance.2.1 - hs
    · linear_combination resonance.2.1 + ha
    · ring
  · ext ⟨i, j⟩
    rw [B_apply]
    fin_cases i <;> fin_cases j
    all_goals
      simp only [w, Pi.smul_apply, smul_eq_mul, Fin.ext_iff, Fin.val_zero,
        one_ne_zero, ite_true, ite_false, z_conj]
      unfold lam
    · linear_combination (a : ℂ) * (c : ℂ) * z_poly
    · linear_combination z ^ 2 * hk - z ^ 2 * hc
    · linear_combination (a : ℂ) * (c : ℂ) * z_poly + (z - 1) * hc
    · rw [hca]
      linear_combination -(a : ℂ) * (kappa : ℂ) * (s : ℂ) * z_poly

private theorem coin_overlap :
    (∑ i : Fin 2 × Fin 2, starRingEnd ℂ (v i) * w i) =
      (3 / 2 : ℂ) * starRingEnd ℂ z := by
  have ha : 2 * (a : ℂ) ^ 2 = 1 := by exact_mod_cast a_facts.1
  have hc : (c : ℂ) * ((a : ℂ) + c) = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.1
  have hk : (kappa : ℂ) * (s : ℂ) ^ 2 = (a : ℂ) ^ 2 := by
    exact_mod_cast scalar_reductions.2
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  change starRingEnd ℂ (a : ℂ) * a +
    starRingEnd ℂ (lam - a) * ((c : ℂ) * z) +
    (starRingEnd ℂ (-lam - c) * (-c) +
    starRingEnd ℂ (-s : ℂ) * ((kappa : ℂ) * s * z)) = _
  simp only [map_sub, map_neg, Complex.conj_ofReal]
  unfold lam
  simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, z_conj]
  linear_combination -(c : ℂ) * ((a : ℂ) + c) * z_poly +
    (2 - 2 * z) * hc - z * hk + (3 / 2 : ℂ) * (1 - z) * ha

private abbrev Index := ZMod 12 × (Fin 2 × Fin 2)
private abbrev H := EuclideanSpace ℂ Index
private abbrev K := EuclideanSpace ℂ (Index × Index)

private theorem coin_inner (θ : ℝ) (x y : Fin 2 → ℂ) :
    (∑ i : Fin 2,
      starRingEnd ℂ (∑ j : Fin 2,
        (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3 θ i j : ℂ) * x j) *
      (∑ j : Fin 2,
        (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3 θ i j : ℂ) * y j)) =
      ∑ i : Fin 2, starRingEnd ℂ (x i) * y i := by
  have h : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  simp only [Fin.sum_univ_two]
  change starRingEnd ℂ ((Real.cos θ : ℂ) * x 0 + (Real.sin θ : ℂ) * x 1) *
      ((Real.cos θ : ℂ) * y 0 + (Real.sin θ : ℂ) * y 1) +
    starRingEnd ℂ ((Real.sin θ : ℂ) * x 0 + ((-Real.cos θ : ℝ) : ℂ) * x 1) *
      ((Real.sin θ : ℂ) * y 0 + ((-Real.cos θ : ℝ) : ℂ) * y 1) = _
  simp only [Complex.ofReal_neg, map_add, map_neg, map_mul, Complex.conj_ofReal]
  linear_combination (starRingEnd ℂ (x 0) * y 0 + starRingEnd ℂ (x 1) * y 1) * h

private theorem walk_inner (x y : ZMod 12 → Fin 2 × Fin 2 → ℂ) :
    (∑ n, ∑ i, starRingEnd ℂ (U phiStar x n i) * U phiStar y n i) =
      ∑ n, ∑ i, starRingEnd ℂ (x n i) * y n i := by
  calc
    _ = ∑ i : Fin 2 × Fin 2, ∑ n : ZMod 12,
        starRingEnd ℂ (coinFlip phiStar x
          (n + (if i.1 = 0 then 1 else -1)) (i.2, i.1)) *
        coinFlip phiStar y (n + (if i.1 = 0 then 1 else -1)) (i.2, i.1) := by
      rw [Finset.sum_comm]; rfl
    _ = ∑ i : Fin 2 × Fin 2, ∑ n : ZMod 12,
        starRingEnd ℂ (coinFlip phiStar x n (i.2, i.1)) *
        coinFlip phiStar y n (i.2, i.1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (Equiv.addRight (if i.1 = 0 then (1 : ZMod 12) else -1))
        (fun n => starRingEnd ℂ (coinFlip phiStar x n (i.2, i.1)) *
          coinFlip phiStar y n (i.2, i.1))
    _ = ∑ n : ZMod 12, ∑ i : Fin 2 × Fin 2,
        starRingEnd ℂ (coinFlip phiStar x n i) * coinFlip phiStar y n i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      exact (Equiv.prodComm (Fin 2) (Fin 2)).sum_comp
        (fun i => starRingEnd ℂ (coinFlip phiStar x n i) * coinFlip phiStar y n i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      exact coin_inner (angle phiStar i) (fun j => x n (i, j)) (fun j => y n (i, j))

private def walkLin : H →ₗ[ℂ] H where
  toFun x := WithLp.toLp 2 (fun i => U phiStar (fun n j => x (n, j)) i.1 i.2)
  map_add' x y := by
    ext ⟨n, i, j⟩
    change U phiStar (fun n j => x (n, j) + y (n, j)) n (i, j) =
      U phiStar (fun n j => x (n, j)) n (i, j) + U phiStar (fun n j => y (n, j)) n (i, j)
    unfold U swap shift coinFlip
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext ⟨n, i, j⟩
    change U phiStar (fun n j => r * x (n, j)) n (i, j) =
      r * U phiStar (fun n j => x (n, j)) n (i, j)
    unfold U swap shift coinFlip
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

private def walkIso : H →ₗᵢ[ℂ] H := walkLin.isometryOfInner (by
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', walkLin, LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_prod_type]
  simpa only [Fintype.sum_prod_type] using walk_inner (fun n j => x (n, j)) (fun n j => y (n, j)))

private def walkEquiv : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective walkIso
    (LinearMap.surjective_of_injective walkIso.injective)

private def M : Matrix Index Index ℂ :=
  walkEquiv.toLinearEquiv.toLinearMap.toMatrix
    (EuclideanSpace.basisFun Index ℂ).toBasis (EuclideanSpace.basisFun Index ℂ).toBasis

private theorem M_unitary : Mᴴ * M = 1 ∧ M * Mᴴ = 1 := by
  exact walkEquiv.toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun Index ℂ) (EuclideanSpace.basisFun Index ℂ)

private theorem M_step (x : H) :
    M *ᵥ (fun i => x i) = fun i => U phiStar (fun n j => x (n, j)) i.1 i.2 := by
  exact walkEquiv.toLinearEquiv.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun Index ℂ).toBasis
    (EuclideanSpace.basisFun Index ℂ).toBasis x

private def flat (A : Matrix Index Index ℂ) : K :=
  WithLp.toLp 2 (fun i => A i.1 i.2)
private def mat (A : K) : Matrix Index Index ℂ := fun i j => A (i, j)

private theorem hs_inner (A B : K) : inner ℂ A B = ((mat A)ᴴ * mat B).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [RCLike.inner_apply', Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mat, starRingEnd_apply]
  rw [Finset.sum_comm]

private def conjugateLin : K →ₗ[ℂ] K where
  toFun A := flat (M * mat A * Mᴴ)
  map_add' A B := by
    change flat (M * (mat A + mat B) * Mᴴ) = flat (M * mat A * Mᴴ) + flat (M * mat B * Mᴴ)
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' r A := by
    change flat (M * (r • mat A) * Mᴴ) = r • flat (M * mat A * Mᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

private def F : K →ₗᵢ[ℂ] K := conjugateLin.isometryOfInner (by
  intro A B
  rw [hs_inner, hs_inner]
  change ((M * mat A * Mᴴ)ᴴ * (M * mat B * Mᴴ)).trace = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Mᴴ M, M_unitary.1, Matrix.one_mul]
  rw [Matrix.trace_mul_comm M]
  simp only [Matrix.mul_assoc, M_unitary.1, Matrix.mul_one])

private def E : Submodule ℂ K := F.toContinuousLinearMap.eqLocus 1
private def Q : K →L[ℂ] K := E.starProjection

private theorem QF (A : K) : Q (F A) = Q A := by
  apply E.eq_starProjection_of_mem_of_inner_eq_zero (E.starProjection_apply_mem A)
  intro Z hZ
  have hz : F Z = Z := hZ
  have hi : inner ℂ (F A) Z = inner ℂ A Z := by
    calc
      _ = inner ℂ (F A) (F Z) := congrArg (inner ℂ (F A)) hz.symm
      _ = _ := F.inner_map_map A Z
  rw [inner_sub_left, hi]
  have h := E.starProjection_inner_eq_zero A Z hZ
  rw [inner_sub_left] at h
  exact h

private def identity : K := flat 1
private def P : K := flat (Matrix.diagonal (fun i : Index => if i.1 = 0 then 1 else 0))
private def outer (x y : H) : K :=
  flat (Matrix.vecMulVec (fun i => x i) (fun i => starRingEnd ℂ (y i)))

private theorem F_identity : F identity = identity := by
  change flat (M * 1 * Mᴴ) = flat 1
  rw [Matrix.mul_one, M_unitary.2]

private theorem identity_inner (A : K) : inner ℂ identity A = (mat A).trace := by
  rw [hs_inner]
  change ((1 : Matrix Index Index ℂ)ᴴ * mat A).trace = _
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

private theorem F_outer (x y : H) : F (outer x y) = outer (walkIso x) (walkIso y) := by
  change flat (M * Matrix.vecMulVec (fun i => x i) (fun i => starRingEnd ℂ (y i)) * Mᴴ) = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hy : (fun i => starRingEnd ℂ (y i)) ᵥ* Mᴴ =
      fun j => starRingEnd ℂ ((M *ᵥ (fun i => y i)) j) := by
    funext j
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      map_sum, map_mul, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hy, M_step x, M_step y]
  rfl

private theorem P_inner (A : K) :
    inner ℂ P A = ∑ j : Fin 2 × Fin 2, A ((0, j), (0, j)) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  change (∑ i : Index, ∑ j : Index,
    A (i, j) * starRingEnd ℂ (Matrix.diagonal
      (fun k : Index => if k.1 = 0 then (1 : ℂ) else 0) i j)) = _
  simp only [Matrix.diagonal_apply, apply_ite, map_zero, map_one, mul_one,
    mul_zero, Fintype.sum_ite_eq]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']

private def f : H := WithLp.toLp 2 (fun i => v i.2)
private def g : H := WithLp.toLp 2 (fun i => chi i.1 * w i.2)
private def X : K := outer f g
private def Y : K := (1 / 12 : ℂ) • identity

private theorem global_eigenvectors : walkIso f = lam • f ∧ walkIso g = lam • g := by
  constructor
  · ext ⟨n, j⟩
    change U phiStar (fun _ i => v i) n j = lam * v j
    rw [trivial_mode, eigenvectors.1]
    rfl
  · ext ⟨n, j⟩
    change U phiStar (fun n i => chi n * w i) n j = lam * (chi n * w j)
    rw [character_mode, eigenvectors.2]
    change chi n * (lam * w j) = _
    ring

private theorem X_fixed : F X = X := by
  rw [X, F_outer, global_eigenvectors.1, global_eigenvectors.2]
  ext ⟨i, j⟩
  change (lam * f i) * starRingEnd ℂ (lam * g j) = f i * starRingEnd ℂ (g j)
  rw [map_mul]
  calc
    _ = (lam * starRingEnd ℂ lam) * (f i * starRingEnd ℂ (g j)) := by ring
    _ = _ := by rw [resonance.1, one_mul]

private theorem X_pairings : inner ℂ X identity = 0 ∧ inner ℂ X P ≠ 0 := by
  constructor
  · have htr : (mat X).trace = 0 := by
      change (∑ i : Index, v i.2 * starRingEnd ℂ (chi i.1 * w i.2)) = 0
      rw [Fintype.sum_prod_type]
      simp only [map_mul]
      calc
        _ = (∑ n : ZMod 12, starRingEnd ℂ (chi n)) *
            (∑ j : Fin 2 × Fin 2, v j * starRingEnd ℂ (w j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [← map_sum, chi_sum, map_zero, zero_mul]
    rw [← inner_conj_symm, identity_inner, htr, map_zero]
  · rw [← inner_conj_symm, P_inner]
    change starRingEnd ℂ (∑ j, v j * starRingEnd ℂ (chi 0 * w j)) ≠ 0
    simp only [AddChar.map_zero_eq_one, one_mul, map_sum, map_mul, Complex.conj_conj]
    rw [coin_overlap]
    exact mul_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr z_ne_zero)

private theorem baseline : F Y = Y ∧ inner ℂ Y P = 1 / 3 ∧ ‖Y‖ ^ 2 = 1 / 3 := by
  have hp : (mat P).trace = 4 := by
    change (Matrix.diagonal (fun i : Index => if i.1 = 0 then (1 : ℂ) else 0)).trace = 4
    rw [Matrix.trace_diagonal, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fintype.sum_ite_eq', Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  have hi : inner ℂ identity identity = 48 := by
    rw [identity_inner]
    change (1 : Matrix Index Index ℂ).trace = 48
    rw [Matrix.trace_one]
    norm_num only [Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · change F ((1 / 12 : ℂ) • identity) = (1 / 12 : ℂ) • identity
    rw [map_smul, F_identity]
  · rw [Y, inner_smul_left, identity_inner, hp]
    norm_num [map_ofNat]
  · rw [@norm_sq_eq_re_inner ℂ, Y, inner_smul_left, inner_smul_right, hi]
    norm_num

private theorem projection_pairing (Z A : K) (hZ : F Z = Z) :
    inner ℂ Z (Q A) = inner ℂ Z A := by
  have hz : Z ∈ E := hZ
  change inner ℂ Z (E.starProjection A) = inner ℂ Z A
  rw [← E.inner_starProjection_left_eq_right, E.starProjection_eq_self_iff.mpr hz]

private theorem strict_surplus : 1 / 3 < ‖Q P‖ ^ 2 := by
  have hne : Q P - Y ≠ 0 := by
    intro h
    have he : Q P = Y := sub_eq_zero.mp h
    have hxp := projection_pairing X P X_fixed
    rw [he, Y, inner_smul_right, X_pairings.1, mul_zero] at hxp
    exact X_pairings.2 hxp.symm
  have horth : inner ℂ Y (Q P - Y) = 0 := by
    rw [inner_sub_right, projection_pairing Y P baseline.1, baseline.2.1]
    have hy : inner ℂ Y Y = (1 / 3 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, baseline.2.2]
      norm_num
    rw [hy, sub_self]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero Y (Q P - Y) horth
  rw [add_sub_cancel] at hp
  simp only [← pow_two] at hp
  rw [baseline.2.2] at hp
  have hpos : 0 < ‖Q P - Y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  linarith only [hp, hpos]

end D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity
