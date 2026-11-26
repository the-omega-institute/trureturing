/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quaternion face geometry and defect estimates near the cyclic quarter turn. -/

import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! The four face classes determine the exact defect of a hub-gauged assignment.
The local rim trace yields a bound on the cosine of its scaled defect. -/

noncomputable section

open Real Quaternion
open scoped Quaternion InnerProductSpace

namespace RoundQuaternionLocalSharpness

open RoundQuaternionK4Bounds
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (unitI coe_unitary_eq_sphere)

local notation "U" => unitary ℍ[ℝ]

/-- The three spokes and the diagonal carry the identity gain. -/
def hubGaugedGains (A : Fin 3 → U) : Fin 4 → Fin 4 → U :=
  ![![1, 1, 1, 1], ![1, 1, A 0, (A 2)⁻¹], ![1, (A 0)⁻¹, 1, A 1],
    ![1, A 2, (A 1)⁻¹, 1]]

/-- The face maximum uses the three spoke triangles and the cyclic rim triangle. -/
def hubMaxDefect (A : Fin 3 → U) : ℝ :=
  max (max (roundDist 1 (A 0)) (max (roundDist 1 (A 1)) (roundDist 1 (A 2))))
    (roundDist (A 0 * A 1 * A 2) 1)

/-- The ratio of the sharp quarter-turn fit radius to its triangle defect. -/
def cStar : ℝ := 2 * quarterError / π

private theorem unit_norm (a : U) : ‖(a : ℍ[ℝ])‖ = 1 :=
  CStarRing.norm_coe_unitary a

def asUnit (a : ℍ[ℝ]) (ha : normSq a = 1) : U :=
  ⟨a, by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    rw [normSq_eq_norm_mul_self] at ha
    nlinarith [norm_nonneg a]⟩

private theorem re_comm (x y : ℍ[ℝ]) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]
  ring

private theorem re_cyclic (x y z : ℍ[ℝ]) : (x * y * z).re = (y * z * x).re := by
  rw [mul_assoc, re_comm x]

private theorem dist_trace (a b : U) :
    roundDist a b = arccos (((a * b⁻¹ : U) : ℍ[ℝ]).re) := by
  rw [roundDist, Quaternion.inner_def, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]

private theorem hub_reverse (A : Fin 3 → U) (i j : Fin 4) :
    hubGaugedGains A j i = (hubGaugedGains A i j)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [hubGaugedGains]

private theorem hub_faces (A : Fin 3 → U) :
    DefectLE (hubGaugedGains A) (hubMaxDefect A) ∧
    ∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      roundDist (hubGaugedGains A i j * hubGaugedGains A j k)
        (hubGaugedGains A i k) = hubMaxDefect A := by
  let g := hubGaugedGains A
  let a := roundDist 1 (A 0)
  let b := roundDist 1 (A 1)
  let c := roundDist 1 (A 2)
  let d := roundDist (A 0 * A 1 * A 2) 1
  have h01 : roundDist (g 0 1 * g 1 2) (g 0 2) = a := by
    simp [g, a, hubGaugedGains, roundDist, real_inner_comm]
  have h02 : roundDist (g 0 2 * g 2 3) (g 0 3) = b := by
    simp [g, b, hubGaugedGains, roundDist, real_inner_comm]
  have h03 : roundDist (g 0 3 * g 3 1) (g 0 1) = c := by
    simp [g, c, hubGaugedGains, roundDist, real_inner_comm]
  have h12 : roundDist (g 1 2 * g 2 3) (g 1 3) = d := by
    simp [g, d, hubGaugedGains, dist_trace]
  have hrev (i j : Fin 4) : g j i = (g i j)⁻¹ := hub_reverse A i j
  have t (i j k : Fin 4) :
      roundDist (g i j * g j k) (g i k) =
        arccos (((g i j * g j k * g k i : U) : ℍ[ℝ]).re) := by
    rw [dist_trace, hrev i k]
  have cycle (i j k : Fin 4) :
      roundDist (g j k * g k i) (g j i) = roundDist (g i j * g j k) (g i k) := by
    rw [t, t, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    rw [re_cyclic (g i j : ℍ[ℝ])]
  have reverse (i j k : Fin 4) :
      roundDist (g k j * g j i) (g k i) = roundDist (g i j * g j k) (g i k) := by
    rw [t, t, hrev j k, hrev i j, hrev k i]
    rw [← mul_inv_rev, ← mul_inv_rev, ← Unitary.star_eq_inv, Unitary.coe_star, Quaternion.re_star]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    rw [re_comm (g k i : ℍ[ℝ])]
  have exactFace (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      let e := roundDist (g i j * g j k) (g i k)
      e = a ∨ e = b ∨ e = c ∨ e = d := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim | skip
    all_goals dsimp only
    · exact Or.inl h01
    · exact Or.inr (Or.inr (Or.inl ((cycle 3 0 1).trans ((cycle 1 3 0).trans ((reverse 0 3 1).trans h03)))))
    · exact Or.inl ((cycle 1 0 2).trans ((cycle 2 1 0).trans ((reverse 0 1 2).trans h01)))
    · exact Or.inr (Or.inl h02)
    · exact Or.inr (Or.inr (Or.inl h03))
    · exact Or.inr (Or.inl ((cycle 2 0 3).trans ((cycle 3 2 0).trans ((reverse 0 2 3).trans h02))))
    · exact Or.inl ((cycle 2 1 0).trans ((reverse 0 1 2).trans h01))
    · exact Or.inr (Or.inr (Or.inl ((cycle 3 1 0).trans ((cycle 0 3 1).trans h03))))
    · exact Or.inl ((cycle 0 1 2).trans h01)
    · exact Or.inr (Or.inr (Or.inr h12))
    · exact Or.inr (Or.inr (Or.inl ((reverse 0 3 1).trans h03)))
    · exact Or.inr (Or.inr (Or.inr ((cycle 2 1 3).trans ((cycle 3 2 1).trans ((reverse 1 2 3).trans h12)))))
    · exact Or.inl ((cycle 1 2 0).trans ((cycle 0 1 2).trans h01))
    · exact Or.inr (Or.inl ((cycle 3 2 0).trans ((reverse 0 2 3).trans h02)))
    · exact Or.inl ((reverse 0 1 2).trans h01)
    · exact Or.inr (Or.inr (Or.inr ((cycle 3 2 1).trans ((reverse 1 2 3).trans h12))))
    · exact Or.inr (Or.inl ((cycle 0 2 3).trans h02))
    · exact Or.inr (Or.inr (Or.inr ((cycle 1 2 3).trans h12)))
    · exact Or.inr (Or.inr (Or.inl ((cycle 1 3 0).trans ((reverse 0 3 1).trans h03))))
    · exact Or.inr (Or.inl ((cycle 2 3 0).trans ((cycle 0 2 3).trans h02)))
    · exact Or.inr (Or.inr (Or.inl ((cycle 0 3 1).trans h03)))
    · exact Or.inr (Or.inr (Or.inr ((cycle 2 3 1).trans ((cycle 1 2 3).trans h12))))
    · exact Or.inr (Or.inl ((reverse 0 2 3).trans h02))
    · exact Or.inr (Or.inr (Or.inr ((reverse 1 2 3).trans h12)))
  refine ⟨⟨hub_reverse A, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i j k hij hjk hik
    change roundDist (g i j * g j k) (g i k) ≤ max (max a (max b c)) d
    rcases exactFace i j k hij hjk hik with h | h | h | h
    · exact h.le.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h.le.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    · exact h.le.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    · exact h.le.trans (le_max_right _ _)
  · change ∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      roundDist (g i j * g j k) (g i k) = max (max a (max b c)) d
    rcases max_choice (max a (max b c)) d with h | h
    · rw [h]
      rcases max_choice a (max b c) with h | h
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h01.trans h.symm⟩
      · rw [h]
        rcases max_choice b c with h | h
        · exact ⟨0, 2, 3, by decide, by decide, by decide, h02.trans h.symm⟩
        · exact ⟨0, 3, 1, by decide, by decide, by decide, h03.trans h.symm⟩
    · exact ⟨1, 2, 3, by decide, by decide, by decide, h12.trans h.symm⟩


def conjugate (C a : U) : U := C * a * C⁻¹

private theorem conj_mul (C a b : U) :
    conjugate C (a * b) = conjugate C a * conjugate C b := by
  unfold conjugate
  group

private theorem conj_inv (C a : U) :
    conjugate C a⁻¹ = (conjugate C a)⁻¹ := by
  unfold conjugate
  group

private theorem conj_one (C : U) : conjugate C 1 = 1 := by
  simp [conjugate]

private theorem conj_cancel (C a : U) : conjugate C⁻¹ (conjugate C a) = a := by
  unfold conjugate
  group

private theorem conj_trace (C a : U) :
    ((conjugate C a : U) : ℍ[ℝ]).re = (a : ℍ[ℝ]).re := by
  change (((C : ℍ[ℝ]) * (a : ℍ[ℝ])) * (↑(C⁻¹) : ℍ[ℝ])).re = _
  rw [← re_cyclic (↑(C⁻¹) : ℍ[ℝ]), ← Submonoid.coe_mul,
    inv_mul_cancel, OneMemClass.coe_one, one_mul]

private theorem conj_inner (C a b : U) :
    ⟪(conjugate C a : ℍ[ℝ]), (conjugate C b : ℍ[ℝ])⟫_ℝ =
      ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ := by
  simp only [Quaternion.inner_def]
  change ((↑(conjugate C a * (conjugate C b)⁻¹) : ℍ[ℝ])).re =
    (↑(a * b⁻¹) : ℍ[ℝ]).re
  rw [← conj_inv, ← conj_mul, conj_trace]

private theorem conj_dist (C a b : U) :
    roundDist (conjugate C a) (conjugate C b) = roundDist a b := by
  simp only [roundDist, conj_inner]

private theorem conjugate_hub (C : U) (A : Fin 3 → U) (i j : Fin 4) :
    hubGaugedGains (conjugate C ∘ A) i j = conjugate C (hubGaugedGains A i j) := by
  fin_cases i <;> fin_cases j <;> simp [hubGaugedGains, conj_one, conj_inv]

private theorem conjugate_hubMaxDefect (C : U) (A : Fin 3 → U) :
    hubMaxDefect (conjugate C ∘ A) = hubMaxDefect A := by
  have h₁ (a : U) : roundDist 1 (conjugate C a) = roundDist 1 a := by
    simpa only [conj_one] using conj_dist C 1 a
  have h₂ (a : U) : roundDist (conjugate C a) 1 = roundDist a 1 := by
    simpa only [conj_one] using conj_dist C a 1
  simp only [hubMaxDefect, Function.comp_apply, ← conj_mul, h₁, h₂]

private theorem conjugate_fits (C : U) (g : Fin 4 → Fin 4 → U) (φ : Fin 4 → U) (R : ℝ) :
    Fits (fun i j => conjugate C (g i j)) (conjugate C ∘ φ) R ↔ Fits g φ R := by
  simp only [Fits, Function.comp_apply, ← conj_inv, ← conj_mul, conj_dist]

private theorem score_ge_iff {a b : U} {R : ℝ} (hR : R ∈ Set.Icc 0 π) :
    roundDist a b ≤ R ↔ cos R ≤ ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ := by
  have hb : |⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ| ≤ 1 := by
    simpa only [unit_norm, mul_one] using abs_real_inner_le_norm (a : ℍ[ℝ]) (b : ℍ[ℝ])
  have ha := abs_le.mp hb
  constructor
  · intro h
    have hh := Real.strictAntiOn_cos.antitoneOn ⟨arccos_nonneg _, arccos_le_pi _⟩ hR h
    simpa only [roundDist, cos_arccos ha.1 ha.2] using hh
  · intro h
    exact (arccos_le_arccos h).trans_eq (arccos_cos hR.1 hR.2)

private theorem strict_fit_of_scores {g : Fin 4 → Fin 4 → U} {φ : Fin 4 → U} {R δ : ℝ}
    (hR : R ∈ Set.Icc 0 π) (hd : 0 < δ)
    (hs : ∀ i j, i ≠ j → cos R + δ ≤
      ⟪(g i j : ℍ[ℝ]), (↑((φ i)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ) :
    ∃ s < R, Fits g φ s := by
  let k := cos R + δ
  have hk₁ : k ≤ 1 := (hs 0 1 (by decide)).trans (by
    simpa only [unit_norm, mul_one] using real_inner_le_norm
      (g 0 1 : ℍ[ℝ]) (↑((φ 0)⁻¹ * φ 1) : ℍ[ℝ]))
  have hk₀ : -1 ≤ k := by linarith [neg_one_le_cos R]
  refine ⟨arccos k, ?_, fun i j hij => arccos_le_arccos (hs i j hij)⟩
  rw [← arccos_cos hR.1 hR.2]
  exact strictAntiOn_arccos ⟨neg_one_le_cos R, cos_le_one R⟩ ⟨hk₀, hk₁⟩
    (lt_add_of_pos_right _ hd)

/-- The primitive third root of unity with positive imaginary part. -/
def zeta : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

def rimPhase (j : Fin 3) : ℂ := ![1, star zeta, zeta] j

/-- The two nonconstant Fourier modes of the transverse rim coordinates. -/
def transverse (p q : ℂ) (j : Fin 3) : ℂ :=
  p * star (rimPhase j) + q * rimPhase j

/-- The complex-pair coordinates of a quaternion in the frame \(1,I,J,IJ\). -/
def quatPair (z h : ℂ) : ℍ[ℝ] := ⟨z.re, z.im, h.re, h.im⟩

/-- The maximum absolute scalar perturbation on the rim. -/
def etaMax (η : Fin 3 → ℝ) : ℝ := max |η 0| (max |η 1| |η 2|)

/-- The Fourier and scalar perturbation threshold. -/
def localR : ℝ := 3/50

private theorem local_abs_eta (η : Fin 3 → ℝ) (j : Fin 3) : |η j| ≤ etaMax η := by
  fin_cases j <;> unfold etaMax
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem local_eta_nonneg (η : Fin 3 → ℝ) : 0 ≤ etaMax η :=
  (abs_nonneg (η 0)).trans (local_abs_eta η 0)

private theorem local_normSq_pair (z h : ℂ) :
    normSq (quatPair z h) = ‖z‖ ^ 2 + ‖h‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [normSq_def', Complex.normSq_apply, quatPair]
  ring

private theorem local_sq_complex (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem local_norm_pair (z h : ℂ) :
    ‖quatPair z h‖ ^ 2 = ‖z‖ ^ 2 + ‖h‖ ^ 2 := by
  rw [← local_normSq_pair, normSq_eq_norm_mul_self, pow_two]

private theorem local_phase_norm (j : Fin 3) : ‖rimPhase j‖ = 1 := by
  have hz : ‖zeta‖ = 1 := by
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h := local_sq_complex (-1/2) (Real.sqrt 3 / 2)
    change ‖zeta‖ ^ 2 = _ at h
    nlinarith [norm_nonneg zeta]
  fin_cases j <;> simp [rimPhase, hz]

private theorem local_pair_sub (z h z' h' : ℂ) :
    quatPair z h - quatPair z' h' = quatPair (z - z') (h - h') := by
  ext <;> rfl

def rimPrev (j : Fin 3) : Fin 3 := j - 1
def rimNext (j : Fin 3) : Fin 3 := j + 1

private theorem quarterBase_bounds :
    (5773 / 10000 : ℝ) < 1 / √3 ∧ 1 / √3 < 5774 / 10000 := by
  have ht : (0 : ℝ) < 1 / √3 := by positivity
  have hs : ((1 : ℝ) / √3) ^ 2 = 1 / 3 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), one_pow]
  exact ⟨(sq_lt_sq₀ (by norm_num) ht.le).mp (by rw [hs]; norm_num),
    (sq_lt_sq₀ ht.le (by norm_num)).mp (by rw [hs]; norm_num)⟩

private theorem nonneg_of_deriv_nonneg_on_ray {f : ℝ → ℝ} (hd : Differentiable ℝ f)
    (h0 : 0 ≤ f 0) (hm : ∀ z ≥ 0, 0 ≤ deriv f z) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (f := f) hd.continuous.continuousOn hd.differentiableOn
    (fun z hz => hm z (interior_subset hz))
  exact h0.trans (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx)

private theorem localCos_taylor {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x ∧
      cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h4 (y : ℝ) (hy : 0 ≤ y) : cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
    let f (z : ℝ) := 1 - z ^ 2 / 2 + z ^ 4 / 24 - cos z
    have h' (z : ℝ) : deriv f z = sin z - (z - z ^ 3 / 6) := by
      simp (disch := fun_prop) [f]
      ring
    exact sub_nonneg.mp (nonneg_of_deriv_nonneg_on_ray (f := f)
      (by dsimp [f]; fun_prop) (by simp [f])
      (fun z hz => by rw [h']; exact sub_nonneg.mpr (sin_ge_sub_cube hz)) hy)
  have h5 (y : ℝ) (hy : 0 ≤ y) : sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
    let f (z : ℝ) := z - z ^ 3 / 6 + z ^ 5 / 120 - sin z
    have h' (z : ℝ) : deriv f z = 1 - z ^ 2 / 2 + z ^ 4 / 24 - cos z := by
      simp (disch := fun_prop) [f]
      ring
    exact sub_nonneg.mp (nonneg_of_deriv_nonneg_on_ray (f := f)
      (by dsimp [f]; fun_prop) (by simp [f])
      (fun z hz => by rw [h']; exact sub_nonneg.mpr (h4 z hz)) hy)
  let f (z : ℝ) := cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 720)
  have h' (z : ℝ) : deriv f z = z - z ^ 3 / 6 + z ^ 5 / 120 - sin z := by
    simp (disch := fun_prop) [f]
    ring
  exact ⟨sub_nonneg.mp (nonneg_of_deriv_nonneg_on_ray (f := f)
    (by dsimp [f]; fun_prop) (by simp [f])
    (fun z hz => by rw [h']; exact sub_nonneg.mpr (h5 z hz)) hx), h4 x hx⟩

private theorem cStar_bounds : 3 / 5 < cStar ∧ cStar < 61 / 100 ∧
    496 / 1000 < cStar * √(2 / 3) ∧ cStar * √(2 / 3) < 1 / 2 := by
  have hlow : (5774 / 10000 : ℝ) < cos (9545 / 10000) := by
    linarith only [(localCos_taylor (by norm_num : (0 : ℝ) ≤ 9545 / 10000)).1]
  have hupp : cos (957 / 1000) < (5773 / 10000 : ℝ) := by
    linarith only [(localCos_taylor (by norm_num : (0 : ℝ) ≤ 957 / 1000)).2]
  have hcos : cos quarterError = 1 / √3 := by
    unfold quarterError
    exact cos_arccos (by linarith [quarterBase_bounds.1]) (by linarith [quarterBase_bounds.2])
  have hmem : quarterError ∈ Set.Icc (0 : ℝ) π :=
    ⟨arccos_nonneg _, arccos_le_pi _⟩
  have hloθ : (9545 / 10000 : ℝ) < quarterError :=
    (strictAntiOn_cos.lt_iff_gt hmem ⟨by norm_num, by linarith [pi_gt_d6]⟩).mp
      (by rw [hcos]; exact quarterBase_bounds.2.trans hlow)
  have hhiθ : quarterError < (957 / 1000 : ℝ) :=
    (strictAntiOn_cos.lt_iff_gt ⟨by norm_num, by linarith [pi_gt_d6]⟩ hmem).mp
      (by rw [hcos]; exact hupp.trans quarterBase_bounds.1)
  have hlo : (6076 / 10000 : ℝ) < cStar := (lt_div_iff₀ pi_pos).mpr
    (by linarith [pi_lt_d6])
  have hhi : cStar < (61 / 100 : ℝ) := (div_lt_iff₀ pi_pos).mpr
    (by linarith [pi_gt_d6])
  have hslo : (8164 / 10000 : ℝ) < √(2 / 3) :=
    lt_sqrt_of_sq_lt (by norm_num)
  have hshi : √(2 / 3) < (817 / 1000 : ℝ) :=
    (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hprod := mul_lt_mul'' hlo hslo (by norm_num) (by norm_num)
  have hsmall : (496 / 1000 : ℝ) < (6076 / 10000) * (8164 / 10000) := by norm_num
  exact ⟨by linarith, hhi, hsmall.trans hprod,
    (mul_lt_mul'' hhi hshi (by linarith) (by positivity)).trans (by norm_num)⟩

private def localAngle (x : ℝ) : ℝ := quarterError + cStar * arcsin x

private def localCos (x : ℝ) : ℝ := cos (localAngle x)

private theorem localAngle_deriv {x : ℝ} (h₁ : -1 < x) (h₂ : x < 1) :
    HasDerivAt localAngle (cStar / √(1 - x ^ 2)) x := by
  change HasDerivAt (fun y => quarterError + cStar * arcsin y) _ x
  rw [show cStar / √(1 - x ^ 2) = cStar * (1 / √(1 - x ^ 2)) by ring]
  exact ((hasDerivAt_arcsin h₁.ne' h₂.ne).const_mul cStar).const_add quarterError

private theorem localCos_deriv {x : ℝ} (h₁ : -1 < x) (h₂ : x < 1) :
    HasDerivAt localCos (- (cStar * sin (localAngle x)) / √(1 - x ^ 2)) x := by
  change HasDerivAt (fun y => cos (localAngle y)) _ x
  rw [show -(cStar * sin (localAngle x)) / √(1 - x ^ 2) =
    -sin (localAngle x) * (cStar / √(1 - x ^ 2)) by ring]
  exact (localAngle_deriv h₁ h₂).cos

private theorem localCos_at_zero :
    localCos 0 = 1 / √3 ∧ sin (localAngle 0) = √(2 / 3) := by
  have ht : (0 : ℝ) ≤ 1 / √3 := by positivity
  have htsq : ((1 : ℝ) / √3) ^ 2 = 1 / 3 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), one_pow]
  simp only [localCos, localAngle, arcsin_zero, mul_zero, add_zero, quarterError]
  refine ⟨cos_arccos (by linarith) (by linarith [quarterBase_bounds.2]), ?_⟩
  rw [sin_arccos, htsq, show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num]

private theorem localCos_strictConcave :
    StrictConcaveOn ℝ (Set.Icc (-(1 / 5 : ℝ)) (1 / 5)) localCos := by
  have hc₀ : 0 < cStar := by linarith [cStar_bounds.1]
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (by
    exact (continuous_cos.comp (continuous_const.add
      (continuous_const.mul continuous_arcsin))).continuousOn)
  intro x hx
  have hx' : x ∈ Set.Icc (-(1 / 5 : ℝ)) (1 / 5) := interior_subset hx
  have hxsq : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := sq_le_sq' hx'.1 hx'.2
  have h₁ : -1 < x := by linarith [hx'.1]
  have h₂ : x < 1 := by linarith [hx'.2]
  let d := √(1 - x ^ 2)
  have hd : (97 / 100 : ℝ) < d := lt_sqrt_of_sq_lt (by linarith)
  have hd₀ : 0 < d := by linarith
  have hasin : |arcsin x| ≤ 205 / 1000 := by
    have hsin : (1 / 5 : ℝ) ≤ sin (205 / 1000) := by
      linarith only [sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 205 / 1000)]
    have hval := arcsin_sin (x := 205 / 1000) (by linarith [pi_pos])
      (by linarith [pi_gt_d6])
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hh := arcsin_le_arcsin (show -x ≤ sin (205 / 1000) by linarith [hx'.1])
      rw [arcsin_neg, hval] at hh
      linarith
    · exact (arcsin_le_arcsin (hx'.2.trans hsin)).trans_eq hval
  have hcos : (45 / 100 : ℝ) < localCos x := by
    have habs := (abs_le.mp (abs_cos_sub_cos_le (localAngle x) quarterError)).1
    have hshift : |localAngle x - quarterError| ≤ (61 / 100) * (205 / 1000) := by
      rw [localAngle, add_sub_cancel_left, abs_mul, abs_of_pos hc₀]
      exact mul_le_mul cStar_bounds.2.1.le hasin (abs_nonneg _) (by norm_num)
    have h0 : cos quarterError = 1 / √3 := by
      simpa [localCos, localAngle] using localCos_at_zero.1
    change -( |localAngle x - quarterError| ) ≤ localCos x - cos quarterError at habs
    linarith only [habs, hshift, h0, quarterBase_bounds.1]
  have hnum : 0 < cStar * localCos x * d + sin (localAngle x) * x := by
    have hcs : (3 / 5 : ℝ) * (45 / 100) < cStar * localCos x :=
      mul_lt_mul'' cStar_bounds.1 hcos (by norm_num) (by norm_num)
    have hcsd := mul_lt_mul'' hcs hd (by norm_num) (by norm_num)
    have hsinx : |sin (localAngle x) * x| ≤ 1 / 5 := by
      rw [abs_mul]
      simpa using mul_le_mul (abs_sin_le_one (localAngle x)) (abs_le.mpr hx')
        (abs_nonneg x) (by norm_num)
    linarith only [hcsd, (abs_le.mp hsinx).1]
  have heq : deriv localCos =ᶠ[nhds x]
      (fun y => -(cStar * sin (localAngle y)) / √(1 - y ^ 2)) := by
    filter_upwards [lt_mem_nhds h₁, gt_mem_nhds h₂] with y hy₁ hy₂
    exact (localCos_deriv hy₁ hy₂).deriv
  have hx2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1 <;> ring
  have hd' := (hasDerivAt_sqrt (show 1 - x ^ 2 ≠ 0 by linarith)).comp x hx2
  have hn' := ((localAngle_deriv h₁ h₂).sin.const_mul cStar).neg
  have hquot := (hn'.div hd' hd₀.ne').deriv
  change deriv (fun y => -(cStar * sin (localAngle y)) / √(1 - y ^ 2)) x = _ at hquot
  rw [Function.iterate_succ_apply', Function.iterate_one, heq.deriv_eq, hquot]
  refine div_neg_of_neg_of_pos ?_ (sq_pos_of_pos hd₀)
  change -(cStar * (cos (localAngle x) * (cStar / d))) * d -
    -(cStar * sin (localAngle x)) * (1 / (2 * d) * (-2 * x)) < 0
  rw [show -(cStar * (cos (localAngle x) * (cStar / d))) * d -
      -(cStar * sin (localAngle x)) * (1 / (2 * d) * (-2 * x)) =
        -cStar * (cStar * localCos x * d + sin (localAngle x) * x) / d by
    unfold localCos
    field_simp [hd₀.ne']
    <;> ring]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hc₀) hnum) hd₀

private theorem quarterCos_le_tangent {h : ℝ} (hh : |h| ≤ 1 / 5) :
    cos (cStar * (π / 2 + arcsin h)) ≤ 1 / √3 - cStar * √(2 / 3) * h := by
  have hcπ : cStar * (π / 2) = quarterError := by
    unfold cStar
    field_simp [pi_pos.ne'] <;> ring
  have ha : cStar * (π / 2 + arcsin h) = localAngle h := by
    rw [localAngle, mul_add, hcπ]
  rw [ha]
  change localCos h ≤ _
  have hc := localCos_strictConcave.concaveOn
  have hh' := abs_le.mp hh
  have hzero : (0 : ℝ) ∈ Set.Icc (-(1 / 5 : ℝ)) (1 / 5) := by norm_num
  have hd : HasDerivAt localCos (-(cStar * √(2 / 3))) 0 := by
    simpa only [pow_two, mul_zero, sub_zero, sqrt_one, div_one, localCos_at_zero.2] using
      (localCos_deriv (x := 0) (by norm_num) (by norm_num))
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · have hs := hc.le_slope_of_hasDerivAt hh' hzero hneg hd
    rw [slope_def_field, zero_sub, le_div_iff₀ (neg_pos.mpr hneg)] at hs
    linarith only [hs, localCos_at_zero.1]
  · simp [localCos_at_zero.1]
  · have hs := hc.slope_le_of_hasDerivAt hzero hh' hpos hd
    rw [slope_def_field, sub_zero, div_le_iff₀ hpos] at hs
    linarith only [hs, localCos_at_zero.1]

private theorem localMargin {P Q E h S : ℝ}
    (hP : P ∈ Set.Icc 0 (3 / 50)) (hQ : Q ∈ Set.Icc 0 (3 / 50)) (hE : 0 ≤ E)
    (hh : |h| ≤ 1 / 5)
    (hdef : E / 3 + (51 / 20) * P ^ 2 / 6 -
      ((13 / 5) * Q ^ 2 + 25 * (3 / 50) ^ 2 * E) / 3 ≤ h)
    (hscore : 1 / √3 + Q / √6 - (√3 / 12) * P ^ 2 - (2 / 5) * P ^ 3 -
      3 * P ^ 4 - (627 / 100) * (3 / 50) * Q - 2 * (3 / 50) * E ≤ S) :
    cos (cStar * (π / 2 + arcsin h)) + Q / 200 + (3 / 100) * (P ^ 2 + E) ≤ S := by
  let k := cStar * √(2 / 3)
  have hk₁ : (496 / 1000 : ℝ) ≤ k := cStar_bounds.2.2.1.le
  have hk₂ : k ≤ (1 / 2 : ℝ) := cStar_bounds.2.2.2.le
  have hk : 0 ≤ k := by linarith
  have hq₆ : (408 / 1000 : ℝ) * Q ≤ Q / √6 := by
    have hs : √(6 : ℝ) < 245 / 100 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hi : (408 / 1000 : ℝ) ≤ 1 / √6 := (le_div_iff₀ (by positivity)).mpr
      (by linarith)
    simpa only [mul_comm Q, one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hi hQ.1
  have hp₃ : P ^ 3 ≤ (3 / 50) * P ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hP.2 (sq_nonneg P)]
  have hp₄ : P ^ 4 ≤ (3 / 50) ^ 2 * P ^ 2 := by
    have hs := pow_le_pow_left₀ hP.1 hP.2 2
    nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg P)]
  have hq₂ : Q ^ 2 ≤ (3 / 50) * Q := by
    nlinarith only [mul_le_mul_of_nonneg_right hQ.2 hQ.1]
  have ha : √(3 : ℝ) / 12 ≤ 145 / 1000 := by
    linarith [(sqrt_lt' (by norm_num : (0 : ℝ) < 174 / 100)).mpr (by norm_num : (3 : ℝ) < (174 / 100) ^ 2)]
  have hthreshold := quarterCos_le_tangent hh
  change cos (cStar * (π / 2 + arcsin h)) ≤ 1 / √3 - k * h at hthreshold
  have hkdef := mul_le_mul_of_nonneg_left hdef hk
  -- Bound all positive and negative contributions before applying the defect estimate.
  have hpMargin : (3 / 100 : ℝ) * P ^ 2 ≤
      (k * (51 / 20) / 6 - √3 / 12) * P ^ 2 - (2 / 5) * P ^ 3 - 3 * P ^ 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hk₁ (sq_nonneg P),
      mul_le_mul_of_nonneg_right ha (sq_nonneg P), hp₃, hp₄, sq_nonneg P]
  have hqMargin : Q / 200 ≤ Q / √6 - (627 / 100) * (3 / 50) * Q -
      (13 / 5) * k * Q ^ 2 / 3 := by
    nlinarith only [hq₆, hq₂, mul_le_mul_of_nonneg_right hk₂ (sq_nonneg Q), hQ.1]
  have heMargin : (3 / 100 : ℝ) * E ≤ k * E / 3 -
      k * 25 * (3 / 50) ^ 2 * E / 3 - 2 * (3 / 50) * E := by
    nlinarith only [mul_le_mul_of_nonneg_right hk₁ hE,
      mul_le_mul_of_nonneg_right hk₂ hE, hE]
  nlinarith only [hthreshold, hscore, hkdef, hpMargin, hqMargin, heMargin]

def localDefectParam (A : Fin 3 → U) (η : Fin 3 → ℝ) : ℝ :=
  max (max (η 0) (max (η 1) (η 2))) (-((A 0 * A 1 * A 2 : U) : ℍ[ℝ]).re)

private theorem hubMaxDefect_eq_asin (A : Fin 3 → U) (η : Fin 3 → ℝ)
    (hη : ∀ j, (A j : ℍ[ℝ]).re = -η j) :
    hubMaxDefect A = π / 2 + arcsin (localDefectParam A η) := by
  have hd (j : Fin 3) : roundDist 1 (A j) = π / 2 + arcsin (η j) := by
    rw [show roundDist 1 (A j) = arccos (A j : ℍ[ℝ]).re by
      simp [dist_trace, ← Unitary.star_eq_inv], hη, arccos_eq_pi_div_two_sub_arcsin,
      arcsin_neg, sub_neg_eq_add]
  have hf (a b : ℝ) :
      max (π / 2 + arcsin a) (π / 2 + arcsin b) = π / 2 + arcsin (max a b) := by
    rcases le_total a b with h | h
    · have h' : π / 2 + arcsin a ≤ π / 2 + arcsin b := by
        linarith only [arcsin_le_arcsin h]
      rw [max_eq_right h, max_eq_right h']
    · have h' : π / 2 + arcsin b ≤ π / 2 + arcsin a := by
        linarith only [arcsin_le_arcsin h]
      rw [max_eq_left h, max_eq_left h']
  unfold hubMaxDefect localDefectParam
  rw [hd, hd, hd, dist_trace]
  simp only [inv_one, mul_one, arccos_eq_pi_div_two_sub_arcsin, sub_eq_add_neg, ← arcsin_neg]
  rw [hf, hf, hf]

private def imagDot (γ : Fin 3 → ℝ) (w : Fin 3 → ℂ) (i j : Fin 3) : ℝ :=
  γ i * γ j + (w i).re * (w j).re + (w i).im * (w j).im

private theorem transverse_area (p q : ℂ) (j : Fin 3) :
    (star (transverse p q j) * transverse p q (j + 1)).im =
      √3 / 2 * (‖p‖ ^ 2 - ‖q‖ ^ 2) := by
  fin_cases j <;>
    norm_num [transverse, rimPhase, zeta, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sq_norm, Complex.normSq_apply, Fin.add_def] <;> ring

private theorem rimPhase_sub_norm (j : Fin 3) :
    ‖rimPhase j - rimPhase (j + 1)‖ = √3 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Complex.sq_norm, Complex.normSq_apply]
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases j <;> norm_num [rimPhase, zeta, Complex.star_def, Complex.sub_re, Complex.sub_im,
    Fin.add_def] <;> nlinarith only [hs]

/-- The scalar triple product reduces to the three cyclic transverse areas. -/
private theorem trace_rim (A : Fin 3 → U) (η γ : Fin 3 → ℝ) (p q : ℂ)
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j)) :
    let w := transverse p q
    ((A 0 * A 1 * A 2 : U) : ℍ[ℝ]).re =
      -η 0 * η 1 * η 2 + η 0 * imagDot γ w 1 2 + η 1 * imagDot γ w 2 0 +
        η 2 * imagDot γ w 0 1 -
      (√3 / 2 * (γ 0 + γ 1 + γ 2)) * (‖p‖ ^ 2 - ‖q‖ ^ 2) := by
  dsimp only
  have ha := transverse_area p q 0
  have hb := transverse_area p q 1
  have hc := transverse_area p q 2
  simp only [show (0 : Fin 3) + 1 = 1 by decide, show (1 : Fin 3) + 1 = 2 by decide,
    show (2 : Fin 3) + 1 = 0 by decide, Complex.star_def, Complex.mul_im,
    Complex.conj_re, Complex.conj_im] at ha hb hc
  simp only [Submonoid.coe_mul, hA, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, quatPair, imagDot]
  linear_combination -γ 2 * ha - γ 0 * hb - γ 1 * hc

private theorem quarterLocal_defectLower (A : Fin 3 → U) (η γ : Fin 3 → ℝ) (p q : ℂ)
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j))
    (hγ : ∀ j, 0 < γ j)
    (hP : ‖p‖ ≤ localR) (hQ : ‖q‖ ≤ localR) (hE : etaMax η ≤ localR) :
    |localDefectParam A η| < 1 / 5 ∧
      etaMax η / 3 + (51 / 20) * ‖p‖ ^ 2 / 6 -
        ((13 / 5) * ‖q‖ ^ 2 + 25 * localR ^ 2 * etaMax η) / 3 ≤ localDefectParam A η := by
  let P := ‖p‖
  let Q := ‖q‖
  let E := etaMax η
  let T := ((A 0 * A 1 * A 2 : U) : ℍ[ℝ]).re
  let m := localDefectParam A η
  let w := transverse p q
  let K := √3 / 2 * (γ 0 + γ 1 + γ 2)
  change P ≤ 3 / 50 at hP
  change Q ≤ 3 / 50 at hQ
  change E ≤ 3 / 50 at hE
  change |m| < 1 / 5 ∧
    E / 3 + (51 / 20) * P ^ 2 / 6 -
      ((13 / 5) * Q ^ 2 + 25 * (3 / 50) ^ 2 * E) / 3 ≤ m
  have hE0 : 0 ≤ E := local_eta_nonneg η
  have hηE (j : Fin 3) : |η j| ≤ E := local_abs_eta η j
  have hηr (j : Fin 3) : |η j| ≤ 3 / 50 := (hηE j).trans hE
  have hw (j : Fin 3) : ‖w j‖ ≤ P + Q := by
    simpa only [w, transverse, norm_mul, Complex.star_def, Complex.norm_conj, local_phase_norm,
      mul_one] using norm_add_le (p * star (rimPhase j)) (q * rimPhase j)
  have hnorm (j : Fin 3) : η j ^ 2 + γ j ^ 2 + ‖w j‖ ^ 2 = 1 := by
    have hn : Quaternion.normSq (A j : ℍ[ℝ]) = 1 := by
      rw [normSq_eq_norm_mul_self, unit_norm, one_mul]
    rw [hA j, local_normSq_pair, local_sq_complex, neg_sq] at hn
    exact hn
  have hηsq (j : Fin 3) : η j ^ 2 ≤ (3 / 50 : ℝ) ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 50)]; exact hηr j)
  have hγlo (j : Fin 3) : (99 / 100 : ℝ) < γ j := by
    apply (sq_lt_sq₀ (by norm_num) (hγ j).le).mp
    have hws := pow_le_pow_left₀ (norm_nonneg (w j))
      (show ‖w j‖ ≤ 6 / 50 by linarith [hw j]) 2
    nlinarith only [hnorm j, hws, hηsq j]
  have hγhi (j : Fin 3) : γ j ≤ 1 :=
    (sq_le_sq₀ (hγ j).le zero_le_one).mp
      (by nlinarith only [hnorm j, sq_nonneg (η j), sq_nonneg ‖w j‖])
  have hKlo : (51 / 20 : ℝ) ≤ K := by
    have hs : (173 / 100 : ℝ) < √3 := lt_sqrt_of_sq_lt (by norm_num)
    have ha : (297 / 100 : ℝ) < γ 0 + γ 1 + γ 2 :=
      by linarith [hγlo 0, hγlo 1, hγlo 2]
    have hm := mul_lt_mul'' hs ha (by norm_num) (by norm_num)
    unfold K
    linarith only [hm]
  have hKhi : K ≤ (13 / 5 : ℝ) := by
    have hs : √(3 : ℝ) ≤ 26 / 15 := sqrt_le_iff.mpr (by norm_num)
    have ha : γ 0 + γ 1 + γ 2 ≤ (3 : ℝ) :=
      by linarith [hγhi 0, hγhi 1, hγhi 2]
    have hm := mul_le_mul hs ha (by linarith [hγ 0, hγ 1, hγ 2]) (by norm_num)
    unfold K
    linarith only [hm]
  have hdist (j : Fin 3) : ‖w j - w (j + 1)‖ ≤ √3 * (P + Q) := by
    calc
      _ = ‖p * star (rimPhase j - rimPhase (j + 1)) +
        q * (rimPhase j - rimPhase (j + 1))‖ := by
          congr 1
          simp only [w, transverse, star_sub]
          ring
      _ ≤ _ := by
        simpa only [norm_mul, Complex.star_def, Complex.norm_conj, rimPhase_sub_norm,
          ← add_mul, mul_comm (√3)] using (norm_add_le
          (p * star (rimPhase j - rimPhase (j + 1))) (q * (rimPhase j - rimPhase (j + 1))))
  have hdot (j : Fin 3) : |imagDot γ w j (j + 1) - 1| ≤ 8 * (3 / 50) ^ 2 := by
    let i := j + 1
    have hΔw : ‖w j - w i‖ ^ 2 ≤ 12 * (3 / 50) ^ 2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg (w j - w i))
        ((hdist j).trans (mul_le_mul_of_nonneg_left
          (show P + Q ≤ 6 / 50 by linarith) (sqrt_nonneg _))) 2
      rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hs
      linarith only [hs]
    have hΔγ : (γ j - γ i) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
      exact abs_le.mpr ⟨by linarith [hγlo j, hγhi i], by linarith [hγlo i, hγhi j]⟩)
    -- The loss of the axial dot product is half the sum of squared differences.
    have heq : 2 * (1 - imagDot γ w j i) = η j ^ 2 + η i ^ 2 +
        (γ j - γ i) ^ 2 + ‖w j - w i‖ ^ 2 := by
      have hj := hnorm j
      have hi := hnorm i
      simp only [imagDot, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im] at hj hi ⊢
      nlinarith only [hj, hi]
    change |imagDot γ w j i - 1| ≤ _
    exact abs_le.mpr ⟨by linarith only [heq, hηsq j, hηsq i, hΔγ, hΔw],
      by linarith only [heq, sq_nonneg (η j), sq_nonneg (η i),
        sq_nonneg (γ j - γ i), sq_nonneg ‖w j - w i‖]⟩
  have hdot₁ (j : Fin 3) : |imagDot γ w j (j + 1)| ≤ 1 := by
    have hsum : 0 ≤ (γ j + γ (j + 1)) ^ 2 + ‖w j + w (j + 1)‖ ^ 2 := by positivity
    have hdiff : 0 ≤ (γ j - γ (j + 1)) ^ 2 + ‖w j - w (j + 1)‖ ^ 2 := by positivity
    have hj := hnorm j
    have hi := hnorm (j + 1)
    simp only [imagDot, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] at hsum hdiff hj hi ⊢
    exact abs_le.mpr ⟨by nlinarith only [hsum, hj, hi, sq_nonneg (η j), sq_nonneg (η (j + 1))],
      by nlinarith only [hdiff, hj, hi, sq_nonneg (η j), sq_nonneg (η (j + 1))]⟩
  have hprod : |η 0 * η 1 * η 2| ≤ (3 / 50) ^ 2 * E := by
    rw [abs_mul, abs_mul, pow_two]
    exact mul_le_mul (mul_le_mul (hηr 0) (hηr 1) (abs_nonneg _) (by norm_num))
      (hηE 2) (abs_nonneg _) (by norm_num)
  have hpair (j : Fin 3) :
      |η j * (imagDot γ w (j + 1) (j + 1 + 1) - 1)| ≤ E * (8 * (3 / 50) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul (hηE j) (hdot (j + 1)) (abs_nonneg _) hE0
  have hpair₁ (j : Fin 3) : |η j * imagDot γ w (j + 1) (j + 1 + 1)| ≤ 3 / 50 := by
    rw [abs_mul, ← mul_one (3 / 50 : ℝ)]
    exact mul_le_mul (hηr j) (hdot₁ (j + 1)) (abs_nonneg _) (by norm_num)
  have htr := trace_rim A η γ p q hA
  change T = -η 0 * η 1 * η 2 + η 0 * imagDot γ w 1 2 + η 1 * imagDot γ w 2 0 +
    η 2 * imagDot γ w 0 1 - K * (P ^ 2 - Q ^ 2) at htr
  have ht : -η 0 - η 1 - η 2 + (51 / 20) * P ^ 2 -
      ((13 / 5) * Q ^ 2 + 25 * (3 / 50) ^ 2 * E) ≤ -T := by
    have h₀ := (abs_le.mp (hpair 0)).2
    have h₁ := (abs_le.mp (hpair 1)).2
    have h₂ := (abs_le.mp (hpair 2)).2
    simp only [show (0 : Fin 3) + 1 = 1 by decide, show (1 : Fin 3) + 1 = 2 by decide,
      show (2 : Fin 3) + 1 = 0 by decide] at h₀ h₁ h₂
    nlinarith only [htr, (abs_le.mp hprod).1, h₀, h₁, h₂,
      mul_le_mul_of_nonneg_right hKlo (sq_nonneg P), mul_le_mul_of_nonneg_right hKhi (sq_nonneg Q)]
  have htAbs : |T| < 1 / 5 := by
    have hprod' := hprod.trans (mul_le_mul_of_nonneg_left hE (sq_nonneg (3 / 50 : ℝ)))
    have h₀ := abs_le.mp (hpair₁ 0)
    have h₁ := abs_le.mp (hpair₁ 1)
    have h₂ := abs_le.mp (hpair₁ 2)
    simp only [show (0 : Fin 3) + 1 = 1 by decide, show (1 : Fin 3) + 1 = 2 by decide,
      show (2 : Fin 3) + 1 = 0 by decide] at h₀ h₁ h₂
    have ha (x : ℝ) (hx : 0 ≤ x) (hr : x ≤ 3 / 50) :
        0 ≤ K * x ^ 2 ∧ K * x ^ 2 ≤ (13 / 5) * (3 / 50) ^ 2 := by
      have hk : 0 ≤ K := by linarith only [hKlo]
      exact ⟨mul_nonneg hk (sq_nonneg _), mul_le_mul hKhi (pow_le_pow_left₀ hx hr 2) (sq_nonneg _) (by norm_num)⟩
    have hp := ha P (norm_nonneg _) hP
    have hq := ha Q (norm_nonneg _) hQ
    exact abs_lt.mpr ⟨by nlinarith only [htr, (abs_le.mp hprod').2, h₀.1, h₁.1, h₂.1, hp.2, hq.1],
      by nlinarith only [htr, (abs_le.mp hprod').1, h₀.2, h₁.2, h₂.2, hp.1, hq.2]⟩
  have hm (j : Fin 3) : η j ≤ m := by
    refine le_max_of_le_left ?_
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hmt : -T ≤ m := le_max_right _ _
  constructor
  · refine abs_lt.mpr ⟨by linarith only [(abs_le.mp (hηr 0)).1, hm 0], ?_⟩
    unfold m localDefectParam
    simp only [max_lt_iff]
    exact ⟨⟨by linarith only [(abs_le.mp (hηr 0)).2],
      by linarith only [(abs_le.mp (hηr 1)).2],
      by linarith only [(abs_le.mp (hηr 2)).2]⟩, by linarith only [(abs_lt.mp htAbs).1]⟩
  · have hex : ∃ j : Fin 3, E = |η j| := by
      rcases max_choice |η 0| (max |η 1| |η 2|) with h | h
      · exact ⟨0, h⟩
      · rcases max_choice |η 1| |η 2| with h' | h'
        · exact ⟨1, h.trans h'⟩
        · exact ⟨2, h.trans h'⟩
    obtain ⟨j, hj⟩ := hex
    rcases le_total 0 (η j) with hp | hn
    · rw [abs_of_nonneg hp] at hj
      have hem : E ≤ m := hj.le.trans (hm j)
      -- The positive extreme receives weight 1/3 and the four-face average weight 2/3.
      nlinarith only [hem, hm 0, hm 1, hm 2, ht, hmt, hE0, sq_nonneg Q]
    · rw [abs_of_nonpos hn] at hj
      fin_cases j
      · change E = -η 0 at hj
        nlinarith only [hj, hm 1, hm 2, ht, hmt, sq_nonneg P]
      · change E = -η 1 at hj
        nlinarith only [hj, hm 0, hm 2, ht, hmt, sq_nonneg P]
      · change E = -η 2 at hj
        nlinarith only [hj, hm 0, hm 1, ht, hmt, sq_nonneg P]

/-- Coordinate laws and transport on the hub-gauged quotient, with its exact face maximum. -/
structure LocalGeometryLaws (e : (Fin 3 → U) → ℝ) : Prop where
  re_comm : ∀ (x y : ℍ[ℝ]),
    (x * y).re = (y * x).re
  re_cyclic : ∀ (x y z : ℍ[ℝ]),
    (x * y * z).re = (y * z * x).re
  dist_trace : ∀ (a b : U),
    roundDist a b = arccos (((a * b⁻¹ : U) : ℍ[ℝ]).re)
  hub_reverse : ∀ (A : Fin 3 → U) (i j : Fin 4),
    hubGaugedGains A j i = (hubGaugedGains A i j)⁻¹
  hub_faces : ∀ (A : Fin 3 → U),
    DefectLE (hubGaugedGains A) (e A) ∧
    ∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      roundDist (hubGaugedGains A i j * hubGaugedGains A j k)
        (hubGaugedGains A i k) = e A
  conj_mul : ∀ (C a b : U),
    conjugate C (a * b) = conjugate C a * conjugate C b
  conj_inv : ∀ (C a : U),
    conjugate C a⁻¹ = (conjugate C a)⁻¹
  conj_cancel : ∀ (C a : U),
    conjugate C⁻¹ (conjugate C a) = a
  conj_inner : ∀ (C a b : U),
    ⟪(conjugate C a : ℍ[ℝ]), (conjugate C b : ℍ[ℝ])⟫_ℝ =
      ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ
  conjugate_hub : ∀ (C : U) (A : Fin 3 → U) (i j : Fin 4),
    hubGaugedGains (conjugate C ∘ A) i j = conjugate C (hubGaugedGains A i j)
  conjugate_hubMaxDefect : ∀ (C : U) (A : Fin 3 → U),
    e (conjugate C ∘ A) = e A
  conjugate_fits : ∀ (C : U) (g : Fin 4 → Fin 4 → U) (φ : Fin 4 → U) (R : ℝ),
    Fits (fun i j => conjugate C (g i j)) (conjugate C ∘ φ) R ↔ Fits g φ R
  score_ge_iff : ∀ {a b : U} {R : ℝ} (hR : R ∈ Set.Icc 0 π),
    roundDist a b ≤ R ↔ cos R ≤ ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ
  strict_fit_of_scores : ∀ {g : Fin 4 → Fin 4 → U} {φ : Fin 4 → U} {R δ : ℝ}
    (hR : R ∈ Set.Icc 0 π) (hd : 0 < δ)
    (hs : ∀ i j, i ≠ j → cos R + δ ≤
      ⟪(g i j : ℍ[ℝ]), (↑((φ i)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ),
    ∃ s < R, Fits g φ s
  local_abs_eta : ∀ (η : Fin 3 → ℝ) (j : Fin 3),
    |η j| ≤ etaMax η
  local_eta_nonneg : ∀ (η : Fin 3 → ℝ),
    0 ≤ etaMax η
  local_normSq_pair : ∀ (z h : ℂ),
    normSq (quatPair z h) = ‖z‖ ^ 2 + ‖h‖ ^ 2
  local_sq_complex : ∀ (x y : ℝ),
    ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2
  local_norm_pair : ∀ (z h : ℂ),
    ‖quatPair z h‖ ^ 2 = ‖z‖ ^ 2 + ‖h‖ ^ 2
  local_phase_norm : ∀ (j : Fin 3),
    ‖rimPhase j‖ = 1
  local_pair_sub : ∀ (z h z' h' : ℂ),
    quatPair z h - quatPair z' h' = quatPair (z - z') (h - h')

/-- The face maximum, quaternion coordinates, and unitary transport agree on the hub gauge. -/
theorem local_geometry : LocalGeometryLaws hubMaxDefect where
  re_comm := re_comm
  re_cyclic := re_cyclic
  dist_trace := dist_trace
  hub_reverse := hub_reverse
  hub_faces := hub_faces
  conj_mul := conj_mul
  conj_inv := conj_inv
  conj_cancel := conj_cancel
  conj_inner := conj_inner
  conjugate_hub := conjugate_hub
  conjugate_hubMaxDefect := conjugate_hubMaxDefect
  conjugate_fits := conjugate_fits
  score_ge_iff := score_ge_iff
  strict_fit_of_scores := strict_fit_of_scores
  local_abs_eta := local_abs_eta
  local_eta_nonneg := local_eta_nonneg
  local_normSq_pair := local_normSq_pair
  local_sq_complex := local_sq_complex
  local_norm_pair := local_norm_pair
  local_phase_norm := local_phase_norm
  local_pair_sub := local_pair_sub

/-- The exact defect, the trace bounds and the resulting numerical score comparison. -/
structure LocalDefectEstimates (A : Fin 3 → U) (η : Fin 3 → ℝ) (p q : ℂ) (e : ℝ) : Prop where
  exact_defect : e = π / 2 + arcsin (localDefectParam A η)
  trace_range : |localDefectParam A η| < 1 / 5
  trace_lower : etaMax η / 3 + (51 / 20) * ‖p‖ ^ 2 / 6 -
    ((13 / 5) * ‖q‖ ^ 2 + 25 * localR ^ 2 * etaMax η) / 3 ≤ localDefectParam A η
  fit_radius_range : cStar * e ∈ Set.Icc 0 π
  score_comparison : ∀ S : ℝ,
    1 / √3 + ‖q‖ / √6 - (√3 / 12) * ‖p‖ ^ 2 - (2 / 5) * ‖p‖ ^ 3 -
      3 * ‖p‖ ^ 4 - (627 / 100) * localR * ‖q‖ - 2 * localR * etaMax η ≤ S →
    cos (cStar * e) + ‖q‖ / 200 + (3 / 100) * (‖p‖ ^ 2 + etaMax η) ≤ S

/-- The cyclic rim trace and the three spoke defects yield the strict score margin. -/
theorem local_defect_estimates (A : Fin 3 → U) (p q : ℂ) (η γ : Fin 3 → ℝ)
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j))
    (hγ : ∀ j, 0 < γ j)
    (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (hη : etaMax η ≤ localR) :
    LocalDefectEstimates A η p q (hubMaxDefect A) := by
  have he := hubMaxDefect_eq_asin A η (fun j => congrArg (fun x : ℍ[ℝ] => x.re) (hA j))
  obtain ⟨hrange, htrace⟩ := quarterLocal_defectLower A η γ p q hA hγ hp hq hη
  refine ⟨he, hrange, htrace, ?_, ?_⟩
  · have hc₀ : 0 ≤ cStar := by linarith [cStar_bounds.1]
    have hc₁ : cStar ≤ 1 := by linarith [cStar_bounds.2.1]
    have he₀ : 0 ≤ hubMaxDefect A := (arccos_nonneg _).trans (le_max_right _ _)
    have he₁ : hubMaxDefect A ≤ π := by
      unfold hubMaxDefect roundDist
      simp only [max_le_iff]
      exact ⟨⟨arccos_le_pi _, arccos_le_pi _, arccos_le_pi _⟩, arccos_le_pi _⟩
    exact ⟨mul_nonneg hc₀ he₀, (mul_le_of_le_one_left he₀ hc₁).trans he₁⟩
  · intro S hs
    rw [he]
    exact localMargin ⟨norm_nonneg _, hp⟩ ⟨norm_nonneg _, hq⟩ (local_eta_nonneg η)
      hrange.le htrace hs

end RoundQuaternionLocalSharpness
