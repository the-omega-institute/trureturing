/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict quantitative sharpness and an angular neighborhood for round quaternion reconstruction on four vertices. -/

import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! The cyclic quarter turn has a quantitative strict fit gap under transverse and
axial perturbations. The angular chart enters this regime by weighted variance. -/

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

private def asUnit (a : ℍ[ℝ]) (ha : normSq a = 1) : U :=
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
  have t (i j k : Fin 4) :
      roundDist (g i j * g j k) (g i k) =
        arccos (((g i j * g j k * g k i : U) : ℍ[ℝ]).re) := by
    rw [dist_trace, hub_reverse A i k]
  have cycle (i j k : Fin 4) :
      roundDist (g j k * g k i) (g j i) = roundDist (g i j * g j k) (g i k) := by
    rw [t, t, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    rw [re_cyclic (g i j : ℍ[ℝ])]
  have reverse (i j k : Fin 4) :
      roundDist (g k j * g j i) (g k i) = roundDist (g i j * g j k) (g i k) := by
    rw [t, t, hub_reverse A j k, hub_reverse A i j, hub_reverse A k i]
    rw [← mul_inv_rev, ← mul_inv_rev, ← Unitary.star_eq_inv, Unitary.coe_star, Quaternion.re_star]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    rw [re_cyclic (g k i : ℍ[ℝ])]
  have exactFace (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      let e := roundDist (g i j * g j k) (g i k)
      e = a ∨ e = b ∨ e = c ∨ e = d := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim | skip
    all_goals dsimp only
    all_goals first
      | exact Or.inl h01 | exact Or.inr (Or.inl h02)
      | exact Or.inr (Or.inr (Or.inl h03)) | exact Or.inr (Or.inr (Or.inr h12))
      | (rw [cycle]; exact Or.inl h01 <|> exact Or.inr (Or.inl h02) <|>
           exact Or.inr (Or.inr (Or.inl h03)) <|> exact Or.inr (Or.inr (Or.inr h12)))
      | (rw [cycle, cycle]; exact Or.inl h01 <|> exact Or.inr (Or.inl h02) <|>
           exact Or.inr (Or.inr (Or.inl h03)) <|> exact Or.inr (Or.inr (Or.inr h12)))
      | (rw [reverse]; exact Or.inl h01 <|> exact Or.inr (Or.inl h02) <|>
           exact Or.inr (Or.inr (Or.inl h03)) <|> exact Or.inr (Or.inr (Or.inr h12)))
      | (rw [reverse, cycle]; exact Or.inl h01 <|> exact Or.inr (Or.inl h02) <|>
           exact Or.inr (Or.inr (Or.inl h03)) <|> exact Or.inr (Or.inr (Or.inr h12)))
      | (rw [reverse, cycle, cycle]; exact Or.inl h01 <|> exact Or.inr (Or.inl h02) <|>
           exact Or.inr (Or.inr (Or.inl h03)) <|> exact Or.inr (Or.inr (Or.inr h12)))
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


private def conjugate (C a : U) : U := C * a * C⁻¹

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
  have ha := abs_le.mp (by simpa only [unit_norm, mul_one] using
    abs_real_inner_le_norm (a : ℍ[ℝ]) (b : ℍ[ℝ]))
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

private def rimPhase (j : Fin 3) : ℂ := ![1, star zeta, zeta] j

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
  fin_cases j <;> simp [rimPhase, Complex.star_def, hz, Complex.norm_conj]

private theorem local_pair_sub (z h z' h' : ℂ) :
    quatPair z h - quatPair z' h' = quatPair (z - z') (h - h') := by
  ext <;> rfl

private def localT : ℝ := Real.sqrt 3 / 3
private def localS : ℝ := Real.sqrt 2 * Real.sqrt 3 / 3
private def localAlpha : ℝ := Real.sqrt 3 / 12
private def localLinear : ℝ := Real.sqrt 2 * Real.sqrt 3 / 6
private def localInvS : ℝ := Real.sqrt 2 * Real.sqrt 3 / 4

private theorem local_constant_squares :
    localT ^ 2 = 1/3 ∧ localS ^ 2 = 2/3 ∧ localAlpha ^ 2 = 1/48 ∧
      localLinear ^ 2 = 1/6 ∧ localInvS ^ 2 = 3/8 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num [localT, localS, localAlpha, localLinear, localInvS, div_pow, mul_pow, h2, h3]

private theorem local_constant_values :
    localT = 1 / Real.sqrt 3 ∧ localS = Real.sqrt (2/3) ∧ localLinear = 1 / Real.sqrt 6 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · apply (eq_div_iff (by positivity : Real.sqrt 3 ≠ 0)).2
    unfold localT
    nlinarith
  · have hs : (Real.sqrt (2/3)) ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
    nlinarith [local_constant_squares.2.1, show 0 ≤ localS by unfold localS; positivity,
      Real.sqrt_nonneg (2/3)]
  · apply (eq_div_iff (by positivity : Real.sqrt 6 ≠ 0)).2
    have h := local_constant_squares.2.2.2.1
    have hsq : (localLinear * Real.sqrt 6)^2 = 1 := by rw [mul_pow, h, h6]; norm_num
    nlinarith [show 0 ≤ localLinear * Real.sqrt 6 by unfold localLinear; positivity]

private theorem local_constant_bounds :
    577/1000 < localT ∧ localT < 5774/10000 ∧ 815/1000 < localS ∧ localS < 817/1000 ∧
    0 < localAlpha ∧ localAlpha < 145/1000 ∧ 408/1000 < localLinear ∧
    localLinear < 409/1000 := by
  obtain ⟨hT, hS, hα, hL, _⟩ := local_constant_squares
  have ht : 0 < localT := by unfold localT; positivity
  have hs : 0 < localS := by unfold localS; positivity
  have ha : 0 < localAlpha := by unfold localAlpha; positivity
  have hl : 0 < localLinear := by unfold localLinear; positivity
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ha,
    by nlinarith, by nlinarith, by nlinarith⟩

private def rimPrev (j : Fin 3) : Fin 3 := j - 1
private def rimNext (j : Fin 3) : Fin 3 := j + 1

private def localB (p : ℂ) (j : Fin 3) : ℝ :=
  localLinear * (p * rimPhase (rimPrev j)).re
private def localTau (p : ℂ) (j : Fin 3) : ℝ := Real.sqrt 3 * localB p j

private def localF (p : ℂ) (j : Fin 3) : ℝ :=
  let x := p.re
  let y := p.im
  ![Real.sqrt 3 * (x ^ 2 - y ^ 2) / 96 + x*y/16,
    Real.sqrt 3 * (x ^ 2 - y ^ 2) / 96 - x*y/16,
    -Real.sqrt 3 * (x ^ 2 - y ^ 2) / 48] j

private def localPsi (p : ℂ) (j : Fin 3) : ℝ := localF p j - localF p (rimPrev j)
private def localFibre (p : ℂ) (j : Fin 3) : ℝ := localS * (localTau p j + localPsi p j)
private def localReal (p q : ℂ) : ℝ := localT + localLinear * ‖q‖ - localAlpha * ‖p‖^2
private def localRadicand (p q : ℂ) (j : Fin 3) : ℝ :=
  1 - localReal p q ^ 2 - localB p j ^ 2 - localFibre p j ^ 2

private def localRim (p q : ℂ) (j : Fin 3) : ℍ[ℝ] :=
  quatPair ⟨localReal p q, localB p j⟩
    (rimPhase j * ⟨Real.sqrt (localRadicand p q j), localFibre p j⟩)

private theorem local_rim_unit (p q : ℂ) (j : Fin 3) (h : 0 ≤ localRadicand p q j) :
    normSq (localRim p q j) = 1 := by
  simp only [localRim, local_normSq_pair, norm_mul, local_phase_norm, one_mul,
    local_sq_complex, Real.sq_sqrt h, localRadicand]
  ring

private def localUnitRim (p q : ℂ) (j : Fin 3) : U :=
  if h : 0 ≤ localRadicand p q j then asUnit (localRim p q j) (local_rim_unit p q j h)
  else 1

/-- The hub potential is \(1\). The rim potentials use the phased transverse coordinates. -/
def quarterLocalPotential (p q : ℂ) : Fin 4 → U :=
  ![1, localUnitRim p q 0, localUnitRim p q 1, localUnitRim p q 2]

private theorem local_b_bound (p : ℂ) (j : Fin 3) : |localB p j| ≤ localLinear * ‖p‖ := by
  have h := Complex.abs_re_le_norm (p * rimPhase (rimPrev j))
  rw [norm_mul, local_phase_norm, mul_one] at h
  have hl : 0 ≤ localLinear := by unfold localLinear; positivity
  simpa only [localB, abs_mul, abs_of_nonneg hl] using mul_le_mul_of_nonneg_left h hl

private theorem local_psi_bound (p : ℂ) (j : Fin 3) : |localPsi p j| ≤ ‖p‖ ^ 2 / 16 := by
  let x := p.re
  let y := p.im
  let a := x ^ 2 - y ^ 2
  let b := 2*x*y
  have h : a ^ 2 + b ^ 2 = ‖p‖ ^ 4 := by
    rw [show ‖p‖ ^ 4 = (‖p‖ ^ 2) ^ 2 by ring, Complex.sq_norm, Complex.normSq_apply]
    dsimp [a, b, x, y]
    ring
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have bound (c d : ℝ) (hc : c ^ 2 + d ^ 2 = (1/16 : ℝ) ^ 2) :
      |c*a + d*b| ≤ ‖p‖^2/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
    rw [sq_abs]
    nlinarith [sq_nonneg (c*b-d*a), congrArg₂ (· * ·) hc h]
  fin_cases j
  · convert bound (Real.sqrt 3 / 32) (1/32) (by rw [div_pow, h3]; norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring

  · convert bound 0 (-1/16) (by norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring
  · convert bound (-Real.sqrt 3 / 32) (1/32) (by rw [div_pow, neg_pow, h3]; norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring


private theorem local_b_sq (p : ℂ) (j : Fin 3) : localB p j ^ 2 ≤ ‖p‖ ^ 2 / 6 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by unfold localLinear; positivity)).2
    (local_b_bound p j)
  rwa [sq_abs, mul_pow, local_constant_squares.2.2.2.1, ← div_eq_inv_mul] at h

private theorem local_psi_sq (p : ℂ) (j : Fin 3) : localPsi p j ^ 2 ≤ ‖p‖ ^ 4 / 256 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (local_psi_bound p j)
  rw [sq_abs] at h
  calc
    _ ≤ (‖p‖ ^ 2 / 16) ^ 2 := h
    _ = _ := by ring

private theorem local_tau_bound (p : ℂ) (j : Fin 3) : |localTau p j| ≤ (71/100) * ‖p‖ := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
  rw [sq_abs, localTau, mul_pow, hs]
  calc
    _ ≤ 3 * (‖p‖^2/6) := by gcongr; exact local_b_sq p j
    _ ≤ _ := by nlinarith [sq_nonneg ‖p‖]

private theorem local_cross (p : ℂ) (j : Fin 3) :
    |2 * localS^2 * localTau p j * localPsi p j| ≤ (3/50) * ‖p‖^3 := by
  rw [local_constant_squares.2.1]
  calc
    _ = (4/3) * |localTau p j| * |localPsi p j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2 * (2/3))]
      ring
    _ ≤ (4/3) * ((71/100) * ‖p‖) * (‖p‖^2/16) := by
      gcongr
      · exact local_tau_bound p j
      · exact local_psi_bound p j
    _ ≤ _ := by nlinarith [show 0 ≤ ‖p‖^3 by positivity]

private theorem local_fibre_sq (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    localB p j ^ 2 + localFibre p j ^ 2 ≤ (51/100) * ‖p‖^2 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : localB p j ^ 2 + localFibre p j ^ 2 = 3 * localB p j ^ 2 +
      2 * localS^2 * localTau p j * localPsi p j + (2/3) * localPsi p j ^ 2 := by
    have hτ : localTau p j ^ 2 = 3 * localB p j ^ 2 := by rw [localTau, mul_pow, h3]
    simp only [localFibre, mul_pow, local_constant_squares.2.1, add_sq, hτ]
    ring
  unfold localR at hp
  rw [he]
  have hp3 : ‖p‖^3 ≤ (3/50) * ‖p‖^2 := by
    rw [pow_succ, mul_comm (‖p‖ ^ 2)]
    gcongr
  have hp4 : ‖p‖^4 ≤ (3/50)^2 * ‖p‖^2 := by
    rw [show ‖p‖^4 = ‖p‖^2 * ‖p‖^2 by ring]
    gcongr
  have hcross := (abs_le.mp (local_cross p j)).2
  nlinarith only [local_b_sq p j, local_psi_sq p j, hcross, hp3, hp4, sq_nonneg ‖p‖]

private theorem local_real_bounds (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) :
    0 < localReal p q ∧ localReal p q < 603/1000 := by
  obtain ⟨htl, htu, _, _, hα, hαu, hll, hlu⟩ := local_constant_bounds
  have hprod : localLinear * ‖q‖ ≤ (409/1000) * localR := by gcongr
  have hprod' : localAlpha * ‖p‖^2 ≤ (145/1000) * localR^2 := by gcongr
  unfold localReal localR at *
  exact ⟨by linarith [mul_nonneg hll.le (norm_nonneg q)],
    by linarith [mul_nonneg hα.le (sq_nonneg ‖p‖)]⟩

private theorem local_radicand_bound (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3) : (795/1000)^2 < localRadicand p q j := by
  obtain ⟨ha, ha'⟩ := local_real_bounds p q hp hq
  have hs := (sq_lt_sq₀ ha.le (by norm_num : 0 ≤ (603/1000:ℝ))).2 ha'
  have hp' := (sq_le_sq₀ (norm_nonneg p) (by unfold localR; positivity)).2 hp
  have hb := local_fibre_sq p hp j
  unfold localRadicand
  norm_num [localR] at hp'
  linarith

private theorem local_unit_rim_coe (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3) : ((localUnitRim p q j : U) : ℍ[ℝ]) = localRim p q j := by
  rw [localUnitRim, dif_pos ((by norm_num : (0:ℝ) ≤ (795/1000)^2).trans
    (local_radicand_bound p q hp hq j).le)]
  rfl



end RoundQuaternionLocalSharpness
