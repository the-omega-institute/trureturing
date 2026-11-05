/- GID: D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolEventArithmetic
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Original raw event integrality and integer norms force arithmetic resource bounds. -/

import D5.S3.Quantum.Dynamics.NativeProtocolEventCoordinates

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Dynamics.NativeProtocolGraft
open Tree

/-- The inverse golden ratio is an algebraic integer before any conditioning. -/
private theorem t_integral : IsIntegral ℤ t := by
  have hcos : 2 * Real.cos ((2 / 5 : ℚ) * Real.pi) = phi⁻¹ := by
    rw [show ((2 / 5 : ℚ) : ℝ) * Real.pi = 2 * (Real.pi / 5) by norm_num; ring,
      Real.cos_two_mul, Real.cos_pi_div_five]
    change _ = Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have ht : IsIntegral ℤ (phi⁻¹ : ℝ) :=
    hcos ▸ Real.isIntegral_two_mul_cos_rat_mul_pi (2 / 5)
  exact (isIntegral_algebraMap_iff (B := ℂ)).mpr ht

private theorem beta_integral : IsIntegral ℤ beta := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have hb : beta ^ 2 = t := by
    dsimp [beta, t]
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    exact inv_nonneg.mpr (by dsimp [phi]; positivity)
  rw [hb]
  exact t_integral

private theorem zeta_integral : IsIntegral ℤ zeta := by
  unfold zeta
  convert Complex.isIntegral_exp_rat_mul_pi_mul_I (3 / 5) using 1 <;>
    push_cast <;> congr 1 <;> ring

private theorem number_integral (i : Fin 16) (b c : Basis) :
    IsIntegral ℤ (number i b c) := by
  classical
  simp only [number, Matrix.diagonal_apply]
  split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

private theorem gate_integral (j : Address) (b c : Basis) :
    IsIntegral ℤ (gate j b c) := by
  classical
  have hid (b c : Basis) : IsIntegral ℤ ((1 : Mat) b c) := by
    simp only [Matrix.one_apply]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  have hx (b c : Basis) : IsIntegral ℤ (bitX (center j) b c) := by
    simp only [bitX]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  have hq (b c : Basis) : IsIntegral ℤ (goldenQ j b c) := by
    exact ((t_integral.mul ((hid b c).sub (number_integral _ b c))).add
      ((t_integral.pow 2).mul (number_integral _ b c))).add
      ((beta_integral.pow 3).mul (hx b c))
  have hmul (A B : Mat) (hA : ∀ b c, IsIntegral ℤ (A b c))
      (hB : ∀ b c, IsIntegral ℤ (B b c)) (b c : Basis) : IsIntegral ℤ ((A * B) b c) := by
    rw [Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ => (hA b k).mul (hB k c))
  have hp : IsIntegral ℤ (goldenP j b c) := by
    apply IsIntegral.add
    · exact hmul _ _ (number_integral _) (number_integral _) b c
    · exact hmul _ _ (fun b c => hmul _ _
        (fun b c => (hid b c).sub (number_integral _ b c))
        (fun b c => (hid b c).sub (number_integral _ b c)) b c) hq b c
  exact zeta_integral.mul ((hid b c).add ((zeta_integral.sub isIntegral_one).mul hp))

private theorem call_integral (j : Address) (d : Direction) (b c : Basis) :
    IsIntegral ℤ (callMatrix j d b c) := by
  classical
  have hp (n : ℕ) : ∀ b c, IsIntegral ℤ ((gate j ^ n) b c) := by
    induction n with
    | zero =>
      intro b c
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
    | succ n ih =>
      intro b c
      rw [pow_succ, Matrix.mul_apply]
      exact IsIntegral.sum _ (fun k _ => (ih b k).mul (gate_integral j k c))
  cases d
  · exact gate_integral j b c
  · exact hp 9 b c

private theorem projector_integral {n : ℕ} (select : Basis → Fin n) (o : Fin n)
    (b c : Basis) : IsIntegral ℤ (projector select o b c) := by
  classical
  simp only [projector, Matrix.diagonal_apply]
  split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

private theorem operator_integral {L : Type} (T : Tree L) (p : Path T) (b c : Basis) :
    IsIntegral ℤ (operator T p b c) := by
  classical
  induction T generalizing b c with
  | leaf l =>
    simp only [operator, Matrix.one_apply]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | call j d U ih =>
    simp only [operator, Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ => (ih p b k).mul (call_integral j d k c))
  | measure n select U ih =>
    simp only [operator, Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ =>
      (ih p.1 p.2 b k).mul (projector_integral select p.1 k c))

/-- Every raw finite event of the original full-menu tree is an algebraic
integer. The statement includes all terminal records, with arbitrary feedback,
inverse calls expanded to nine forward calls and the original fixed root. -/
private theorem original_event_integral {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) : IsIntegral ℤ (eventMass T event) := by
  classical
  have hv (p : Path T) (z : Basis) :
      IsIntegral ℤ ((operator T p).mulVec omega0 z) := by
    simp only [Matrix.mulVec, dotProduct]
    exact IsIntegral.sum _ (fun b _ => (operator_integral T p z b).mul
      (by simp only [omega0]; split_ifs <;>
        first | exact isIntegral_one | exact isIntegral_zero))
  have hm (p : Path T) (z : Basis) : IsIntegral ℤ (mass T p z) := by
    apply (isIntegral_algebraMap_iff (B := ℂ)).mp
    change IsIntegral ℤ ((Complex.normSq ((operator T p).mulVec omega0 z) : ℝ) : ℂ)
    rw [Complex.normSq_eq_conj_mul_self]
    exact ((hv p z).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)).mul (hv p z)
  unfold eventMass
  apply IsIntegral.sum
  intro p _
  apply IsIntegral.sum
  intro z _
  split_ifs
  · exact hm p z
  · exact isIntegral_zero

/-- The two scalar masses occurring in the original reference comparison. -/
def emptyTarget : ℝ := (13 - 5 * Real.sqrt 5) / 22
def referenceTarget : ℝ := (9 * Real.sqrt 5 - 19) / 22

private abbrev GoldenField :=
  D5.S3.Arith.Lattices.GoldenIntegerRing.GoldenNumberField

private def goldenEmbedding : GoldenField →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenRatio, by
    simpa only [Rat.smul_def, Rat.cast_one, one_mul, smul_eq_mul, mul_one,
      ← pow_two, one_pow, add_comm] using Real.goldenRatio_sq⟩

private theorem target_nonintegral :
    ¬ IsIntegral ℤ emptyTarget ∧ ¬ IsIntegral ℤ referenceTarget := by
  have norm_obstruction (a : GoldenField) (n : ℚ)
      (hn : Algebra.norm ℚ a = n) (hni : ¬ IsIntegral ℤ n) :
      ¬ IsIntegral ℤ (goldenEmbedding a) := by
    intro h
    have ha : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (goldenEmbedding.restrictScalars ℤ)
        goldenEmbedding.injective).mp h
    exact hni (hn ▸ Algebra.isIntegral_norm ℚ ha)
  have he : goldenEmbedding (⟨9/11,-5/11⟩ : GoldenField) = emptyTarget := by
    simp [goldenEmbedding, QuadraticAlgebra.lift, emptyTarget, Real.goldenRatio, Rat.smul_def]
    ring
  have hr : goldenEmbedding (⟨-14/11,9/11⟩ : GoldenField) = referenceTarget := by
    simp [goldenEmbedding, QuadraticAlgebra.lift, referenceTarget, Real.goldenRatio, Rat.smul_def]
    ring
  constructor
  · rw [← he]
    apply norm_obstruction _ (1/11)
    · change (DistribSMul.toLinearMap ℚ GoldenField
        (⟨9/11,-5/11⟩ : GoldenField)).det = 1/11
      rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
      norm_num [QuadraticAlgebra.norm]
    · intro h
      obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp h
      change (z : ℚ) = 1 / 11 at hz
      have hh : (11 : ℚ) * (z : ℚ) = 1 := by rw [hz]; norm_num
      have hh' : 11 * z = 1 := by exact_mod_cast hh
      omega
  · rw [← hr]
    apply norm_obstruction _ (-1/11)
    · change (DistribSMul.toLinearMap ℚ GoldenField
        (⟨-14/11,9/11⟩ : GoldenField)).det = -1/11
      rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
      norm_num [QuadraticAlgebra.norm]
    · intro h
      obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp h
      change (z : ℚ) = -1 / 11 at hz
      have hh : (11 : ℚ) * (z : ℚ) = -1 := by rw [hz]; norm_num
      have hh' : 11 * z = -1 := by exact_mod_cast hh
      omega

/-- Raw events in any original native tree are algebraic integers and hence
cannot equal either of the two nonintegral reference-comparison masses. -/
theorem original_event_arithmetic {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    IsIntegral ℤ (eventMass T event) ∧ eventMass T event ≠ emptyTarget ∧
      eventMass T event ≠ referenceTarget := by
  have h := original_event_integral T event
  exact ⟨h, fun he => target_nonintegral.1 (he ▸ h),
    fun he => target_nonintegral.2 (he ▸ h)⟩

#print axioms original_event_arithmetic


namespace Coeff


private theorem norm_product (x : O) :
    realPhysical x * realConjugate x = ((QuadraticAlgebra.norm x : ℤ) : ℝ) := by
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]
    ring
  have hp : phi^2 = phi+1 := Real.goldenRatio_sq
  change ((x.re : ℝ)+(x.im : ℝ)*phi⁻¹) *
    ((x.re : ℝ)+(x.im : ℝ)*(-phi)) = _
  rw [hi, QuadraticAlgebra.norm_def]
  push_cast
  linear_combination -(x.im : ℝ)^2 * hp

private theorem norm_zero (x : O) (hn : QuadraticAlgebra.norm x = 0) : x = 0 := by
  let g : D5.S0.Carrier.GoldenInt := ⟨x.re-x.im,x.im⟩
  have hg : D5.S0.Carrier.norm g = 0 := by
    dsimp [D5.S0.Carrier.norm, g]
    rw [QuadraticAlgebra.norm_def] at hn
    nlinarith
  have hz := (D5.S0.Carrier.norm_eq_zero_iff g).mp hg
  have ha := congrArg D5.S0.Carrier.GoldenInt.a hz
  have hb := congrArg D5.S0.Carrier.GoldenInt.b hz
  dsimp [g] at ha hb
  ext <;> simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero] <;> omega

private theorem int_abs_lower (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  have hh : (1 : ℤ) ≤ |n| := by
    by_cases hp : 0 ≤ n
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_neg (lt_of_not_ge hp)]; omega
  exact_mod_cast hh

private theorem norm_div11 (x u : O)
    (hu : QuadraticAlgebra.norm u = 11 ∨ QuadraticAlgebra.norm u = -11) :
    11 ∣ QuadraticAlgebra.norm (11*x-u) := by
  let c := 2*x.re*u.re-x.re*u.im-x.im*u.re-2*x.im*u.im
  have he : QuadraticAlgebra.norm (11*x-u) =
      121*QuadraticAlgebra.norm x-11*c+QuadraticAlgebra.norm u := by
    simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    dsimp [c]
    ring
  rw [he]
  rcases hu with hu | hu
  · refine ⟨11*QuadraticAlgebra.norm x-c+1,?_⟩
    rw [hu]; ring
  · refine ⟨11*QuadraticAlgebra.norm x-c-1,?_⟩
    rw [hu]; ring

private theorem discrepancy (x u : O) (a K C : ℝ)
    (hu : realPhysical u = 11*a)
    (hc : |realConjugate u| = 11*C)
    (hn : QuadraticAlgebra.norm u = 11 ∨ QuadraticAlgebra.norm u = -11)
    (hne : realPhysical x ≠ a) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hb : |realConjugate x| ≤ K) :
    1/(11*(K+C)) ≤ |realPhysical x-a| := by
  let y : O := 11*x-u
  have hny : QuadraticAlgebra.norm y ≠ 0 := by
    intro he
    have hy := norm_zero y he
    have hh := congrArg realPhysical hy
    simp only [y, map_sub, map_mul, map_ofNat, map_zero, hu] at hh
    apply hne
    linarith
  obtain ⟨k,hk⟩ := norm_div11 x u hn
  have hk0 : k ≠ 0 := by
    intro he
    apply hny
    change QuadraticAlgebra.norm (11*x-u) = 0
    simp [hk, he]
  have hlow : (11 : ℝ) ≤ |((QuadraticAlgebra.norm y : ℤ) : ℝ)| := by
    have hka := int_abs_lower k hk0
    dsimp [y]
    rw [hk, Int.cast_mul, Int.cast_ofNat, abs_mul]
    norm_num only
    linarith
  have hpy : realPhysical y = 11*(realPhysical x-a) := by
    dsimp [y]
    rw [map_sub, map_mul, map_ofNat, hu]
    ring
  have hcy : |realConjugate y| ≤ 11*(K+C) := by
    dsimp [y]
    simp only [map_sub, map_mul, map_ofNat]
    have ht := abs_sub (11*realConjugate x) (realConjugate u)
    rw [abs_mul, hc] at ht
    norm_num only at ht
    nlinarith
  rw [← norm_product, abs_mul, hpy, abs_mul] at hlow
  norm_num only at hlow
  have hh := mul_le_mul_of_nonneg_left hcy (mul_nonneg (by norm_num : (0:ℝ) ≤ 11) (abs_nonneg (realPhysical x-a)))
  have hden : 0 < 11*(K+C) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [hh, abs_nonneg (realPhysical x-a)]

theorem positive_lower (x : O) (K : ℝ) (hK : 0 < K)
    (hp : 0 < realPhysical x) (hb : |realConjugate x| ≤ K) :
    K⁻¹ ≤ realPhysical x := by
  have hn : QuadraticAlgebra.norm x ≠ 0 := by
    intro he
    have hz := norm_zero x he
    rw [hz, map_zero] at hp
    linarith
  have hlow := int_abs_lower (QuadraticAlgebra.norm x) hn
  rw [← norm_product, abs_mul, abs_of_pos hp] at hlow
  rw [inv_le_iff_one_le_mul₀ hK]
  nlinarith [mul_le_mul_of_nonneg_left hb hp.le]

end Coeff

/-- Arithmetic resource bounds for every computed original raw event. The
reference-state and record-law realization obligations are separate. -/
theorem original_event_resource_bounds {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    (0 < eventMass T event →
      (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ eventMass T event) ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
      |eventMass T event-emptyTarget| ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(19+9*Real.sqrt 5)/22)) ≤
      |eventMass T event-referenceTarget| := by
  let x := Coeff.coordinates T event
  have hm := (original_event_coordinates_and_bound T event).1
  have hb := (original_event_coordinates_and_bound T event).2.2
  have hK : 1 ≤ Coeff.kappa^(2*maxCalls T) := one_le_pow₀ Coeff.kappa_one
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]; ring
  refine ⟨?_,?_,?_⟩
  · intro hp
    rw [hm] at hp ⊢
    exact Coeff.positive_lower x _ (lt_of_lt_of_le zero_lt_one hK) hp hb
  · rw [hm]
    apply Coeff.discrepancy x (⟨4,-5⟩ : Coeff.O) emptyTarget _
      ((13+5*Real.sqrt 5)/22)
    · simp only [Coeff.realPhysical, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [hi]; dsimp [phi, emptyTarget]; ring
    · simp only [Coeff.realConjugate, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [abs_of_nonneg (by have hp := Coeff.phi_positive; nlinarith)]
      dsimp [phi]; ring
    · left; norm_num [QuadraticAlgebra.norm_def]
    · rw [← hm]
      exact (original_event_arithmetic T event).2.1
    · exact hK
    · positivity
    · exact hb
  · rw [hm]
    apply Coeff.discrepancy x (⟨-5,9⟩ : Coeff.O) referenceTarget _
      ((19+9*Real.sqrt 5)/22)
    · simp only [Coeff.realPhysical, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [hi]; dsimp [phi, referenceTarget]; ring
    · simp only [Coeff.realConjugate, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [abs_of_nonpos (by dsimp [phi]; nlinarith [Real.sqrt_nonneg (5:ℝ)])]
      dsimp [phi]; ring
    · right; norm_num [QuadraticAlgebra.norm_def]
    · rw [← hm]
      exact (original_event_arithmetic T event).2.2
    · exact hK
    · positivity
    · exact hb

#print axioms original_event_coordinates_and_bound
#print axioms original_event_resource_bounds

end D5.S3.Quantum.Dynamics.NativeProtocolGraft
