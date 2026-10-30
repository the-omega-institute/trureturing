/- GID: D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Original-carrier reflection, energy orthogonality and integer-current transposes. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
import D5.S3.VertexAlgebra.LatticeEnergyGrading

/-!
The bilinear form on the original carrier respects reflection, the full signed
energy grading and all integer neutral currents. The zero current is the actual
charge scalar. These algebraic statements allow degenerate and indefinite Gram
matrices and rank zero. They do not assert charged-field or all-state BPZ.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeActualAnnihilation LatticeInvolution
open LatticePositiveEnergy MvPolynomial OriginalSourcePairing
open private wick_constant_left from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
open private FactorialBilinear.form FactorialBilinear.monomial_left
  FactorialBilinear.symmetric modeMatrix from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

private theorem sigma_constant (D : LatticeData) (p : Oscillator D) :
    (sigma D p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    rw [map_mul, sigma_X, mul_neg, MvPolynomial.coeff_neg,
      MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
    simp

private theorem sigma_annihilate (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) :
    sigma D (annihilate D i k p) = -annihilate D i k (sigma D p) := by
  simp only [annihilate, weightedPartial, LinearMap.sum_apply,
    LinearMap.smul_apply, Derivation.coeFn_coe]
  simp only [map_sum, sigma_smul, sigma_pderiv, smul_neg,
    Finset.sum_neg_distrib]

private theorem integerWick_sigma (D : LatticeData) (p q : Oscillator D) :
    integerWick D (sigma D p) (sigma D q) = integerWick D p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    simp only [sigma_C, integerWick_apply,
      show retune D (C c) = C c from (retune D).commutes c,
      wick_constant_left, sigma_constant]
  | add p r hp hr =>
    simp only [map_add, LinearMap.add_apply, hp, hr]
  | mul_X p x hp =>
    rcases x with ⟨i,k⟩
    rw [map_mul, sigma_X, mul_neg, map_neg, LinearMap.neg_apply,
      mul_comm (sigma D p), integerWick_creation, mul_comm p, integerWick_creation]
    have harg : -((k : ℂ) + 1) • annihilate D i k (sigma D q) =
        -sigma D (-((k : ℂ) + 1) • annihilate D i k q) := by
      rw [sigma_smul, sigma_annihilate]
      simp
    simp only [harg, map_neg, neg_neg, hp]

/-- Reflection negates both charge and oscillator variables in the literal carrier. -/
theorem sourcePairing_theta (D : LatticeData) (u v : Carrier D) :
    sourcePairing D (theta D u) (theta D v) = sourcePairing D u v := by
  change sourcePairing D (thetaLinear D u) (thetaLinear D v) = _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | single a p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | single b q =>
      rw [theta_single, theta_single, sourcePairing_single_single,
        sourcePairing_single_single, integerWick_sigma]
      have hc : (-b = - -a) ↔ b = -a := neg_inj
      simp only [hc]

private theorem integerWick_neutral (D : LatticeData) (i : Fin D.rank)
    (a : Charge D) (m : ℤ) (p q : Oscillator D) :
    integerWick D (neutralPolynomialMode D i a m p) q =
      -integerWick D p (neutralPolynomialMode D i (-a) (-m) q) := by
  by_cases hn : m < 0
  · let k := (-m-1).toNat
    have hm : m = -(k : ℤ)-1 := by dsimp [k]; omega
    rw [hm, show -(-(k : ℤ)-1) = (k : ℤ)+1 by omega,
      neutralPolynomialMode_negative, neutralPolynomialMode_positive]
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply]
    change integerWick D (X (i,k) * p) q =
      -integerWick D p (((k : ℂ)+1) • annihilate D i k q)
    rw [integerWick_creation, neg_smul, map_neg]
  · by_cases hz : m = 0
    · subst m
      simp only [neutralPolynomialMode, neg_zero, lt_self_iff_false,
        ite_false, ite_true, LinearMap.smul_apply, LinearMap.id_apply,
        bilinear_neg_right, Int.cast_neg, neg_smul, LinearMap.neg_apply,
        map_smul, map_neg, neg_neg]
    · let k := (m-1).toNat
      have hm : m = (k : ℤ)+1 := by dsimp [k]; omega
      rw [hm, show -((k : ℤ)+1) = -(k : ℤ)-1 by omega,
        neutralPolynomialMode_positive, neutralPolynomialMode_negative]
      simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply]
      change integerWick D (((k : ℂ)+1) • annihilate D i k p) q =
        -integerWick D p (X (i,k) * q)
      have h := integerWick_lowering D i k p q
      simp only [neg_smul, map_neg, LinearMap.neg_apply] at h
      exact neg_eq_iff_eq_neg.mp h

/-- Every integer current, including its genuine charge zero mode, is skew transpose. -/
theorem sourcePairing_neutralMode (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (u v : Carrier D) :
    sourcePairing D (neutralMode D i m u) v =
      -sourcePairing D u (neutralMode D i (-m) v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, hu, hw, neg_add_rev]
    exact add_comm _ _
  | single a p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw =>
      simp only [map_add, hv, hw, neg_add_rev]
      exact add_comm _ _
    | single b q =>
      rw [neutralMode_single, neutralMode_single,
        sourcePairing_single_single, sourcePairing_single_single]
      by_cases h : b = -a
      · subst b
        simp only [ite_true]
        exact integerWick_neutral D i a m p q
      · simp [h]

private theorem substitution_monomial_weight (D : LatticeData)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (d : Exponent D) (c : ℂ) :
    IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ)+1)
      (OriginalCurrentMetric.substitution A (monomial d c))
      (Finsupp.weight (fun x : Index D => (x.2 : ℤ)+1) d) := by
  classical
  rw [OriginalCurrentMetric.substitution, MvPolynomial.aeval_monomial]
  apply IsWeightedHomogeneous.C_mul
  change IsWeightedHomogeneous _ (∏ x ∈ d.support,
    OriginalCurrentMetric.variableImage A x ^ d x) _
  have hgen (x : Index D) :
      IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ)+1)
        (OriginalCurrentMetric.variableImage A x ^ d x) (d x • ((x.2 : ℤ)+1)) := by
    apply IsWeightedHomogeneous.pow
    apply IsWeightedHomogeneous.sum
    intro j hj
    exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ _).smul_mem _
      (isWeightedHomogeneous_X ℂ _ (j,x.2))
  have hh := IsWeightedHomogeneous.prod d.support _ _ (fun x _ => hgen x)
  simpa only [Finsupp.weight_apply, Finsupp.sum] using hh

private theorem substitution_weight (D : LatticeData)
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Oscillator D) (n : ℤ)
    (hp : IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ)+1) p n) :
    IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ)+1)
      (OriginalCurrentMetric.substitution A p) n := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  have hn := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [← hn]
  exact substitution_monomial_weight D A d (p.coeff d)

private theorem integerWick_monomial_energy (D : LatticeData)
    (d e : Exponent D) (h : oscillatorEnergy d ≠ oscillatorEnergy e) :
    integerWick D (monomial d 1) (monomial e 1) = 0 := by
  rw [integerWick_apply]
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D)
      (retune D (monomial d 1)))
    (monomial e 1) = 0
  rw [FactorialBilinear.symmetric, FactorialBilinear.monomial_left]
  have hr := substitution_monomial_weight D (fun k => retuneMatrix D k) d 1
  change IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ)+1)
    (retune D (monomial d 1)) _ at hr
  have hw := substitution_weight D (modeMatrix D) _ _ hr
  have hweight (z : Exponent D) :
      Finsupp.weight (fun x : Index D => (x.2 : ℤ)+1) z =
        (oscillatorEnergy z : ℤ) := by
    simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_add]
  rw [hw.coeff_eq_zero e (by rw [hweight, hweight]; exact_mod_cast Ne.symm h)]
  simp

private theorem basis_energy_orthogonal (D : LatticeData) (a b : Label D)
    (h : energy D a ≠ energy D b) :
    sourcePairing D (carrierBasis D a) (carrierBasis D b) = 0 := by
  rw [carrierBasis_apply, carrierBasis_apply, sourcePairing_single_single]
  split_ifs with hab
  · have hc : chargeEnergy D b.1 = chargeEnergy D a.1 := by
      rw [hab, chargeEnergy, bilinear_neg_neg]
      rfl
    apply integerWick_monomial_energy
    intro he
    apply h
    simp only [energy, hc, he]
  · rfl

/-- Distinct full signed energy grades are orthogonal, without finite-dimensionality. -/
theorem sourcePairing_grade (D : LatticeData) (h k : ℤ) (hk : h ≠ k)
    (u v : Carrier D) (hu : u ∈ grade D h) (hv : v ∈ grade D k) :
    sourcePairing D u v = 0 := by
  rw [grade_eq_span] at hu hv
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, hb, rfl⟩ := hv
      have ha' : energy D a = h := ha
      have hb' : energy D b = k := hb
      exact basis_energy_orthogonal D a b (by rw [ha', hb']; exact hk)
    | zero => simp
    | add v w hv hw ihv ihw =>
      simp only [map_add, ihv, ihw, add_zero]
    | smul c v hv ih => simp only [map_smul, ih, smul_zero]
  | zero => simp
  | add u w hu hw ihu ihw =>
    simp only [map_add, LinearMap.add_apply, ihu, ihw, add_zero]
  | smul c u hu ih =>
    simp only [map_smul, LinearMap.smul_apply, ih, smul_zero]

#print axioms sourcePairing_theta
#print axioms sourcePairing_neutralMode
#print axioms sourcePairing_grade

end D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
