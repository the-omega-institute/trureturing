/- GID: D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Reflection isometry, energy orthogonality and all signed integer current transposes on the original charge carrier. -/

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
set_option maxHeartbeats 2000000
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
  change sigma D (∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j,k) p) =
    -(∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j,k) (sigma D p))
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
    rw [map_mul, sigma_X, mul_neg, map_neg, integerWick_creation,
      mul_comm p, integerWick_creation]
    have harg : -((k : ℂ) + 1) • annihilate D i k (sigma D q) =
        -sigma D (-((k : ℂ) + 1) • annihilate D i k q) := by
      rw [sigma_smul, sigma_annihilate]
      simp
    rw [harg, map_neg, neg_neg, hp]

/-- Reflection negates both charge and oscillator variables in the literal carrier. -/
theorem sourcePairing_theta (D : LatticeData) (u v : Carrier D) :
    sourcePairing D (theta D u) (theta D v) = sourcePairing D u v := by
  change sourcePairing D (thetaLinear D u) (thetaLinear D v) = _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp [hu, hw]
  | single a p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [hv, hw]
    | single b q =>
      rw [theta_single, theta_single, sourcePairing_single_single,
        sourcePairing_single_single, integerWick_sigma]
      congr 1
      exact neg_inj.trans (by simp)

private theorem integerWick_neutral (D : LatticeData) (i : Fin D.rank)
    (a : Charge D) (m : ℤ) (p q : Oscillator D) :
    integerWick D (neutralPolynomialMode D i a m p) q =
      -integerWick D p (neutralPolynomialMode D i (-a) (-m) q) := by
  by_cases hn : m < 0
  · let k := (-m-1).toNat
    have hm : m = -(k : ℤ)-1 := by dsimp [k]; omega
    rw [hm, show -(-(k : ℤ)-1) = (k : ℤ)+1 by omega,
      neutralPolynomialMode_negative, neutralPolynomialMode_positive]
    change integerWick D (X (i,k) * p) q =
      -integerWick D p (((k : ℂ)+1) • annihilate D i k q)
    rw [integerWick_creation, neg_smul, map_neg]
  · by_cases hz : m = 0
    · subst m
      simp [neutralPolynomialMode, bilinear,
        LinearMap.BilinForm.smul_left]
    · let k := (m-1).toNat
      have hm : m = (k : ℤ)+1 := by dsimp [k]; omega
      rw [hm, show -((k : ℤ)+1) = -(k : ℤ)-1 by omega,
        neutralPolynomialMode_positive, neutralPolynomialMode_negative]
      change integerWick D (((k : ℂ)+1) • annihilate D i k p) q =
        -integerWick D p (X (i,k) * q)
      have h := integerWick_lowering D i k p q
      rw [neg_smul, map_neg] at h
      exact neg_eq_iff_eq_neg.mp h

/-- Every integer current, including its genuine charge zero mode, is skew transpose. -/
theorem sourcePairing_neutralMode (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (u v : Carrier D) :
    sourcePairing D (neutralMode D i m u) v =
      -sourcePairing D u (neutralMode D i (-m) v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp [hu, hw, neg_add]
  | single a p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [hv, hw, neg_add]
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
  have h := IsWeightedHomogeneous.prod d.support
    (fun x => OriginalCurrentMetric.variableImage A x ^ d x)
    (fun x => d x • ((x.2 : ℤ)+1)) ?_
  · simpa only [Finsupp.weight_apply, Finsupp.sum] using h
  · intro x hx
    apply IsWeightedHomogeneous.pow
    apply IsWeightedHomogeneous.sum
    intro j hj
    exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ _).smul_mem _
      (isWeightedHomogeneous_X ℂ _ (j,x.2))

private theorem retune_monomial (D : LatticeData) (d : Exponent D) (c : ℂ) :
    retune D (monomial d c) =
      monomial d (c * d.prod (fun x e => integerScale x.2 ^ e)) := by
  rw [monomial_eq, map_mul, show retune D (C c) = C c from (retune D).commutes c]
  simp only [Finsupp.prod, map_prod, map_pow, retune_X, smul_eq_C_mul,
    mul_pow, ← Finset.prod_mul_distrib]
  rw [← map_prod, ← mul_assoc, ← map_mul, monomial_eq]
  simp [Finsupp.prod]

private theorem integerWick_monomial_energy (D : LatticeData)
    (d e : Exponent D) (h : oscillatorEnergy d ≠ oscillatorEnergy e) :
    integerWick D (monomial d 1) (monomial e 1) = 0 := by
  rw [integerWick_apply, retune_monomial]
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D)
      (monomial d (1 * d.prod (fun x n => integerScale x.2 ^ n))))
    (monomial e 1) = 0
  rw [FactorialBilinear.symmetric, FactorialBilinear.monomial_left]
  have hw := substitution_monomial_weight D (modeMatrix D) d
    (1 * d.prod (fun x n => integerScale x.2 ^ n))
  have hweight (z : Exponent D) :
      Finsupp.weight (fun x : Index D => (x.2 : ℤ)+1) z =
        (oscillatorEnergy z : ℤ) := by
    simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
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
      exact basis_energy_orthogonal D a b (by simpa [ha, hb] using hk)
    | zero => simp
    | add v w hv hw => simp [hv, hw]
    | smul c v hv => simp [hv]
  | zero => simp
  | add u w hu hw => simp [hu, hw]
  | smul c u hu => simp [hu]

#print axioms sourcePairing_theta
#print axioms sourcePairing_neutralMode
#print axioms sourcePairing_grade

end D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
