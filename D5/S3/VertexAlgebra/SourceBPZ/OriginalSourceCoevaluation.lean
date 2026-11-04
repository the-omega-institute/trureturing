/- GID: D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse, mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Explicit inverse-Wick charge coefficients and projected finite-energy source coevaluation. -/

import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
The original bilinear source form has a coefficient dual obtained by reversing
charge and substituting the actual matrix -(k+1)⁻¹ G⁻¹, divided by every
occupation factorial. Its theta projection gives a finite frame, rather than
an independent basis. All sums below are algebraic sums at a signed energy.
No analytic convergence, crossing or mixed Jacobi statement is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField MvPolynomial OriginalSourcePairing SourcePairingLaws
open SignedOscillatorWick OriginalCurrentMetric
open LatticeHalfFock (gramComplex)

/-- Same-mode inverse of the original integer-frequency Wick covariance. -/
def inverseOscillator (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  substitution (fun k => (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹)

/-- Each occupation contributes its own factorial, including the empty product. -/
def dualOscillatorMonomial (D : LatticeData) (α : Exponent D) : Oscillator D :=
  (FactorialFockMetric.weight α : ℂ)⁻¹ •
    inverseOscillator D (monomial α 1)

/-- Charge is reversed in the literal original carrier. -/
def dualCarrierBasis (D : LatticeData) (a : Label D) : Carrier D :=
  Finsupp.single (-a.1) (dualOscillatorMonomial D a.2)

private theorem integer_covariance (D : LatticeData) (k : ℕ) :
    modeMatrix D k * retuneMatrix D k =
      -((k : ℂ) + 1) • gramComplex D := by
  rw [modeMatrix, retuneMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, Matrix.mul_one]
  congr 1
  rw [neg_mul, mul_comm, integerScale_mul_frequency]

private theorem covariance_inverse (D : LatticeData) (hu : IsUnit D.G.det)
    (k : ℕ) :
    (-((k : ℂ) + 1) • gramComplex D) *
      ((-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹) = 1 := by
  have hn : -((k : ℂ) + 1) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ hn, one_smul,
    Matrix.mul_nonsing_inv _ (complex_det_unit D hu)]

private theorem integerWick_dual (D : LatticeData) (hu : IsUnit D.G.det)
    (α : Exponent D) (p : Oscillator D) :
    integerWick D (dualOscillatorMonomial D α) p = p.coeff α := by
  have hinv (q : Oscillator D) :
      substitution (modeMatrix D) (retune D (inverseOscillator D q)) = q := by
    change ((substitution (modeMatrix D)).comp
      (substitution (retuneMatrix D))).comp
        (inverseOscillator D) q = q
    rw [substitution_comp]
    simp only [integer_covariance]
    exact AlgHom.congr_fun (substitution_inverse _ _ (covariance_inverse D hu)) q
  have hw : (FactorialFockMetric.weight α : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (FactorialFockMetric.weight_pos α))
  change FactorialBilinear.form (Index D)
    (substitution (modeMatrix D) (retune D (dualOscillatorMonomial D α))) p = _
  simp only [dualOscillatorMonomial, map_smul, hinv,
    LinearMap.smul_apply, FactorialBilinear.monomial_left, mul_one,
    smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- Exact native coefficient extraction for every original state. -/
theorem dualCarrierBasis_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Label D) (v : Carrier D) :
    sourcePairing D (dualCarrierBasis D a) v = carrierCoeffEquiv D v a := by
  rw [dualCarrierBasis, sourcePairing_single, neg_neg, integerWick_dual D hu]
  rfl

private theorem oscillator_weight (D : LatticeData) (α : Exponent D) :
    IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ) + 1)
      (dualOscillatorMonomial D α) (oscillatorEnergy α : ℤ) := by
  have hw := substitution_monomial_weight D
    (fun k => (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹) α 1
  have he : Finsupp.weight (fun x : Index D => (x.2 : ℤ) + 1) α =
      (oscillatorEnergy α : ℤ) := by
    simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_add]
  rw [he] at hw
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ _ _).smul_mem _ hw

/-- The explicit inverse preserves the exact full signed energy. -/
theorem dualCarrierBasis_mem_grade (D : LatticeData) (a : Label D) :
    dualCarrierBasis D a ∈ grade D (energy D a) := by
  classical
  rw [mem_grade_iff]
  intro b hb
  by_cases hc : -a.1 = b.1
  · have hn : oscillatorEnergy b.2 ≠ oscillatorEnergy a.2 := by
      intro h
      apply hb
      simp only [energy, ← hc, chargeEnergy, bilinear_neg_neg, h]
    simp only [dualCarrierBasis, Finsupp.single_eq_same, ← hc]
    exact (oscillator_weight D a.2).coeff_eq_zero b.2 (by
      have he : Finsupp.weight (fun x : Index D => (x.2 : ℤ) + 1) b.2 =
          (oscillatorEnergy b.2 : ℤ) := by
        simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum,
          Nat.cast_sum, Nat.cast_mul, Nat.cast_add]
      rw [he]
      exact_mod_cast hn)
  · simp [dualCarrierBasis, Finsupp.single_apply, hc]

private theorem basis_mem_grade (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    carrierBasis D a.val ∈ grade D h := by
  rw [grade_eq_span]
  exact Submodule.subset_span ⟨a.val, a.property, rfl⟩

private theorem theta_mem_grade (D : LatticeData) (h : ℤ) (v : Carrier D)
    (hv : v ∈ grade D h) : theta D v ∈ grade D h := by
  rw [grade_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    change energy D a = h at ha
    have he : energy D (-a.1, a.2) = h := by
      simpa only [energy, chargeEnergy, bilinear_neg_neg] using ha
    have hm := (grade D h).smul_mem
      ((-1 : ℂ) ^ (occurrences D a.2).length)
      (basis_mem_grade D h ⟨(-a.1, a.2), he⟩)
    change thetaLinear D (carrierBasis D a) ∈ grade D h
    simpa only [carrierBasis_apply, theta_single, sigma_monomial,
      Finsupp.smul_single] using hm
  | zero => simpa only [map_zero] using (grade D h).zero_mem
  | add u v hu hv ihu ihv =>
    simpa only [map_add] using (grade D h).add_mem ihu ihv
  | smul c v hv ih =>
    simpa only [map_smul] using (grade D h).smul_mem c ih

private def projectGrade (D : LatticeData) (h : ℤ) :
    grade D h →ₗ[ℂ] ↥(grade D h ⊓ fixedSpace D) where
  toFun x := ⟨plusPart D x.val, by
    constructor
    · exact (grade D h).smul_mem _
        ((grade D h).add_mem x.property (theta_mem_grade D h x.val x.property))
    · change plusPart D x.val ∈ fixedSpace D
      rw [mem_fixedSpace]
      have hi : theta D (theta D x.val) = x.val := theta_involutive D x.val
      simp only [plusPart, map_smul, map_add]
      rw [hi, add_comm]⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [plusPart, Submodule.coe_add, map_add, smul_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    simp [plusPart, smul_add, smul_smul, mul_comm]

/-- Projected original charge/occupation vectors; no orbit representatives. -/
def fixedFrame (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    ↥(grade D h ⊓ fixedSpace D) :=
  projectGrade D h ⟨carrierBasis D a.val, basis_mem_grade D h a⟩

/-- Projected explicit inverse-Wick vectors at the same signed grade. -/
def fixedDualFrame (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    ↥(grade D h ⊓ fixedSpace D) :=
  projectGrade D h ⟨dualCarrierBasis D a.val, by
    simpa only [a.property] using dualCarrierBasis_mem_grade D a.val⟩

private theorem gradeBasis_val (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    (gradeBasis D h a).val = carrierBasis D a.val := by
  apply (carrierCoeffEquiv D).injective
  change carrierCoeffEquiv D ((gradeCoeffEquiv D h).symm (Finsupp.single a 1)).val =
    (carrierBasis D).repr (carrierBasis D a.val)
  rw [Module.Basis.repr_self]
  change (carrierCoeffEquiv D) ((carrierCoeffEquiv D).symm
    ((Finsupp.supportedEquivFinsupp (M := ℂ)
      (R := ℂ) {a : Label D | energy D a = h}).symm (Finsupp.single a 1)).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.supportedEquivFinsupp_symm_single _ a 1

private theorem frame_project_expansion (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (x : grade D h) :
    (∑ᶠ a : EnergyFiber D h,
      (carrierCoeffEquiv D x.val a.val) • fixedFrame D h a) = projectGrade D h x := by
  classical
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  rw [finsum_eq_sum_of_fintype]
  have hs := congrArg (projectGrade D h) ((gradeBasis D h).sum_repr x)
  rw [map_sum] at hs
  simp only [map_smul] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply congrArg (projectGrade D h)
  apply Subtype.ext
  exact (gradeBasis_val D h a).symm

private theorem frame_expansion (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (x : ↥(grade D h ⊓ fixedSpace D)) :
    (∑ᶠ a : EnergyFiber D h,
      (carrierCoeffEquiv D x.val a.val) • fixedFrame D h a) = x := by
  rw [frame_project_expansion D hD h ⟨x.val, x.property.1⟩]
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • (x.val + theta D x.val) = x.val
  rw [(mem_fixedSpace D x.val).mp x.property.2, ← two_smul ℂ x.val,
    smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem projected_dual_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : EnergyFiber D h) (x : ↥(grade D h ⊓ fixedSpace D)) :
    sourcePairing D (fixedDualFrame D h a).val x.val =
      carrierCoeffEquiv D x.val a.val := by
  have ht := sourcePairing_theta D (dualCarrierBasis D a.val) x.val
  rw [(mem_fixedSpace D x.val).mp x.property.2] at ht
  change sourcePairing D (plusPart D (dualCarrierBasis D a.val)) x.val = _
  simp only [plusPart, map_smul, map_add, LinearMap.smul_apply,
    LinearMap.add_apply, ht, dualCarrierBasis_pairing D hu, smul_eq_mul]
  ring

/-- The actual finite-energy coevaluation, with the original theta projection. -/
def coevaluation (D : LatticeData) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    ↥(grade D h ⊓ fixedSpace D) :=
  ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) • fixedDualFrame D h a

/-- Evaluation of the explicit factorial/Gram frame against the original form. -/
theorem coevaluation_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D)) :
    sourcePairing D (coevaluation D h f).val x.val = f x := by
  classical
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  have he := congrArg f (frame_expansion D hD h x)
  rw [finsum_eq_sum_of_fintype, map_sum] at he
  simp only [map_smul, smul_eq_mul] at he
  rw [coevaluation, finsum_eq_sum_of_fintype]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    projected_dual_pairing D hu]
  simpa only [mul_comm] using he

private theorem projection_basis (D : LatticeData) (h : ℤ) (a : Label D) :
    gradeProjection D h (carrierBasis D a) =
      if energy D a = h then carrierBasis D a else 0 := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext b
  rw [gradeProjection_coeff]
  have hc : carrierCoeffEquiv D (carrierBasis D a) = Finsupp.single a 1 :=
    (carrierBasis D).repr_self a
  split_ifs <;> simp_all [hc, Finsupp.single_apply]
  all_goals
    intro hab
    subst b
    contradiction

private theorem theta_projection (D : LatticeData) (h : ℤ) (v : Carrier D) :
    theta D (gradeProjection D h v) = gradeProjection D h (theta D v) := by
  classical
  have heq : (thetaLinear D).comp (gradeProjection D h) =
      (gradeProjection D h).comp (thetaLinear D) := by
    apply (carrierBasis D).ext
    intro a
    have ht : thetaLinear D (carrierBasis D a) =
        ((-1 : ℂ) ^ (occurrences D a.2).length) •
          carrierBasis D (-a.1, a.2) := by
      simp only [carrierBasis_apply, theta_single, sigma_monomial, Finsupp.smul_single]
    have he : energy D (-a.1, a.2) = energy D a := by
      unfold energy chargeEnergy
      rw [bilinear_neg_neg]
    simp only [LinearMap.comp_apply, projection_basis, ht, map_smul, he]
    split_ifs <;> simp only [ht, map_zero, smul_zero]
  exact LinearMap.congr_fun heq v

private def gradeOrderEquiv (D : LatticeData) (h : ℤ) :
    FixedGradedDuality.FixedGrade D h ≃ₗ[ℂ] ↥(grade D h ⊓ fixedSpace D) where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coevaluation_eq_of_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y) :
    x = coevaluation D h f := by
  let e := gradeOrderEquiv D h
  have nd := FixedGradedDuality.fixedGradeNondegenerate D (sourcePairing D)
    (sourcePairing_nondegenerate D hu) (theta_projection D) (sourcePairing_theta D)
    (fun m n u v hu hv hmn => sourcePairing_grade D m n hmn u v hu hv) hD h
  apply e.symm.injective
  apply sub_eq_zero.mp
  apply nd.1
  intro y
  change sourcePairing D (x.val - (coevaluation D h f).val) (e y).val = 0
  rw [map_sub, LinearMap.sub_apply, hx, coevaluation_pairing D hu hD, sub_self]

/-- The finite coefficient formula for the actual original-pairing inverse.
The input x can be the existing dual equivalence's inverse, using its evaluation
law for hx. No new existence or uniqueness structure is introduced. -/
theorem inverse_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f g : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y) :
    g x = ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) * g (fixedDualFrame D h a) := by
  classical
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  rw [coevaluation_eq_of_pairing D hu hD h f x hx, coevaluation,
    finsum_eq_sum_of_fintype, map_sum, finsum_eq_sum_of_fintype]
  simp only [map_smul, smul_eq_mul]

open private left_grade_projection_pairing pairing_plusPart_right_of_fixed_left from
  D5.S3.VertexAlgebra.Lattice.FixedGradedDuality

private theorem coevaluation_unprojected (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    (coevaluation D h f).val =
      ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) • dualCarrierBasis D a.val := by
  classical
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate D hu).1
  intro v
  let pv : grade D h := ⟨gradeProjection D h v, gradeProjection_mem D h v⟩
  have hr := left_grade_projection_pairing D (sourcePairing D)
    (fun m n u v hu hv hmn => sourcePairing_grade D m n hmn u v hu hv)
    h (coevaluation D h f).val (coevaluation D h f).property.1 v
  have hp := pairing_plusPart_right_of_fixed_left D (sourcePairing D)
    (sourcePairing_theta D) (coevaluation D h f).val
    (coevaluation D h f).property.2 pv.val
  have he := coevaluation_pairing D hu hD h f (projectGrade D h pv)
  have hv : sourcePairing D (coevaluation D h f).val v = f (projectGrade D h pv) := by
    exact hr.symm.trans (hp.symm.trans he)
  have hs := congrArg f (frame_project_expansion D hD h pv)
  rw [finsum_eq_sum_of_fintype, map_sum] at hs
  simp only [map_smul, smul_eq_mul] at hs
  have hc (a : EnergyFiber D h) :
      carrierCoeffEquiv D pv.val a.val = carrierCoeffEquiv D v a.val := by
    exact (gradeProjection_coeff D h v a.val).trans (if_pos a.property)
  simp only [hc] at hs
  rw [map_sub, LinearMap.sub_apply, hv, finsum_eq_sum_of_fintype]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, dualCarrierBasis_pairing D hu]
  rw [← hs]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

/-- Single-half-average expansion of the original projected kernel.
Both scalar tests are on the original carrier. The fixed-grade inverse can be
supplied by the existing pairing equivalence through hx. -/
theorem inverse_contraction_half_average (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f g : Module.Dual ℂ (Carrier D)) (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y.val) :
    g x.val = (2 : ℂ)⁻¹ * ∑ᶠ a : EnergyFiber D h,
      (f (carrierBasis D a.val) + f (theta D (carrierBasis D a.val))) *
        g (dualCarrierBasis D a.val) := by
  classical
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  let F := f.comp (grade D h ⊓ fixedSpace D).subtype
  rw [coevaluation_eq_of_pairing D hu hD h F x hx, coevaluation_unprojected D hu hD]
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change f (plusPart D (carrierBasis D a.val)) * g (dualCarrierBasis D a.val) = _
  rw [plusPart, map_smul, map_add]
  simp only [smul_eq_mul]
  ring

/-- Negative signed energies have no labels; no toNat truncation is used. -/
theorem coevaluation_negative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) (hh : h < 0)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    coevaluation D h f = 0 := by
  haveI : IsEmpty (EnergyFiber D h) := ⟨by
    intro a
    have hq := chargeEnergy_nonneg D hD a.val.1
    have he := a.property
    dsimp [energy] at he
    omega⟩
  exact finsum_of_isEmpty _

/-- The grade-zero frame is the genuine original vacuum. -/
def gradeVacuum (D : LatticeData) : ↥(grade D 0 ⊓ fixedSpace D) :=
  ⟨vacuum D, by
    constructor
    · change vacuum D ∈ grade D 0
      simpa [carrierBasis_apply, vacuum] using
        basis_mem_grade D 0 ⟨(0,0), by simp [energy, oscillatorEnergy]⟩
    · exact (mem_fixedSpace D _).mpr (theta_vacuum D)⟩

/-- The zero-energy coevaluation keeps the vacuum coefficient. -/
theorem coevaluation_vacuum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (f : Module.Dual ℂ ↥(grade D 0 ⊓ fixedSpace D)) :
    coevaluation D 0 f = f (gradeVacuum D) • gradeVacuum D := by
  classical
  letI := energyFiber_finite D hD 0
  letI := Fintype.ofFinite (EnergyFiber D 0)
  let a0 : EnergyFiber D 0 := ⟨(0,0), by simp [energy, oscillatorEnergy]⟩
  have hall (a : EnergyFiber D 0) : a = a0 := by
    apply Subtype.ext
    exact (energy_eq_zero_iff D hD a.val).mp a.property
  have hp : plusPart D (vacuum D) = vacuum D := by
    rw [plusPart, theta_vacuum, ← two_smul ℂ (vacuum D), smul_smul]
    norm_num
  have hf : fixedFrame D 0 a0 = gradeVacuum D := by
    apply Subtype.ext
    change plusPart D (carrierBasis D (0,0)) = vacuum D
    simpa [carrierBasis_apply, vacuum] using hp
  have hd : fixedDualFrame D 0 a0 = gradeVacuum D := by
    apply Subtype.ext
    change plusPart D (dualCarrierBasis D (0,0)) = vacuum D
    have hb : dualCarrierBasis D (0,0) = vacuum D := by
      simp [dualCarrierBasis, dualOscillatorMonomial, FactorialFockMetric.weight,
        inverseOscillator, vacuum]
    rw [hb, hp]
  rw [coevaluation, finsum_eq_sum_of_fintype, Finset.sum_eq_single a0]
  · rw [hf, hd]
  · intro b hb hne
    exact (hne (hall b)).elim
  · simp

/-- The signed native contraction has an actual zero branch and an actual
vacuum branch before its positive-energy finite-frame expansion. -/
theorem inverse_contraction_signed (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (g : Module.Dual ℂ (Carrier D)) (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y) :
    g x.val = if hh : h < 0 then 0 else if hz : h = 0 then
      f (hz.symm ▸ gradeVacuum D) * g (vacuum D) else
      ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) * g (fixedDualFrame D h a).val := by
  by_cases hh : h < 0
  · rw [dif_pos hh, coevaluation_eq_of_pairing D hu hD h f x hx,
      coevaluation_negative D hD h hh]
    exact g.map_zero
  · rw [dif_neg hh]
    by_cases hz : h = 0
    · subst h
      rw [dif_pos rfl, coevaluation_eq_of_pairing D hu hD 0 f x hx,
        coevaluation_vacuum D hD, Submodule.coe_smul, map_smul]
      rfl
    · rw [dif_neg hz]
      exact inverse_contraction D hu hD h f
        (g.comp (grade D h ⊓ fixedSpace D).subtype) x hx

#print axioms dualCarrierBasis_pairing
#print axioms dualCarrierBasis_mem_grade
#print axioms coevaluation_pairing
#print axioms inverse_contraction
#print axioms inverse_contraction_half_average
#print axioms coevaluation_negative
#print axioms inverse_contraction_signed
#print axioms coevaluation_vacuum

end D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
