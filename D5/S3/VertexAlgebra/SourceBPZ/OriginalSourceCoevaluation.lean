/- GID: D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse, mathlib/module/Mathlib.Algebra.BigOperators.Finprod]
   utility: none
   digest: Explicit inverse integer Gram occupation coefficients and the projected finite coevaluation on the full original fixed energy grades. -/

import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import Mathlib.Algebra.BigOperators.Finprod

/-!
The inverse is the literal same-mode substitution by -(k+1)^{-1} G^{-1},
with every occupation factorial and opposite charge. Its coefficient extraction
is proved from the original retuned Wick form. The redundant projected frame
then represents every functional on grade D h intersect fixedSpace D.
The grade h is an arbitrary integer; the restricted dual is never identified
with the source. No source BPZ, field action compatibility or crossing is assumed.

The finite inverse-form construction is classical Wick/Fock linear algebra.
Existing factorial, substitution, reflection and energy results are reused at
their original owners. Mathlib material retains its Apache-2.0 attribution.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticePositiveEnergy LatticeInvolution
open MvPolynomial OriginalSourcePairing SourcePairingLaws

private def integerMatrix (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (-((k : ℂ) + 1)) • gramComplex D

private def inverseMatrix (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (-((k : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹

/-- Actual inverse of the negative INTEGER-frequency Gram substitution. -/
def inverseOscillator (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitution (inverseMatrix D)

/-- Every occupation factorial is present, including the empty product. -/
def dualOscillatorMonomial (D : LatticeData) (a : Exponent D) : Oscillator D :=
  (FactorialFockMetric.weight a : ℂ)⁻¹ •
    inverseOscillator D (monomial a 1)

/-- Opposite charge in the full original finite-support carrier. -/
def dualCarrierBasis (D : LatticeData) (a : Label D) : Carrier D :=
  Finsupp.single (-a.1) (dualOscillatorMonomial D a.2)

private theorem integer_matrix_retuning (D : LatticeData) (k : ℕ) :
    SignedOscillatorWick.modeMatrix D k * retuneMatrix D k = integerMatrix D k := by
  rw [SignedOscillatorWick.modeMatrix, retuneMatrix, mul_smul_comm,
    Matrix.mul_one, smul_smul, mul_neg, integerScale_mul_frequency]
  rfl

private theorem integerWick_substitution (D : LatticeData) (p q : Oscillator D) :
    integerWick D p q = SignedOscillatorWick.FactorialBilinear.form (Index D)
      (OriginalCurrentMetric.substitution (integerMatrix D) p) q := by
  change SignedOscillatorWick.FactorialBilinear.form (Index D)
    (((OriginalCurrentMetric.substitution (SignedOscillatorWick.modeMatrix D)).comp
      (OriginalCurrentMetric.substitution (retuneMatrix D))) p) q = _
  rw [OriginalCurrentMetric.substitution_comp]
  simp only [integer_matrix_retuning]

private theorem integer_matrix_inverse (D : LatticeData) (hu : IsUnit D.G.det)
    (k : ℕ) : integerMatrix D k * inverseMatrix D k = 1 := by
  have hk : -((k : ℂ) + 1) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (show k + 1 ≠ 0 by omega)
  rw [integerMatrix, inverseMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_inv_cancel₀ hk, one_smul,
    Matrix.mul_nonsing_inv _ (SignedOscillatorWick.complex_det_unit D hu)]

private theorem integer_substitution_inverse (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Oscillator D) :
    OriginalCurrentMetric.substitution (integerMatrix D) (inverseOscillator D p) = p := by
  change ((OriginalCurrentMetric.substitution (integerMatrix D)).comp
    (OriginalCurrentMetric.substitution (inverseMatrix D))) p = p
  rw [OriginalCurrentMetric.substitution_inverse _ _ (integer_matrix_inverse D hu)]
  rfl

private theorem dualOscillatorMonomial_pairing (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Exponent D) (p : Oscillator D) :
    integerWick D (dualOscillatorMonomial D a) p = p.coeff a := by
  have hw : (FactorialFockMetric.weight a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (FactorialFockMetric.weight_pos a))
  rw [integerWick_substitution, dualOscillatorMonomial, map_smul,
    integer_substitution_inverse D hu, map_smul, LinearMap.smul_apply,
    SignedOscillatorWick.FactorialBilinear.monomial_left, mul_one]
  change (FactorialFockMetric.weight a : ℂ)⁻¹ *
    ((FactorialFockMetric.weight a : ℂ) * p.coeff a) = p.coeff a
  rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- The prescribed negative inverse Gram/factorial vector extracts the ACTUAL
charge/occupation coefficient of every original source state. -/
theorem dualCarrierBasis_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Label D) (v : Carrier D) :
    sourcePairing D (dualCarrierBasis D a) v = carrierCoeffEquiv D v a := by
  rw [dualCarrierBasis, sourcePairing_single, neg_neg,
    dualOscillatorMonomial_pairing D hu]
  rfl

private theorem weight_eq_energy (D : LatticeData) (a : Exponent D) :
    Finsupp.weight (fun x : Index D => (x.2 : ℤ) + 1) a =
      (oscillatorEnergy a : ℤ) := by
  simp [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_add]

private theorem chargeEnergy_neg (D : LatticeData) (q : Charge D) :
    chargeEnergy D (-q) = chargeEnergy D q := by
  rw [chargeEnergy, chargeEnergy, bilinear_neg_neg]

/-- Mode-preserving inverse substitution preserves the full signed energy.
This support statement needs neither determinant invertibility nor positivity. -/
theorem dualCarrierBasis_mem_grade (D : LatticeData) (a : Label D) :
    dualCarrierBasis D a ∈ grade D (energy D a) := by
  classical
  have hw := substitution_monomial_weight D (inverseMatrix D) a.2 1
  have hd : IsWeightedHomogeneous (fun x : Index D => (x.2 : ℤ) + 1)
      (dualOscillatorMonomial D a.2)
      (Finsupp.weight (fun x : Index D => (x.2 : ℤ) + 1) a.2) :=
    (weightedHomogeneousSubmodule ℂ _ _).smul_mem _ hw
  rw [mem_grade_iff]
  rintro ⟨q, b⟩ hb
  by_cases hq : -a.1 = q
  · subst q
    simp only [dualCarrierBasis, Finsupp.single_eq_same]
    apply hd.coeff_eq_zero b
    rw [weight_eq_energy, weight_eq_energy]
    intro he
    apply hb
    simp only [energy, chargeEnergy_neg]
    exact congrArg (fun n : ℤ => chargeEnergy D a.1 + n) he
  · simp [dualCarrierBasis, Finsupp.single_apply, hq]

private theorem carrierBasis_mem_grade (D : LatticeData) (a : Label D) :
    carrierBasis D a ∈ grade D (energy D a) := by
  rw [grade_eq_span]
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

private theorem theta_mem_grade (D : LatticeData) (h : ℤ) (v : Carrier D)
    (hv : v ∈ grade D h) : theta D v ∈ grade D h := by
  rw [grade_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    have ha' : energy D a = h := ha
    have ht : theta D (carrierBasis D a) =
        ((-1 : ℂ) ^ (LatticeAllStateField.occurrences D a.2).length) •
          carrierBasis D (-a.1, a.2) := by
      simp only [carrierBasis_apply]
      change thetaLinear D (Finsupp.single a.1 (monomial a.2 1)) = _
      rw [theta_single, sigma_monomial, ← Finsupp.smul_single]
    rw [ht]
    apply (grade D h).smul_mem
    have he : energy D (-a.1, a.2) = h := by
      simpa only [energy, chargeEnergy_neg] using ha'
    rw [← he]
    exact carrierBasis_mem_grade D _
  | zero => simpa using (grade D h).zero_mem
  | add v w hv hw ihv ihw =>
    rw [map_add]
    exact (grade D h).add_mem ihv ihw
  | smul c v hv ih =>
    rw [map_smul]
    exact (grade D h).smul_mem c ih

private def plusLinear (D : LatticeData) : Module.End ℂ (Carrier D) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + thetaLinear D)

private theorem plusPart_mem_grade (D : LatticeData) (h : ℤ) (v : Carrier D)
    (hv : v ∈ grade D h) : plusPart D v ∈ grade D h :=
  (grade D h).smul_mem _ ((grade D h).add_mem hv (theta_mem_grade D h v hv))

private theorem plusPart_eq_self (D : LatticeData) (v : Carrier D)
    (hv : v ∈ fixedSpace D) : plusPart D v = v := by
  rw [plusPart, (mem_fixedSpace D v).mp hv, ← two_smul ℂ v, smul_smul]
  norm_num

private theorem plusPart_self_adjoint (D : LatticeData) (u v : Carrier D) :
    sourcePairing D (plusPart D u) v = sourcePairing D u (plusPart D v) := by
  have ht := sourcePairing_theta D u (theta D v)
  have hi : theta D (theta D v) = v := theta_involutive D v
  rw [hi] at ht
  simp only [plusPart, map_smul, map_add, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [ht]

/-- A redundant projected frame in the full actual fixed grade. -/
def fixedFrame (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    ↥(grade D h ⊓ fixedSpace D) :=
  ⟨plusPart D (carrierBasis D a.1),
    ⟨plusPart_mem_grade D h _ (by
      simpa only [a.property] using carrierBasis_mem_grade D a.val),
     FixedGradedDuality.plusPart_mem_fixedSpace D _⟩⟩

/-- Project the explicit opposite-charge inverse vector, using the existing half. -/
def fixedDualFrame (D : LatticeData) (h : ℤ) (a : EnergyFiber D h) :
    ↥(grade D h ⊓ fixedSpace D) :=
  ⟨plusPart D (dualCarrierBasis D a.1),
    ⟨plusPart_mem_grade D h _ (by
      simpa only [a.property] using dualCarrierBasis_mem_grade D a.val),
     FixedGradedDuality.plusPart_mem_fixedSpace D _⟩⟩

private theorem fixedDualFrame_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : EnergyFiber D h) (x : ↥(grade D h ⊓ fixedSpace D)) :
    sourcePairing D (fixedDualFrame D h a).val x.val =
      carrierCoeffEquiv D x.val a.1 := by
  change sourcePairing D (plusPart D (dualCarrierBasis D a.1)) x.val = _
  rw [plusPart_self_adjoint, plusPart_eq_self D x.val x.property.2,
    dualCarrierBasis_pairing D hu]

private theorem grade_expansion (D : LatticeData) (h : ℤ)
    [Fintype (EnergyFiber D h)] (x : ↥(grade D h)) :
    (∑ a : EnergyFiber D h,
      carrierCoeffEquiv D x.val a.1 • carrierBasis D a.1) = x.val := by
  classical
  have hb (a : Label D) : carrierCoeffEquiv D (carrierBasis D a) =
      Finsupp.single a 1 := (carrierBasis D).repr_self a
  apply (carrierCoeffEquiv D).injective
  ext b
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, hb,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases he : energy D b = h
  · let a : EnergyFiber D h := ⟨b, he⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro c hc hca
      have hcb : c.val ≠ b := by
        intro hh
        exact hca (Subtype.ext hh)
      simp [hcb]
    · simp
  · have hz : carrierCoeffEquiv D x.val b = 0 :=
      (mem_grade_iff D h x.val).mp x.property b he
    rw [hz]
    apply Finset.sum_eq_zero
    intro a ha
    have hab : a.val ≠ b := by
      intro hh
      exact he (hh ▸ a.property)
    simp [hab]

private theorem fixedFrame_expansion (D : LatticeData) (h : ℤ)
    [Fintype (EnergyFiber D h)] (x : ↥(grade D h ⊓ fixedSpace D)) :
    (∑ a : EnergyFiber D h,
      carrierCoeffEquiv D x.val a.1 • fixedFrame D h a) = x := by
  apply Subtype.ext
  change (grade D h ⊓ fixedSpace D).subtype
    (∑ a : EnergyFiber D h,
      carrierCoeffEquiv D x.val a.1 • fixedFrame D h a) = x.val
  rw [map_sum]
  simp only [map_smul]
  change (∑ a : EnergyFiber D h,
    carrierCoeffEquiv D x.val a.1 • plusLinear D (carrierBasis D a.1)) = x.val
  calc
    _ = plusLinear D (∑ a : EnergyFiber D h,
        carrierCoeffEquiv D x.val a.1 • carrierBasis D a.1) := by
      simp only [map_sum, map_smul]
    _ = plusPart D x.val := congrArg (plusLinear D)
      (grade_expansion D h ⟨x.val, x.property.1⟩)
    _ = x.val := plusPart_eq_self D x.val x.property.2

/-- The prescribed finite coevaluation, not a choice from abstract perfection.
The finite energy fiber follows from real positive definiteness only here. -/
def representFixedGrade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D) →ₗ[ℂ]
      ↥(grade D h ⊓ fixedSpace D) := by
  classical
  letI : Finite (EnergyFiber D h) := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  exact
    { toFun := fun f => ∑ᶠ a : EnergyFiber D h,
        f (fixedFrame D h a) • fixedDualFrame D h a
      map_add' := by
        intro f g
        simp only [finsum_eq_sum_of_fintype, LinearMap.add_apply,
          add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [finsum_eq_sum_of_fintype, LinearMap.smul_apply,
          smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul] }

/-- Every functional on the actual fixed integer grade has exactly this
explicit Q representative; the two carriers remain distinct types. -/
theorem representFixedGrade_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D)) :
    sourcePairing D (representFixedGrade D hD h f).val x.val = f x := by
  classical
  letI : Finite (EnergyFiber D h) := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  change sourcePairing D ((grade D h ⊓ fixedSpace D).subtype
    (∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) • fixedDualFrame D h a)) x.val = _
  rw [finsum_eq_sum_of_fintype, map_sum]
  change ((sourcePairing D).flip x.val)
    (∑ a : EnergyFiber D h,
      f (fixedFrame D h a) • (fixedDualFrame D h a).val) = f x
  rw [map_sum]
  simp only [map_smul, LinearMap.flip_apply, smul_eq_mul]
  calc
    (∑ a : EnergyFiber D h,
        f (fixedFrame D h a) * sourcePairing D (fixedDualFrame D h a).val x.val) =
      ∑ a : EnergyFiber D h,
        carrierCoeffEquiv D x.val a.1 * f (fixedFrame D h a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [fixedDualFrame_pairing D hu]
      exact mul_comm (f (fixedFrame D h a)) (carrierCoeffEquiv D x.val a.1)
    _ = f (∑ a : EnergyFiber D h,
        carrierCoeffEquiv D x.val a.1 • fixedFrame D h a) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = f x := congrArg f (fixedFrame_expansion D h x)

/-- Uniqueness is tested by the actual projected inverse vectors, without
assuming a restricted nondegeneracy or coevaluation law. -/
theorem representFixedGrade_unique (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y) :
    x = representFixedGrade D hD h f := by
  apply Subtype.ext
  apply (carrierCoeffEquiv D).injective
  ext a
  by_cases ha : energy D a = h
  · let b : EnergyFiber D h := ⟨a, ha⟩
    have hleft := hx (fixedDualFrame D h b)
    have hright := representFixedGrade_pairing D hu hD h f (fixedDualFrame D h b)
    rw [sourcePairing_symmetric, fixedDualFrame_pairing D hu] at hleft hright
    exact hleft.trans hright.symm
  · have hleft : carrierCoeffEquiv D x.val a = 0 :=
      (mem_grade_iff D h x.val).mp x.property.1 a ha
    have hright : carrierCoeffEquiv D (representFixedGrade D hD h f).val a = 0 :=
      (mem_grade_iff D h _).mp (representFixedGrade D hD h f).property.1 a ha
    exact hleft.trans hright.symm

/-- Finite scalar pair exchange for the explicit inverse of the original Q.
This does not move any field mode through Q. -/
theorem fixed_contraction_comm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f g : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    (∑ᶠ a : EnergyFiber D h,
      f (fixedFrame D h a) * g (fixedDualFrame D h a)) =
    (∑ᶠ a : EnergyFiber D h,
      g (fixedFrame D h a) * f (fixedDualFrame D h a)) := by
  classical
  letI : Finite (EnergyFiber D h) := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  have eval (u v : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
      v (representFixedGrade D hD h u) =
        ∑ᶠ a : EnergyFiber D h, u (fixedFrame D h a) * v (fixedDualFrame D h a) := by
    change v (∑ᶠ a : EnergyFiber D h, u (fixedFrame D h a) • fixedDualFrame D h a) = _
    simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]
  rw [← eval f g, ← eval g f,
    ← representFixedGrade_pairing D hu hD h g (representFixedGrade D hD h f),
    sourcePairing_symmetric,
    representFixedGrade_pairing D hu hD h f (representFixedGrade D hD h g)]

#print axioms dualCarrierBasis_pairing
#print axioms dualCarrierBasis_mem_grade
#print axioms representFixedGrade_pairing
#print axioms representFixedGrade_unique
#print axioms fixed_contraction_comm

end D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
