/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTranslationCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical differentiation of native creation coefficients and normal insertions. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection MvPolynomial
open scoped BigOperators

noncomputable section

private theorem jet_successor (order : ℕ) (mode : ℤ) :
    (order + 1 : ℂ) * jetScalar (order + 1) mode =
      (-(mode : ℂ) - 3 / 2 - (order : ℂ)) * jetScalar order mode := by
  have factorial : (order.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero order
  have successor : (order + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero order
  unfold jetScalar
  rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

def physicalDerivative (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) : NativeField D hu :=
  HVertexOperator.of_coeff
    (fun exponent => ((((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2))) (by
      intro vector
      apply Set.IsWF.isPWO
      apply BddBelow.isWF
      refine ⟨((HahnModule.of ℂ).symm (field vector)).order - 2, ?_⟩
      intro exponent member
      by_contra outside
      have zero : field.coeff (exponent + 2) vector = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (by omega)
      apply member
      change ((((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2) vector) = 0
      rw [zero, smul_zero])

private theorem negative_derivative_term (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (exponent : ℤ)
    (vector : ActualTensor D hu) (offset : ℕ) :
    ((((exponent + 2 : ℤ) : ℂ) / 2) •
        negativeTerm D hu index field (exponent + 2) vector offset) =
      (index.2 + 1 : ℂ) •
          negativeTerm D hu (index.1, index.2 + 1) field exponent vector offset +
        negativeTerm D hu index (physicalDerivative D hu field) exponent vector offset := by
  simp only [negativeTerm, physicalDerivative, HVertexOperator.coeff_of_coeff,
    LinearMap.smul_apply, map_smul, smul_smul, Nat.cast_add, Nat.cast_one]
  rw [show exponent - 2 * offset + 2 * ((index.2 : ℤ) + 1) + 1 =
      exponent + 2 - 2 * offset + 2 * index.2 + 1 by omega,
    show exponent - 2 * offset + 2 * index.2 + 1 + 2 =
      exponent + 2 - 2 * offset + 2 * index.2 + 1 by omega]
  rw [← add_smul, jet_successor]
  congr 1
  push_cast
  ring

private theorem positive_derivative_term (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (exponent : ℤ)
    (vector : ActualTensor D hu) (offset : ℕ) :
    ((((exponent + 2 : ℤ) : ℂ) / 2) •
        positiveTerm D hu index field (exponent + 2) vector offset) =
      (index.2 + 1 : ℂ) •
          positiveTerm D hu (index.1, index.2 + 1) field exponent vector offset +
        positiveTerm D hu index (physicalDerivative D hu field) exponent vector offset := by
  simp only [positiveTerm, physicalDerivative, HVertexOperator.coeff_of_coeff,
    LinearMap.smul_apply, map_smul, smul_smul, Nat.cast_add, Nat.cast_one]
  rw [show exponent + 2 * offset + 2 * ((index.2 : ℤ) + 1) + 3 =
      exponent + 2 + 2 * offset + 2 * index.2 + 3 by omega,
    show exponent + 2 * offset + 2 * index.2 + 3 + 2 =
      exponent + 2 + 2 * offset + 2 * index.2 + 3 by omega]
  rw [← add_smul, jet_successor]
  congr 1
  push_cast
  ring

theorem normalInsertion_physical_derivative (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) :
    physicalDerivative D hu (normalInsertion D hu index field) =
      (index.2 + 1 : ℂ) • normalInsertion D hu (index.1, index.2 + 1) field +
        normalInsertion D hu index (physicalDerivative D hu field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    physicalDerivative, normalInsertion, HVertexOperator.coeff_of_coeff,
    normalCoefficient, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.add_apply, smul_add]
  rw [smul_finsum' _ (negativeTerm_finite D hu index field (exponent + 2) vector),
    smul_finsum' _ (positiveTerm_finite D hu index field (exponent + 2) vector)]
  have negative := funext (negative_derivative_term D hu index field exponent vector)
  have positive := funext (positive_derivative_term D hu index field exponent vector)
  rw [negative, positive,
    finsum_add_distrib
      ((negativeTerm_finite D hu (index.1, index.2 + 1) field exponent vector).fun_comp
        (smul_zero (index.2 + 1 : ℂ)))
      (negativeTerm_finite D hu index (physicalDerivative D hu field) exponent vector),
    finsum_add_distrib
      ((positiveTerm_finite D hu (index.1, index.2 + 1) field exponent vector).fun_comp
        (smul_zero (index.2 + 1 : ℂ)))
      (positiveTerm_finite D hu index (physicalDerivative D hu field) exponent vector),
    ← smul_finsum' _ (negativeTerm_finite D hu (index.1, index.2 + 1) field exponent vector),
    ← smul_finsum' _ (positiveTerm_finite D hu (index.1, index.2 + 1) field exponent vector)]
  ac_rfl

private theorem singleton_modes_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (fun mode : ℤ =>
      flatTerm D hu field [index] exponent vector (mode, ())) :=
  (flatTerm_finite D hu field [index] exponent vector).comp_of_injective
    (show Function.Injective (fun mode : ℤ => (mode, ())) from by
      intro first second equality
      exact congrArg Prod.fst equality)

def normalInsertionLinear (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) :
    Module.End ℂ (NativeField D hu) where
  toFun := normalInsertion D hu index
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    rw [normalInsertion_integer_modes, normalInsertion_integer_modes,
      normalInsertion_integer_modes,
      ← finsum_add_distrib (singleton_modes_finite D hu index first exponent vector)
        (singleton_modes_finite D hu index second exponent vector)]
    apply finsum_congr
    intro mode
    simp only [flatTerm, flatCoefficient]
    split_ifs <;>
      simp only [Module.End.mul_apply, map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' scalar field := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply]
    rw [normalInsertion_integer_modes, normalInsertion_integer_modes,
      smul_finsum' scalar (singleton_modes_finite D hu index field exponent vector)]
    apply finsum_congr
    intro mode
    simp only [flatTerm, flatCoefficient]
    split_ifs <;>
      simp only [Module.End.mul_apply, map_smul, RingHom.id_apply,
        Pi.smul_apply, LinearMap.smul_apply]

theorem normalSequence_physical_derivative (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (field : NativeField D hu) :
    physicalDerivative D hu (normalSequence D hu field word) =
      ((labelledRemainders D word).map (fun entry =>
        (sourceWeight D entry.1 : ℂ) • normalInsertion D hu (entry.1.1, entry.1.2 + 1)
          (normalSequence D hu field entry.2))).sum +
        normalSequence D hu (physicalDerivative D hu field) word := by
  induction word with
  | nil => simp [normalSequence, labelledRemainders]
  | cons index tail inductionProof =>
    rw [normalSequence, normalInsertion_physical_derivative, inductionProof]
    change (index.2 + 1 : ℂ) • normalInsertion D hu (index.1, index.2 + 1)
        (normalSequence D hu field tail) +
      normalInsertionLinear D hu index
        (((labelledRemainders D tail).map (fun entry =>
          (sourceWeight D entry.1 : ℂ) • normalInsertion D hu (entry.1.1, entry.1.2 + 1)
            (normalSequence D hu field entry.2))).sum +
          normalSequence D hu (physicalDerivative D hu field) tail) = _
    rw [map_add, map_list_sum]
    simp only [labelledRemainders, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_apply, sourceWeight, normalSequence]
    have terms : (labelledRemainders D tail).map (fun entry =>
        normalInsertionLinear D hu index
          ((entry.1.2 + 1 : ℂ) • normalInsertion D hu (entry.1.1, entry.1.2 + 1)
            (normalSequence D hu field entry.2))) =
      (labelledRemainders D tail).map (fun entry =>
        (entry.1.2 + 1 : ℂ) • normalInsertion D hu (entry.1.1, entry.1.2 + 1)
          (normalInsertion D hu index (normalSequence D hu field entry.2))) := by
      apply List.map_congr_left
      intro entry member
      rw [map_smul]
      congr 1
      exact normalInsertion_commute D hu index (entry.1.1, entry.1.2 + 1) _
    simp only [Function.comp_def, normalSequence, Nat.cast_add, Nat.cast_one]
    rw [terms]
    rw [show normalInsertionLinear D hu index
        (normalSequence D hu (physicalDerivative D hu field) tail) =
      normalInsertion D hu index (normalSequence D hu (physicalDerivative D hu field) tail)
        from rfl]
    exact (add_assoc _ _ _).symm

end
end D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus.normalInsertion_physical_derivative
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockTranslationCalculus.normalSequence_physical_derivative
