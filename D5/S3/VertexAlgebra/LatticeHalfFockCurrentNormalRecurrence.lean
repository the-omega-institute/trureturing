/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormalRecurrence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentNormalRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Statewise finite half-current contractions in native normal insertions. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField
open scoped BigOperators TensorProduct

noncomputable section

private def insertionTerm (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) (mode : ℤ) :=
  flatTerm D hu field [index] exponent vector (mode, ())

private theorem insertionTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (insertionTerm D hu index field exponent vector) :=
  (flatTerm_finite D hu field [index] exponent vector).comp_of_injective
    (show Function.Injective (fun mode : ℤ => (mode, ())) from by
      intro first second equality
      exact congrArg Prod.fst equality)

def coverShift (D : LatticeData) (hu : IsUnit D.G.det) (shift : ℤ)
    (field : NativeField D hu) : NativeField D hu :=
  HVertexOperator.of_coeff (fun exponent => field.coeff (exponent + shift)) (by
    intro vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨((HahnModule.of ℂ).symm (field vector)).order - shift, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    change ((HahnModule.of ℂ).symm (field vector)).coeff (exponent + shift) = 0
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega))

theorem normalInsertion_coverShift (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (shift : ℤ) :
    normalInsertion D hu index (coverShift D hu shift field) =
      coverShift D hu shift (normalInsertion D hu index field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [coverShift, HVertexOperator.coeff_of_coeff]
  rw [normalInsertion_integer_modes, normalInsertion_integer_modes]
  apply finsum_congr
  intro mode
  simp only [flatTerm, flatCoefficient, coverShift, HVertexOperator.coeff_of_coeff]
  have shifted : exponent + 2 * mode + 2 * (index.2 : ℤ) + 3 + shift =
      exponent + shift + 2 * mode + 2 * (index.2 : ℤ) + 3 := by omega
  rw [shifted]

def normalInsertionLinear (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) :
    NativeField D hu →ₗ[ℂ] NativeField D hu where
  toFun := normalInsertion D hu index
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    change (normalInsertion D hu index (first + second)).coeff exponent vector =
      (normalInsertion D hu index first).coeff exponent vector +
        (normalInsertion D hu index second).coeff exponent vector
    rw [normalInsertion_integer_modes, normalInsertion_integer_modes,
      normalInsertion_integer_modes]
    have terms : insertionTerm D hu index (first + second) exponent vector =
        fun mode => insertionTerm D hu index first exponent vector mode +
          insertionTerm D hu index second exponent vector mode := by
      funext mode
      simp only [insertionTerm, flatTerm, flatCoefficient]
      split_ifs <;> simp
    change (∑ᶠ mode : ℤ, insertionTerm D hu index (first + second) exponent vector mode) = _
    rw [terms, finsum_add_distrib (insertionTerm_finite D hu index first exponent vector)
      (insertionTerm_finite D hu index second exponent vector)]
    rfl
  map_smul' scalar field := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    change (normalInsertion D hu index (scalar • field)).coeff exponent vector =
      scalar • (normalInsertion D hu index field).coeff exponent vector
    rw [normalInsertion_integer_modes, normalInsertion_integer_modes]
    have terms : insertionTerm D hu index (scalar • field) exponent vector =
        fun mode => scalar • insertionTerm D hu index field exponent vector mode := by
      funext mode
      simp only [insertionTerm, flatTerm, flatCoefficient]
      split_ifs <;> simp
    change (∑ᶠ mode : ℤ, insertionTerm D hu index (scalar • field) exponent vector mode) = _
    rw [terms]
    simpa only [insertionTerm] using
      (smul_finsum' scalar (insertionTerm_finite D hu index field exponent vector)).symm

private theorem tensorCurrent_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour other : Fin D.rank) (mode currentMode : ℤ) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) other currentMode -
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) other currentMode *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      if mode + currentMode + 1 = 0 then
        (LatticeHalfFock.frequency mode * (D.G colour other : ℂ)) • 1 else 0 := by
  apply TensorProduct.ext'
  intro polynomial ground
  simp only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
    Module.End.mul_apply, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.sub_tmul, LatticeHalfFock.current_heisenberg_apply]
  split_ifs <;> simp [TensorProduct.smul_tmul']

theorem tensorCurrent_jet_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (index : Index D) (mode currentMode : ℤ) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode *
        jetCurrent D hu index currentMode -
      jetCurrent D hu index currentMode *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
      if currentMode = -mode - 1 then
        (LatticeHalfFock.frequency mode * jetScalar index.2 currentMode *
          (D.G colour index.1 : ℂ)) • 1 else 0 := by
  simp only [jetCurrent, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    tensorCurrent_commutator]
  by_cases exceptional : currentMode = -mode - 1
  · simp only [exceptional, show mode + (-mode - 1) + 1 = 0 by omega,
      ite_true, smul_smul]
    congr 1
    ring
  · simp [exceptional, show mode + currentMode + 1 ≠ 0 by omega]

private theorem commutator_mul {Algebra : Type*} [Ring Algebra]
    (current first second : Algebra) :
    current * (first * second) - (first * second) * current =
      (current * first - first * current) * second +
        first * (current * second - second * current) := by
  noncomm_ring

theorem normalInsertion_current_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (mode exponent : ℤ) (index : Index D)
    (field deltaField : NativeField D hu)
    (commutator : ∀ coefficient,
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode * field.coeff coefficient -
        field.coeff coefficient * LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode =
          deltaField.coeff coefficient)
    (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
        ((normalInsertion D hu index field).coeff exponent vector) -
      (normalInsertion D hu index field).coeff exponent
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      (normalInsertion D hu index deltaField).coeff exponent vector +
        (LatticeHalfFock.frequency mode * jetScalar index.2 (-mode - 1) *
          (D.G colour index.1 : ℂ)) •
            field.coeff (exponent - 2 * mode + 2 * index.2 + 1) vector := by
  classical
  let current := LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
  let scalar := LatticeHalfFock.frequency mode * jetScalar index.2 (-mode - 1) *
    (D.G colour index.1 : ℂ)
  let central : ℤ → ActualTensor D hu := fun currentMode =>
    if currentMode = -mode - 1 then
      scalar • field.coeff (exponent - 2 * mode + 2 * index.2 + 1) vector else 0
  have commonFinite : Set.Finite
      (Function.support (insertionTerm D hu index field exponent vector) ∪
        Function.support (insertionTerm D hu index field exponent (current vector)) ∪
          Function.support (insertionTerm D hu index deltaField exponent vector)) :=
    ((insertionTerm_finite D hu index field exponent vector).union
      (insertionTerm_finite D hu index field exponent (current vector))).union
        (insertionTerm_finite D hu index deltaField exponent vector)
  have fieldFinite : Function.HasFiniteSupport (insertionTerm D hu index field exponent vector) :=
    commonFinite.subset (by intro currentMode member; exact Or.inl (Or.inl member))
  have currentFinite :
      Function.HasFiniteSupport (insertionTerm D hu index field exponent (current vector)) :=
    commonFinite.subset (by intro currentMode member; exact Or.inl (Or.inr member))
  have deltaFinite : Function.HasFiniteSupport (insertionTerm D hu index deltaField exponent vector) :=
    commonFinite.subset (by intro currentMode member; exact Or.inr member)
  have centralFinite : Function.HasFiniteSupport central := by
    apply ({-mode - 1} : Finset ℤ).finite_toSet.subset
    intro currentMode member
    by_contra outside
    apply member
    simp only [Finset.mem_coe, Finset.mem_singleton] at outside
    simp [central, outside]
  have terms (currentMode : ℤ) :
      current (insertionTerm D hu index field exponent vector currentMode) -
        insertionTerm D hu index field exponent (current vector) currentMode =
      insertionTerm D hu index deltaField exponent vector currentMode + central currentMode := by
    have operator : current * flatCoefficient D hu field [index] (currentMode, ()) exponent -
        flatCoefficient D hu field [index] (currentMode, ()) exponent * current =
      flatCoefficient D hu deltaField [index] (currentMode, ()) exponent +
        if currentMode = -mode - 1 then
          scalar • field.coeff (exponent - 2 * mode + 2 * index.2 + 1) else 0 := by
      simp only [flatCoefficient]
      by_cases negative : currentMode < 0
      · rw [if_pos negative, if_pos negative]
        calc
          _ = (current * jetCurrent D hu index currentMode -
              jetCurrent D hu index currentMode * current) * field.coeff _ +
            jetCurrent D hu index currentMode * (current * field.coeff _ -
              field.coeff _ * current) := commutator_mul _ _ _
          _ = _ := by
            rw [show current = LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
              from rfl, tensorCurrent_jet_commutator, commutator]
            by_cases exceptional : currentMode = -mode - 1
            · subst currentMode
              rw [show
                exponent + 2 * (-mode - 1) + 2 * (index.2 : ℤ) + 3 =
                  exponent - 2 * mode + 2 * index.2 + 1 by omega]
              simp only [ite_true, smul_mul_assoc, one_mul, scalar]
              exact add_comm _ _
            · simp only [if_neg exceptional, zero_mul, zero_add, add_zero]
      · rw [if_neg negative, if_neg negative]
        calc
          _ = (current * field.coeff _ - field.coeff _ * current) *
              jetCurrent D hu index currentMode + field.coeff _ *
            (current * jetCurrent D hu index currentMode -
              jetCurrent D hu index currentMode * current) := commutator_mul _ _ _
          _ = _ := by
            rw [show current = LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
              from rfl, tensorCurrent_jet_commutator, commutator]
            by_cases exceptional : currentMode = -mode - 1
            · subst currentMode
              rw [show
                exponent + 2 * (-mode - 1) + 2 * (index.2 : ℤ) + 3 =
                  exponent - 2 * mode + 2 * index.2 + 1 by omega]
              simp only [ite_true, mul_smul_comm, mul_one, scalar]
            · simp only [if_neg exceptional, mul_zero, zero_add, add_zero]
    by_cases exceptional : currentMode = -mode - 1
    · simpa only [insertionTerm, flatTerm, central, if_pos exceptional,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply] using congrArg
        (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector) operator
    · simpa only [insertionTerm, flatTerm, central, if_neg exceptional,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.zero_apply] using congrArg
        (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector) operator
  rw [normalInsertion_integer_modes, normalInsertion_integer_modes,
    normalInsertion_integer_modes]
  change current (∑ᶠ currentMode : ℤ, insertionTerm D hu index field exponent vector currentMode) -
    (∑ᶠ currentMode : ℤ, insertionTerm D hu index field exponent (current vector) currentMode) =
      (∑ᶠ currentMode : ℤ, insertionTerm D hu index deltaField exponent vector currentMode) +
        scalar • field.coeff (exponent - 2 * mode + 2 * index.2 + 1) vector
  have mapped : current (∑ᶠ currentMode : ℤ,
        insertionTerm D hu index field exponent vector currentMode) =
      ∑ᶠ currentMode : ℤ, current (insertionTerm D hu index field exponent vector currentMode) :=
    current.toAddMonoidHom.map_finsum fieldFinite
  rw [mapped,
    ← finsum_sub_distrib
      (fieldFinite.fun_comp (map_zero current)) currentFinite]
  simp_rw [terms]
  rw [finsum_add_distrib deltaFinite centralFinite]
  congr 1
  rw [finsum_eq_single _ (-mode - 1)]
  · simp [central, scalar]
  · intro currentMode outside
    simp [central, outside]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentNormalRecurrence
