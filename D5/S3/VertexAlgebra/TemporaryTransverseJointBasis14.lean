import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis13

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def nativeLevel (D : LatticeData) (powers : Index D →₀ ℕ) (subset : Finset ℕ) : ℤ :=
  (Finsupp.weight (frequencyWeight D) powers : ℤ) + polarizedLevel subset

def nativeDegree (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) : ℤ :=
  Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers + epsilonCount subset +
    (thetaCount subset : ℤ) - (etaCount subset : ℤ)

theorem nativeWord_T0 (D : LatticeData)
    (H frame : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (beta : Charge D) (index : NativeIndex D) :
    (M D H 0 + G D 0) (nativeWord D frame beta index) =
      (chosenH D beta + (nativeLevel D index.1 index.2 : ℂ) - 1) • nativeWord D frame beta index := by
  simpa only [nativeWord, nativeLevel, Int.cast_add, Int.cast_natCast, add_assoc] using
    original_total_energy_coordinate_polarized D H frame leftGramInverse rightGramInverse
      beta index.1 1 index.2

theorem nativeWord_aux (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (rightFrameInverse : frame * inverse = 1) (xAxis yAxis : Fin D.rank)
    (beta : Charge D) (index : NativeIndex D) :
    auxiliary D frame inverse xAxis yAxis (nativeWord D frame beta index) =
      (nativeDegree D xAxis yAxis index.1 index.2 : ℂ) • nativeWord D frame beta index := by
  exact original_coordinate_polarized_aux_degree D frame inverse rightFrameInverse
    xAxis yAxis beta index.1 1 index.2

section NativeCoordinates

variable (D : LatticeData)
variable (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D)

theorem nativeCoefficient_sum (subset : Finset (NativeIndex D)) (coefficient : NativeIndex D → ℂ)
    (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta
      (∑ key ∈ subset, coefficient key • nativeWord D frame beta key) index =
      if index ∈ subset then coefficient index else 0 := by
  classical
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    nativeCoefficients_word, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' subset index coefficient

theorem nativeT0_coefficient
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (psi : State D) (sector : chargeProjection D beta psi = psi) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta
      ((M D H 0 + G D 0) psi) index =
      (chosenH D beta + (nativeLevel D index.1 index.2 : ℂ) - 1) *
        nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
  have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
    (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
  have image : (M D H 0 + G D 0) psi = ∑ key ∈ coefficients.support,
      (coefficients key * (chosenH D beta + (nativeLevel D key.1 key.2 : ℂ) - 1)) •
        nativeWord D frame beta key := by
    rw [expansion]
    simp only [map_sum, map_smul, nativeWord_T0 D H frame leftGramInverse rightGramInverse,
      smul_smul]
  rw [image, nativeCoefficient_sum]
  by_cases member : index ∈ coefficients.support
  · simp [member, coefficients, mul_comm]
  · have vanished : coefficients index = 0 := Finsupp.notMem_support_iff.mp member
    simp only [if_neg member]
    change 0 = _ * coefficients index
    rw [vanished, mul_zero]

theorem nativeAux_coefficient (xAxis yAxis : Fin D.rank)
    (psi : State D) (sector : chargeProjection D beta psi = psi) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta
      (auxiliary D frame inverse xAxis yAxis psi) index =
      (nativeDegree D xAxis yAxis index.1 index.2 : ℂ) *
        nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
  have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
    (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
  have image : auxiliary D frame inverse xAxis yAxis psi = ∑ key ∈ coefficients.support,
      (coefficients key * (nativeDegree D xAxis yAxis key.1 key.2 : ℂ)) •
        nativeWord D frame beta key := by
    rw [expansion]
    simp only [map_sum, map_smul, nativeWord_aux D frame inverse rightFrameInverse,
      smul_smul]
  rw [image, nativeCoefficient_sum]
  by_cases member : index ∈ coefficients.support
  · simp [member, coefficients, mul_comm]
  · have vanished : coefficients index = 0 := Finsupp.notMem_support_iff.mp member
    simp only [if_neg member]
    change 0 = _ * coefficients index
    rw [vanished, mul_zero]

theorem nativeT0_support_level
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (level : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index ≠ 0) :
    nativeLevel D index.1 index.2 = level := by
  have evaluated := congrArg
    (fun state => nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index) energy
  rw [nativeT0_coefficient D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse psi sector index] at evaluated
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at evaluated
  have annihilated : ((chosenH D beta + (nativeLevel D index.1 index.2 : ℂ) - 1) -
      (chosenH D beta + (level : ℂ) - 1)) *
      nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index = 0 := by
    rw [sub_mul, evaluated, sub_self]
  have scalarEqual := (mul_eq_zero.mp annihilated).resolve_right nonzero
  have integerCasts : (nativeLevel D index.1 index.2 : ℂ) = (level : ℂ) := by
    linear_combination scalarEqual
  exact_mod_cast integerCasts

theorem nativeAux_support_degree (xAxis yAxis : Fin D.rank)
    (degree : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index ≠ 0) :
    nativeDegree D xAxis yAxis index.1 index.2 = degree := by
  have evaluated := congrArg
    (fun state => nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta state index) homogeneous
  rw [nativeAux_coefficient D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi sector index] at evaluated
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at evaluated
  have annihilated : ((nativeDegree D xAxis yAxis index.1 index.2 : ℂ) - (degree : ℂ)) *
      nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index = 0 := by
    rw [sub_mul, evaluated, sub_self]
  have scalarEqual := (mul_eq_zero.mp annihilated).resolve_right nonzero
  have integerCasts : (nativeDegree D xAxis yAxis index.1 index.2 : ℂ) = (degree : ℂ) :=
    sub_eq_zero.mp scalarEqual
  exact_mod_cast integerCasts

theorem nativeT0_homogeneous_iff_support
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (level : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi) :
    (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi ↔
      ∀ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
        nativeLevel D index.1 index.2 = level := by
  classical
  constructor
  · intro energy index member
    exact nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
      leftGramInverse rightGramInverse level psi sector energy index (Finsupp.mem_support_iff.mp member)
  · intro support
    let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
    have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
      (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
    rw [expansion]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul,
      nativeWord_T0 D H frame leftGramInverse rightGramInverse]
    apply Finset.sum_congr rfl
    intro index member
    rw [support index member]
    rw [mul_comm]

theorem nativeAux_homogeneous_iff_support (xAxis yAxis : Fin D.rank)
    (degree : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi) :
    AuxHomogeneous D frame inverse xAxis yAxis degree psi ↔
      ∀ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
        nativeDegree D xAxis yAxis index.1 index.2 = degree := by
  classical
  constructor
  · intro homogeneous index member
    exact nativeAux_support_degree D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis
      degree psi sector homogeneous index (Finsupp.mem_support_iff.mp member)
  · intro support
    let coefficients := nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi
    have expansion : psi = ∑ key ∈ coefficients.support, coefficients key • nativeWord D frame beta key :=
      (native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector).symm
    unfold AuxHomogeneous
    rw [expansion]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul,
      nativeWord_aux D frame inverse rightFrameInverse]
    apply Finset.sum_congr rfl
    intro index member
    rw [support index member]
    rw [mul_comm]

theorem native_joint_homogeneous_iff_support
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (xAxis yAxis : Fin D.rank) (level degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi) :
    ((M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi ∧
      AuxHomogeneous D frame inverse xAxis yAxis degree psi) ↔
      ∀ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support,
        nativeLevel D index.1 index.2 = level ∧ nativeDegree D xAxis yAxis index.1 index.2 = degree := by
  rw [nativeT0_homogeneous_iff_support D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level psi sector,
    nativeAux_homogeneous_iff_support D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis
      degree psi sector]
  constructor
  · rintro ⟨levels, degrees⟩ index member
    exact ⟨levels index member, degrees index member⟩
  · intro joint
    exact ⟨fun index member => (joint index member).1, fun index member => (joint index member).2⟩

def nativeJointLabel (xAxis yAxis : Fin D.rank) (index : NativeIndex D) : ℤ × ℤ :=
  (nativeLevel D index.1 index.2, nativeDegree D xAxis yAxis index.1 index.2)

def nativeJointLabels (xAxis yAxis : Fin D.rank) (psi : State D) : Finset (ℤ × ℤ) :=
  (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support.image
    (nativeJointLabel D xAxis yAxis)

def nativeJointComponent (xAxis yAxis : Fin D.rank) (psi : State D) (label : ℤ × ℤ) : State D :=
  ∑ index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support.filter
      (fun key => nativeJointLabel D xAxis yAxis key = label),
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index •
      nativeWord D frame beta index

theorem native_joint_finite_decomposition (xAxis yAxis : Fin D.rank)
    (psi : State D) (sector : chargeProjection D beta psi = psi) :
    ∑ label ∈ nativeJointLabels D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi,
      nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label = psi := by
  classical
  unfold nativeJointLabels nativeJointComponent
  rw [Finset.sum_fiberwise_of_maps_to
    (fun index member => Finset.mem_image_of_mem (nativeJointLabel D xAxis yAxis) member)]
  exact native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta psi sector

theorem nativeJointComponent_sector (xAxis yAxis : Fin D.rank) (psi : State D) (label : ℤ × ℤ) :
    chargeProjection D beta (nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta
      xAxis yAxis psi label) =
      nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label := by
  simp only [nativeJointComponent, map_sum, map_smul, nativeWord_sector]

theorem nativeJointComponent_coefficient (xAxis yAxis : Fin D.rank) (psi : State D)
    (label : ℤ × ℤ) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta
      (nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label) index =
      if nativeJointLabel D xAxis yAxis index = label then
        nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index else 0 := by
  classical
  rw [nativeJointComponent, nativeCoefficient_sum]
  by_cases member : index ∈ (nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi).support
  · simp [Finset.mem_filter, member]
  · have vanished := Finsupp.notMem_support_iff.mp member
    simp [Finset.mem_filter, member, vanished]

theorem nativeJointComponent_T0
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (xAxis yAxis : Fin D.rank) (psi : State D) (label : ℤ × ℤ) :
    (M D H 0 + G D 0)
      (nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label) =
      (chosenH D beta + (label.1 : ℂ) - 1) •
        nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label := by
  classical
  simp only [nativeJointComponent, map_sum, map_smul, Finset.smul_sum, smul_smul,
    nativeWord_T0 D H frame leftGramInverse rightGramInverse]
  apply Finset.sum_congr rfl
  intro index member
  have labelEqual := (Finset.mem_filter.mp member).2
  have levelEqual : nativeLevel D index.1 index.2 = label.1 := congrArg Prod.fst labelEqual
  rw [levelEqual, mul_comm]

theorem nativeJointComponent_aux (xAxis yAxis : Fin D.rank) (psi : State D) (label : ℤ × ℤ) :
    AuxHomogeneous D frame inverse xAxis yAxis label.2
      (nativeJointComponent D frame inverse leftFrameInverse rightFrameInverse beta xAxis yAxis psi label) := by
  classical
  unfold AuxHomogeneous
  simp only [nativeJointComponent, map_sum, map_smul, Finset.smul_sum, smul_smul,
    nativeWord_aux D frame inverse rightFrameInverse]
  apply Finset.sum_congr rfl
  intro index member
  have labelEqual := (Finset.mem_filter.mp member).2
  have degreeEqual : nativeDegree D xAxis yAxis index.1 index.2 = label.2 := congrArg Prod.snd labelEqual
  rw [degreeEqual, mul_comm]

end NativeCoordinates

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
