import D5.S3.VertexAlgebra.TemporaryNativeTransverse24Energy

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24

open Module LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (beta : Charge D) (frame : OriginalAdaptedFrameData D beta)
  (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)

def fixedEnergy (energy : ℂ) : Submodule ℂ (State D) :=
  fixedReduced D beta frame ⊓ LinearMap.ker
    ((M D H 0 + G D 0) - energy • (1 : Module.End ℂ (State D)))

theorem fixedEnergy_mem (energy : ℂ) (state : State D) :
    state ∈ fixedEnergy D beta frame H energy ↔ state ∈ fixedReduced D beta frame ∧
      (M D H 0 + G D 0) state = energy • state := by
  simp [fixedEnergy, LinearMap.mem_ker, sub_eq_zero]

include leftGramInverse rightGramInverse in
theorem fixedEnergy_realize_mem (energy : ℂ) (pair : Polynomial × Polynomial) :
    realize D beta frame pair ∈ fixedEnergy D beta frame H energy ↔
      pair.1 ∈ polynomialEnergySector D beta energy ∧ pair.2 ∈ polynomialEnergySector D beta energy := by
  rw [fixedEnergy_mem]
  simp only [realize_mem, true_and]
  rw [T0_realize_eigen_iff D beta frame H leftGramInverse rightGramInverse,
    polynomialEnergySector_mem, polynomialEnergySector_mem]

include leftGramInverse rightGramInverse in
theorem fixedEnergy_extract_mem (energy : ℂ) (state : State D)
    (member : state ∈ fixedEnergy D beta frame H energy) :
    readLane D beta frame false state ∈ polynomialEnergySector D beta energy ∧
      readLane D beta frame true state ∈ polynomialEnergySector D beta energy := by
  have reducedMember := ((fixedEnergy_mem D beta frame H energy state).mp member).1
  apply (fixedEnergy_realize_mem D beta frame H leftGramInverse rightGramInverse energy
    (extract D beta frame state)).mp
  simpa only [realize_extract D beta frame state reducedMember] using member

def energyRealize (energy : ℂ) :
    polynomialEnergySector D beta energy × polynomialEnergySector D beta energy →ₗ[ℂ]
      fixedEnergy D beta frame H energy :=
  ((realize D beta frame).comp ((polynomialEnergySector D beta energy).subtype.prodMap
    (polynomialEnergySector D beta energy).subtype)).codRestrict (fixedEnergy D beta frame H energy)
    (fun pair => (fixedEnergy_realize_mem D beta frame H leftGramInverse rightGramInverse energy
      ((pair.1 : Polynomial), (pair.2 : Polynomial))).mpr ⟨pair.1.property, pair.2.property⟩)

def energyExtract (energy : ℂ) (state : fixedEnergy D beta frame H energy) :
    polynomialEnergySector D beta energy × polynomialEnergySector D beta energy :=
  (⟨readLane D beta frame false state,
    (fixedEnergy_extract_mem D beta frame H leftGramInverse rightGramInverse energy state state.property).1⟩,
   ⟨readLane D beta frame true state,
    (fixedEnergy_extract_mem D beta frame H leftGramInverse rightGramInverse energy state state.property).2⟩)

def energyEquiv (energy : ℂ) :
    (polynomialEnergySector D beta energy × polynomialEnergySector D beta energy) ≃ₗ[ℂ]
      fixedEnergy D beta frame H energy where
  toLinearMap := energyRealize D beta frame H leftGramInverse rightGramInverse energy
  invFun := energyExtract D beta frame H leftGramInverse rightGramInverse energy
  left_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (extract_realize D beta frame ((pair.1 : Polynomial), (pair.2 : Polynomial)))
    · apply Subtype.ext
      exact congrArg Prod.snd (extract_realize D beta frame ((pair.1 : Polynomial), (pair.2 : Polynomial)))
  right_inv state := by
    apply Subtype.ext
    exact realize_extract D beta frame state ((fixedEnergy_mem D beta frame H energy state).mp state.property).1

theorem energyEquiv_apply (energy : ℂ)
    (pair : polynomialEnergySector D beta energy × polynomialEnergySector D beta energy) :
    (energyEquiv D beta frame H leftGramInverse rightGramInverse energy pair : State D) =
      realize D beta frame ((pair.1 : Polynomial), (pair.2 : Polynomial)) := rfl

theorem energyEquiv_symm (energy : ℂ) (state : fixedEnergy D beta frame H energy) :
    (((energyEquiv D beta frame H leftGramInverse rightGramInverse energy).symm state).1 : Polynomial) =
      readLane D beta frame false state ∧
    (((energyEquiv D beta frame H leftGramInverse rightGramInverse energy).symm state).2 : Polynomial) =
      readLane D beta frame true state := ⟨rfl, rfl⟩

def fixedRelativeEnergy (energy : ℂ) : Submodule ℂ (State D) :=
  fixedRelative D beta frame ⊓ LinearMap.ker
    ((M D H 0 + G D 0) - energy • (1 : Module.End ℂ (State D)))

theorem fixedRelativeEnergy_mem (energy : ℂ) (state : State D) :
    state ∈ fixedRelativeEnergy D beta frame H energy ↔ state ∈ fixedRelative D beta frame ∧
      (M D H 0 + G D 0) state = energy • state := by
  simp [fixedRelativeEnergy, LinearMap.mem_ker, sub_eq_zero]

include leftGramInverse rightGramInverse in
theorem fixedRelativeEnergy_lower_mem (energy : ℂ) (polynomial : Polynomial) :
    lane D beta frame false polynomial ∈ fixedRelativeEnergy D beta frame H energy ↔
      polynomial ∈ polynomialEnergySector D beta energy := by
  rw [fixedRelativeEnergy_mem]
  simp only [lower_relative, true_and]
  rw [T0_lane D beta frame H leftGramInverse rightGramInverse, polynomialEnergySector_mem]
  constructor
  · intro equality
    have recovered := congrArg (readLane D beta frame false) equality
    simpa only [map_smul, readLane_lane, if_true] using recovered
  · intro equality
    rw [equality, map_smul]

include leftGramInverse rightGramInverse in
theorem fixedRelativeEnergy_read_mem (energy : ℂ) (state : State D)
    (member : state ∈ fixedRelativeEnergy D beta frame H energy) :
    readLane D beta frame false state ∈ polynomialEnergySector D beta energy := by
  obtain ⟨relativeMember, eigenvector⟩ := (fixedRelativeEnergy_mem D beta frame H energy state).mp member
  obtain ⟨reducedMember, upperZero⟩ := (fixedRelative_mem D beta frame state).mp relativeMember
  have recovered : lane D beta frame false (readLane D beta frame false state) = state := by
    have equality := realize_extract D beta frame state reducedMember
    change lane D beta frame false (readLane D beta frame false state) +
      lane D beta frame true (readLane D beta frame true state) = state at equality
    rw [upperZero, map_zero, add_zero] at equality
    exact equality
  apply (fixedRelativeEnergy_lower_mem D beta frame H leftGramInverse rightGramInverse energy _).mp
  rw [recovered]
  exact member

def relativeEnergyRealize (energy : ℂ) : polynomialEnergySector D beta energy →ₗ[ℂ]
    fixedRelativeEnergy D beta frame H energy where
  toFun polynomial := ⟨lane D beta frame false polynomial,
    (fixedRelativeEnergy_lower_mem D beta frame H leftGramInverse rightGramInverse energy polynomial).mpr
      polynomial.property⟩
  map_add' first second := by
    apply Subtype.ext
    exact map_add (lane D beta frame false) _ _
  map_smul' scalar polynomial := by
    apply Subtype.ext
    exact map_smul (lane D beta frame false) scalar _

def relativeEnergyEquiv (energy : ℂ) : polynomialEnergySector D beta energy ≃ₗ[ℂ]
    fixedRelativeEnergy D beta frame H energy where
  toLinearMap := relativeEnergyRealize D beta frame H leftGramInverse rightGramInverse energy
  invFun state := ⟨readLane D beta frame false state,
    fixedRelativeEnergy_read_mem D beta frame H leftGramInverse rightGramInverse energy state state.property⟩
  left_inv polynomial := by
    apply Subtype.ext
    change readLane D beta frame false (lane D beta frame false (polynomial : Polynomial)) =
      (polynomial : Polynomial)
    simpa using readLane_lane D beta frame false false (polynomial : Polynomial)
  right_inv state := by
    apply Subtype.ext
    obtain ⟨relativeMember, eigenvector⟩ :=
      (fixedRelativeEnergy_mem D beta frame H energy state).mp state.property
    obtain ⟨reducedMember, upperZero⟩ := (fixedRelative_mem D beta frame state).mp relativeMember
    change lane D beta frame false (readLane D beta frame false state) = (state : State D)
    have equality := realize_extract D beta frame state reducedMember
    change lane D beta frame false (readLane D beta frame false state) +
      lane D beta frame true (readLane D beta frame true state) = (state : State D) at equality
    rw [upperZero, map_zero, add_zero] at equality
    exact equality

def zeroT0Equiv : (polynomialEnergySector D beta 0 × polynomialEnergySector D beta 0) ≃ₗ[ℂ]
    fixedEnergy D beta frame H 0 := energyEquiv D beta frame H leftGramInverse rightGramInverse 0

def relativeZeroT0Equiv : polynomialEnergySector D beta 0 ≃ₗ[ℂ]
    fixedRelativeEnergy D beta frame H 0 :=
  relativeEnergyEquiv D beta frame H leftGramInverse rightGramInverse 0

include leftGramInverse rightGramInverse in
theorem fixed_zeroT0_nonzero_matching (state : State D)
    (member : state ∈ fixedEnergy D beta frame H 0) (nonzero : state ≠ 0) :
    ∃ level : ℕ, (level : ℂ) = 1 - chosenH D beta := by
  obtain ⟨lowerOnShell, upperOnShell⟩ :=
    fixedEnergy_extract_mem D beta frame H leftGramInverse rightGramInverse 0 state member
  by_cases lowerNonzero : readLane D beta frame false state ≠ 0
  · exact zeroT0_nonzero_level_matching D beta _ lowerNonzero lowerOnShell
  · have lowerZero := not_ne_iff.mp lowerNonzero
    have upperNonzero : readLane D beta frame true state ≠ 0 := by
      intro upperZero
      apply nonzero
      have recovered := realize_extract D beta frame state
        ((fixedEnergy_mem D beta frame H 0 state).mp member).1
      simpa [realize, extract, lowerZero, upperZero] using recovered.symm
    exact zeroT0_nonzero_level_matching D beta _ upperNonzero upperOnShell

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24
