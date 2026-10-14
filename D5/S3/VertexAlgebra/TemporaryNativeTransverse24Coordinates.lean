import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.TemporaryOriginalQuartet06

import D5.S3.VertexAlgebra.BrstAdaptedFrameTransient
import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis18
import D5.S3.VertexAlgebra.TemporaryTransverseJointGhostCovariance

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24

open Module LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

abbrev Mode := Fin 24 × ℕ
abbrev Exponent := Mode →₀ ℕ
abbrev Polynomial := MvPolynomial Mode ℂ

def positiveFrequency (mode : Mode) : ℕ := mode.2 + 1

variable (D : LatticeData) (beta : Charge D) (frame : OriginalAdaptedFrameData D beta)

def rowMode (mode : Mode) : Index D := (frame.transverseRow mode.1, mode.2)

theorem rowMode_injective : Function.Injective (rowMode D beta frame) := by
  intro first second equality
  have rows : first.1 = second.1 :=
    frame.transverseRowInjective (congrArg (fun index : Index D => index.1) equality)
  have frequencies : first.2 = second.2 := congrArg (fun index : Index D => index.2) equality
  exact Prod.ext rows frequencies

theorem transverseRow_not_axes (row : Fin 24) :
    frame.transverseRow row ≠ frame.xAxis ∧ frame.transverseRow row ≠ frame.yAxis := by
  exact (frame.transverseRowExact (frame.transverseRow row)).mpr ⟨row, rfl⟩

theorem rowMode_range (index : Index D) :
    index ∈ Set.range (rowMode D beta frame) ↔
      index.1 ≠ frame.xAxis ∧ index.1 ≠ frame.yAxis := by
  constructor
  · rintro ⟨mode, rfl⟩
    exact transverseRow_not_axes D beta frame mode.1
  · intro away
    obtain ⟨row, equality⟩ := (frame.transverseRowExact index.1).mp away
    exact ⟨(row, index.2), Prod.ext equality rfl⟩

def exponentInclusion (powers : Exponent) : Index D →₀ ℕ :=
  powers.mapDomain (rowMode D beta frame)

theorem exponentInclusion_apply (powers : Exponent) (mode : Mode) :
    exponentInclusion D beta frame powers (rowMode D beta frame mode) = powers mode := by
  simp [exponentInclusion, Finsupp.mapDomain_apply (rowMode_injective D beta frame)]

theorem exponentInclusion_injective : Function.Injective (exponentInclusion D beta frame) := by
  intro first second equality
  ext mode
  have coefficients := congrArg (fun powers : Index D →₀ ℕ => powers (rowMode D beta frame mode)) equality
  simpa only [exponentInclusion_apply] using coefficients

theorem exponentInclusion_no_axes (powers : Exponent) :
    (∀ frequency : ℕ, exponentInclusion D beta frame powers (frame.xAxis, frequency) = 0) ∧
    (∀ frequency : ℕ, exponentInclusion D beta frame powers (frame.yAxis, frequency) = 0) := by
  classical
  have supported (index : Index D)
      (nonzero : exponentInclusion D beta frame powers index ≠ 0) :
      index ∈ Set.range (rowMode D beta frame) := by
    have member := Finsupp.mem_support_iff.mpr nonzero
    rw [exponentInclusion, Finsupp.mapDomain_support_of_injective
      (rowMode_injective D beta frame)] at member
    obtain ⟨mode, _, equality⟩ := Finset.mem_image.mp member
    exact ⟨mode, equality⟩
  constructor
  · intro frequency
    by_contra nonzero
    exact ((rowMode_range D beta frame _).mp (supported _ nonzero)).1 rfl
  · intro frequency
    by_contra nonzero
    exact ((rowMode_range D beta frame _).mp (supported _ nonzero)).2 rfl

def exponentRestriction (powers : Index D →₀ ℕ) : Exponent :=
  Finsupp.comapDomain (rowMode D beta frame) powers (rowMode_injective D beta frame).injOn

theorem exponentRestriction_apply (powers : Index D →₀ ℕ) (mode : Mode) :
    exponentRestriction D beta frame powers mode = powers (rowMode D beta frame mode) := by
  simp [exponentRestriction, Finsupp.comapDomain_apply]

theorem exponentRestriction_inclusion (powers : Exponent) :
    exponentRestriction D beta frame (exponentInclusion D beta frame powers) = powers := by
  ext mode
  rw [exponentRestriction_apply, exponentInclusion_apply]

theorem exponentInclusion_restriction (powers : Index D →₀ ℕ)
    (xZero : ∀ frequency : ℕ, powers (frame.xAxis, frequency) = 0)
    (yZero : ∀ frequency : ℕ, powers (frame.yAxis, frequency) = 0) :
    exponentInclusion D beta frame (exponentRestriction D beta frame powers) = powers := by
  apply Finsupp.mapDomain_comapDomain (rowMode D beta frame) (rowMode_injective D beta frame)
  intro index member
  apply (rowMode_range D beta frame index).mpr
  have nonzero := Finsupp.mem_support_iff.mp member
  constructor
  · intro equality
    exact nonzero ((congrArg powers (show index = (frame.xAxis, index.2) from
      Prod.ext equality rfl)).trans (xZero index.2))
  · intro equality
    exact nonzero ((congrArg powers (show index = (frame.yAxis, index.2) from
      Prod.ext equality rfl)).trans (yZero index.2))

def epsilonSites (upper : Bool) : Finset ℕ := if upper then {3} else ∅

theorem epsilonSites_injective : Function.Injective epsilonSites := by
  intro first second equality
  cases first <;> cases second <;> simp_all [epsilonSites]

theorem epsilonSites_only (upper : Bool) : epsilonSites upper ⊆ {3} := by
  cases upper <;> simp [epsilonSites]

theorem epsilonSites_exhaustion (subset : Finset ℕ) (onlyEpsilon : subset ⊆ {3}) :
    ∃ upper : Bool, epsilonSites upper = subset := by
  classical
  by_cases occupied : 3 ∈ subset
  · exact ⟨true, Finset.Subset.antisymm (Finset.singleton_subset_iff.mpr occupied) onlyEpsilon⟩
  · refine ⟨false, ?_⟩
    apply Eq.symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro site member
    exact occupied ((Finset.mem_singleton.mp (onlyEpsilon member)) ▸ member)

def laneIndex (upper : Bool) (powers : Exponent) : NativeIndex D :=
  (exponentInclusion D beta frame powers, epsilonSites upper)

theorem laneIndex_injective (upper : Bool) : Function.Injective (laneIndex D beta frame upper) := by
  intro first second equality
  exact exponentInclusion_injective D beta frame (congrArg Prod.fst equality)

theorem laneIndex_eq_iff (first second : Bool) (powers other : Exponent) :
    laneIndex D beta frame first powers = laneIndex D beta frame second other ↔
      powers = other ∧ first = second := by
  constructor
  · intro equality
    exact ⟨exponentInclusion_injective D beta frame (congrArg Prod.fst equality),
      epsilonSites_injective (congrArg Prod.snd equality)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem laneIndex_zero_occupation (upper : Bool) (powers : Exponent) :
    kappa D frame.xAxis frame.yAxis (laneIndex D beta frame upper powers).1
      (laneIndex D beta frame upper powers).2 = 0 := by
  apply (kappa_zero_iff D frame.xAxis frame.yAxis _ _).mpr
  exact ⟨(exponentInclusion_no_axes D beta frame powers).1,
    (exponentInclusion_no_axes D beta frame powers).2, epsilonSites_only upper⟩

theorem zero_occupation_exhaustion (index : NativeIndex D)
    (zero : kappa D frame.xAxis frame.yAxis index.1 index.2 = 0) :
    ∃ powers : Exponent, ∃ upper : Bool, laneIndex D beta frame upper powers = index := by
  obtain ⟨xZero, yZero, onlyEpsilon⟩ := (kappa_zero_iff D frame.xAxis frame.yAxis _ _).mp zero
  obtain ⟨upper, sites⟩ := epsilonSites_exhaustion index.2 onlyEpsilon
  refine ⟨exponentRestriction D beta frame index.1, upper, ?_⟩
  exact Prod.ext (exponentInclusion_restriction D beta frame index.1 xZero yZero) sites

def matterEmbedding : Polynomial →ₐ[ℂ] Oscillator D :=
  (coordinateSub D frame.frame).comp (MvPolynomial.rename (rowMode D beta frame))

theorem matterEmbedding_X (mode : Mode) :
    matterEmbedding D beta frame (MvPolynomial.X mode) =
      ∑ original, (frame.transverseBasis mode.1 : Fin D.rank → ℂ) original •
        MvPolynomial.X (original, mode.2) := by
  simp only [matterEmbedding, AlgHom.comp_apply, MvPolynomial.rename_X, coordinateSub_X,
    coordinate, rowMode, frame.transverseRowVector]

theorem matterEmbedding_monomial (powers : Exponent) (scalar : ℂ) :
    matterEmbedding D beta frame (MvPolynomial.monomial powers scalar) =
      coordinateSub D frame.frame (MvPolynomial.monomial (exponentInclusion D beta frame powers) scalar) := by
  simp [matterEmbedding, exponentInclusion, MvPolynomial.rename_monomial]

def lane (upper : Bool) : Polynomial →ₗ[ℂ] State D :=
  (MvPolynomial.basisMonomials Mode ℂ).constr ℂ
    (fun powers => nativeWord D frame.frame beta (laneIndex D beta frame upper powers))

theorem lane_monomial (upper : Bool) (powers : Exponent) (scalar : ℂ) :
    lane D beta frame upper (MvPolynomial.monomial powers scalar) =
      scalar • nativeWord D frame.frame beta (laneIndex D beta frame upper powers) := by
  have scaled : MvPolynomial.monomial powers scalar = scalar • MvPolynomial.monomial powers (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [scaled, map_smul]
  change scalar • ((MvPolynomial.basisMonomials Mode ℂ).constr ℂ
    (fun exponent => nativeWord D frame.frame beta (laneIndex D beta frame upper exponent)))
    ((MvPolynomial.basisMonomials Mode ℂ) powers) = _
  rw [Module.Basis.constr_basis]

def physicalLane (upper : Bool) : Polynomial →ₗ[ℂ] State D where
  toFun polynomial := Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ]
    downWord (epsilonSites upper) down
  map_add' first second := by
    simp [map_add, Finsupp.single_add, TensorProduct.add_tmul]
  map_smul' scalar polynomial := by
    simp only [map_smul, ← Finsupp.smul_single, TensorProduct.smul_tmul', RingHom.id_apply]

theorem lane_eq_physical (upper : Bool) : lane D beta frame upper = physicalLane D beta frame upper := by
  apply (MvPolynomial.basisMonomials Mode ℂ).ext
  intro powers
  change lane D beta frame upper (MvPolynomial.monomial powers 1) =
    physicalLane D beta frame upper (MvPolynomial.monomial powers 1)
  rw [lane_monomial, one_smul]
  change nativeWord D frame.frame beta (laneIndex D beta frame upper powers) =
    Finsupp.single beta (matterEmbedding D beta frame (MvPolynomial.monomial powers 1)) ⊗ₜ[ℂ]
      downWord (epsilonSites upper) down
  rw [matterEmbedding_monomial]
  rfl

theorem epsilon_polarization_sign (upper : Bool) :
    polarizationSign (epsilonSites upper) = if upper then -1 else 1 := by
  cases upper <;> norm_num [epsilonSites, polarizationSign, Finset.filter_singleton]

theorem epsilon_polarization_sign_nonzero (upper : Bool) :
    polarizationSign (epsilonSites upper) ≠ 0 := by
  rw [epsilon_polarization_sign]
  cases upper <;> norm_num

theorem epsilon_ghost (upper : Bool) :
    downWord (epsilonSites upper) down = if upper then up else down := by
  cases upper <;> simp [epsilonSites, downWord, downCreator, up, c]

theorem lane_tensor (upper : Bool) (polynomial : Polynomial) :
    lane D beta frame upper polynomial =
      Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ]
        (if upper then up else down) := by
  rw [lane_eq_physical]
  exact congrArg (fun ghost : Fock ℂ =>
    Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ] ghost) (epsilon_ghost upper)

def readLane (upper : Bool) : State D →ₗ[ℂ] Polynomial where
  toFun state := AddMonoidAlgebra.ofCoeff (Finsupp.comapDomain (laneIndex D beta frame upper)
    (nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta state)
    (laneIndex_injective D beta frame upper).injOn)
  map_add' first second := by
    ext powers
    simp [MvPolynomial.coeff, Finsupp.comapDomain_apply, map_add]
  map_smul' scalar state := by
    ext powers
    simp [MvPolynomial.coeff, Finsupp.comapDomain_apply, map_smul]

theorem readLane_coeff (upper : Bool) (state : State D) (powers : Exponent) :
    MvPolynomial.coeff powers (readLane D beta frame upper state) =
      nativeCoefficients D frame.frame frame.inverse frame.leftFrameInverse frame.rightFrameInverse beta
        state (laneIndex D beta frame upper powers) := by
  simp [readLane, Finsupp.comapDomain_apply, MvPolynomial.coeff]

theorem readLane_nativeWord (upper other : Bool) (powers : Exponent) :
    readLane D beta frame upper (nativeWord D frame.frame beta (laneIndex D beta frame other powers)) =
      if upper = other then MvPolynomial.monomial powers 1 else 0 := by
  classical
  apply MvPolynomial.ext
  intro exponent
  rw [readLane_coeff, nativeCoefficients_word]
  by_cases same : upper = other
  · subst other
    simp [Finsupp.single_apply, laneIndex_eq_iff, MvPolynomial.coeff_monomial, eq_comm]
  · simp [Finsupp.single_apply, laneIndex_eq_iff, MvPolynomial.coeff_monomial,
      same, Ne.symm same, eq_comm]

theorem readLane_lane (upper other : Bool) (polynomial : Polynomial) :
    readLane D beta frame upper (lane D beta frame other polynomial) =
      if upper = other then polynomial else 0 := by
  classical
  have equality : (readLane D beta frame upper).comp (lane D beta frame other) =
      if upper = other then LinearMap.id else 0 := by
    apply (MvPolynomial.basisMonomials Mode ℂ).ext
    intro powers
    simp only [LinearMap.comp_apply, MvPolynomial.coe_basisMonomials, lane_monomial, one_smul,
      readLane_nativeWord]
    by_cases same : upper = other <;> simp [same]
  have evaluated := congrArg (fun operator : Polynomial →ₗ[ℂ] Polynomial => operator polynomial) equality
  by_cases same : upper = other <;> simpa [same] using evaluated

def realize : Polynomial × Polynomial →ₗ[ℂ] State D where
  toFun pair := lane D beta frame false pair.1 + lane D beta frame true pair.2
  map_add' first second := by simp [map_add]; abel
  map_smul' scalar pair := by simp [map_smul, smul_add]

def extract : State D →ₗ[ℂ] Polynomial × Polynomial :=
  (readLane D beta frame false).prod (readLane D beta frame true)

theorem extract_realize (pair : Polynomial × Polynomial) :
    extract D beta frame (realize D beta frame pair) = pair := by
  ext <;> simp [extract, realize, readLane_lane]

theorem realize_injective : Function.Injective (realize D beta frame) := by
  intro first second equality
  have recovered := congrArg (extract D beta frame) equality
  simpa only [extract_realize] using recovered

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24
