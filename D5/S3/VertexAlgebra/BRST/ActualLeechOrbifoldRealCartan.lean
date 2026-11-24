/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealCartan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealCartan
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Real Cartan and Lorentzian root geometry of native Leech orbifold relative BRST. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechBRSTRealLie
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldIntegerGrading
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNullMomentum
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOppositeRootBracket
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Ring

/-!
The real Cartan in native relative BRST cohomology comes from the two plane
Heisenberg currents tensored with the Leech orbifold vacuum and the ghost c₁.
The signed BPZ form identifies the Cartan functional at momentum p with the
Cartan vector of coordinates p in the ordered null basis.

These are real Cartan and root-space ingredients for Theorem 2 of Borcherds,
*A characterization of generalized Kac-Moody algebras*, J. Algebra 174 (1995),
1073–1079, https://math.berkeley.edu/~reb/papers/gkmas/gkmas.tex.

proof_shape: coefficientConjugationMomentum_cartanClass, mem_realCartan_iff,
  realCartan_selfCentralizing, realCartanBPZ_diagonal, mem_realMomentumWeightSpace: content
admission_basis: escape-witness
escape_witness: The literal plane current, matter vacuum and ghost ket are
coefficient-real. The two Cartan zero modes detect both momentum coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators ComplexConjugate DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldModeRealForm (orbifoldConjugation)
open Lattice.ActualCoefficientRealForm (fixedKappa fixedKappa_vacuum)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open RelativeCohomology (GradedCycles GradedCohomology ghostOne_eq_zero_of_nonzero_null)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier kappaCarrier_single kappaOsc_X)
open TwistedGround.ActualLeechTwistedTensorRealForm (negativeConjugation)
open TwistedGround.Orbifold.OriginalOrbifoldField (vacuumState)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)
open BcGhostBilinear (kappa_ket)
open RealRootBracket (cartanClass lie_cartanClass_incl zero_momentum_lie_eq_zero
  mem_momentum_range_iff_cartan_eigenvectors)

open private planeConjugation ghostConjugation matterConjugation_tmul
  momentumConjugationAddHom_apply from
  D5.S3.VertexAlgebra.BRST.ActualLeechBRSTCoefficientRealForm
open private cartanCycle cartanCycle_native incl_injective plane_pairing from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket
open private nativeValue_injective from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "component" => DirectSum.component ℂ Momentum H

local instance realCartanStateAddCommGroup : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup
local instance realCartanShellAddCommGroup (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance realCartanCyclesAddCommGroup (p : Momentum) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

private theorem coefficientConjugation_u (i : Fin 2) :
    coefficientConjugation (RelativeZeroMomentum.u i) = RelativeZeroMomentum.u i := by
  have hv : orbifoldConjugation (vacuumState leechData leechUnit) =
      vacuumState leechData leechUnit := by
    change (fixedKappa leechData _, negativeConjugation 0) = (_, 0)
    exact Prod.ext (fixedKappa_vacuum leechData) negativeConjugation.map_zero
  have hc : planeConjugation (LatticeZeroMomentumBRST.current hyperbolicPlane i) =
      LatticeZeroMomentumBRST.current hyperbolicPlane i := by
    change kappaCarrier (Finsupp.single 0 (MvPolynomial.X (i, 0)) : Carrier hyperbolicPlane) =
      Finsupp.single 0 (MvPolynomial.X (i, 0))
    rw [kappaCarrier_single, kappaOsc_X]
  have hg : ghostConjugation (ket {1}) = ket {1} := kappa_ket {1}
  simp only [RelativeZeroMomentum.u, coefficientConjugation_tmul, matterConjugation_tmul,
    hv, hc, hg]

private theorem coefficientConjugation_cartanCycle (f : Fin 2 → ℂ) :
    coefficientConjugationCycles 0 (cartanCycle f) = cartanCycle (fun i => conj (f i)) := by
  apply nativeValue_injective 0
  rw [coefficientConjugationCycles_nativeValue, cartanCycle_native f,
    cartanCycle_native (fun i => conj (f i))]
  simp only [map_add, map_smulₛₗ, coefficientConjugation_u]

set_option maxHeartbeats 1000000 in
-- The two quotient presentations must elaborate over the concrete cycle space.
/-- The zero-momentum quotient coordinates inherit ordinary coefficient conjugation. -/
theorem coefficientConjugationCohomology_cartan (f : Fin 2 → ℂ) :
    coefficientConjugationCohomology 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm f) =
      RelativeZeroMomentum.ghostOneCohomologyEquiv.symm (fun i => conj (f i)) := by
  rw [RelativeZeroMomentum.ghostOneCohomologyEquiv_symm f,
    RelativeZeroMomentum.ghostOneCohomologyEquiv_symm (fun i => conj (f i))]
  change coefficientConjugationCohomology 0 (Submodule.Quotient.mk (cartanCycle f)) =
    Submodule.Quotient.mk (cartanCycle (fun i => conj (f i)))
  rw [coefficientConjugationCohomology_mk, coefficientConjugation_cartanCycle]

/-- The inclusion of the Cartan in the momentum sum carries coefficient conjugation. -/
theorem coefficientConjugationMomentum_cartanClass (f : Fin 2 → ℂ) :
    coefficientConjugationMomentum (cartanClass f) = cartanClass (fun i => conj (f i)) := by
  simp only [cartanClass, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coefficientConjugationMomentum_incl, coefficientConjugationCohomology_cartan]

private theorem cartanClass_injective : Function.Injective cartanClass :=
  (incl_injective 0).comp RelativeZeroMomentum.ghostOneCohomologyEquiv.symm.injective

private abbrev complexCoordinates (f : Fin 2 → ℝ) : Fin 2 → ℂ := fun i => (f i : ℂ)

/-- The two real plane-current directions in the fixed real BRST Lie algebra. -/
def realCartanClass : (Fin 2 → ℝ) →ₗ[ℝ] momentumRealLie where
  toFun f := ⟨cartanClass (complexCoordinates f), by
    change coefficientConjugationMomentum (cartanClass (complexCoordinates f)) = _
    have h : (fun i => conj (complexCoordinates f i)) = complexCoordinates f :=
      funext fun i => Complex.conj_ofReal (f i)
    rw [coefficientConjugationMomentum_cartanClass, h]⟩
  map_add' f g := by
    apply Subtype.ext
    change cartanClass (complexCoordinates (f + g)) =
      cartanClass (complexCoordinates f) + cartanClass (complexCoordinates g)
    rw [show complexCoordinates (f + g) = complexCoordinates f + complexCoordinates g by
      funext i
      exact Complex.ofReal_add (f i) (g i), map_add]
  map_smul' r f := by
    apply Subtype.ext
    change cartanClass (complexCoordinates (r • f)) = (r : ℂ) • cartanClass (complexCoordinates f)
    rw [show complexCoordinates (r • f) = (r : ℂ) • complexCoordinates f by
      funext i
      exact Complex.ofReal_mul r (f i), map_smul]

@[simp] theorem momentumRealValue_realCartanClass (f : Fin 2 → ℝ) :
    momentumRealValue (realCartanClass f) = cartanClass (complexCoordinates f) := rfl

theorem realCartanClass_injective : Function.Injective realCartanClass := by
  intro f g h
  have hc := cartanClass_injective (congrArg momentumRealValue h)
  funext i
  exact Complex.ofReal_injective (congrFun hc i)

/-- The image of the plane-current map is a real Lie subalgebra. -/
def realCartan : LieSubalgebra ℝ momentumRealLie where
  __ := LinearMap.range realCartanClass
  lie_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    have h : ⁅realCartanClass f, realCartanClass g⁆ = 0 := by
      apply Subtype.ext
      exact zero_momentum_lie_eq_zero _ _
    rw [h]
    exact (LinearMap.range realCartanClass).zero_mem

/-- The real Cartan is precisely the intersection with the complex zero-momentum summand. -/
theorem mem_realCartan_iff (x : momentumRealLie) :
    x ∈ realCartan ↔ momentumRealValue x ∈ LinearMap.range (incl 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨RelativeZeroMomentum.ghostOneCohomologyEquiv.symm (complexCoordinates f), rfl⟩
  · rintro ⟨a, ha⟩
    let f := RelativeZeroMomentum.ghostOneCohomologyEquiv a
    have hf : cartanClass f = momentumRealValue x := by
      change incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm
        (RelativeZeroMomentum.ghostOneCohomologyEquiv a)) = _
      rw [LinearEquiv.symm_apply_apply]
      exact ha
    have hconj : (fun i => conj (f i)) = f := by
      apply cartanClass_injective
      rw [← coefficientConjugationMomentum_cartanClass, hf, momentumConjugation_realValue]
    refine ⟨fun i => (f i).re, Subtype.ext ?_⟩
    have hre : complexCoordinates (fun i => (f i).re) = f :=
      funext fun i => Complex.conj_eq_iff_re.mp (congrFun hconj i)
    change cartanClass (complexCoordinates (fun i => (f i).re)) = _
    rw [hre, hf]

/-- A real class lies in the native momentum summand exactly when its unique
complex summand representative is fixed at that momentum. -/
theorem momentumRealValue_mem_incl_range_iff (p : Momentum) (x : momentumRealLie) :
    momentumRealValue x ∈ LinearMap.range (incl p) ↔
      ∃ a : H p, coefficientConjugationCohomology p a = a ∧ incl p a = momentumRealValue x := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, incl_injective p ?_, ha⟩
    rw [← coefficientConjugationMomentum_incl, ha, momentumConjugation_realValue]
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩

/-- Coordinates on the real Cartan in the ordered null basis. -/
def realCartanEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] realCartan :=
  LinearEquiv.ofInjective realCartanClass realCartanClass_injective

private theorem complexCoordinates_single (i : Fin 2) :
    complexCoordinates (Pi.single i 1) = Pi.single i 1 := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [complexCoordinates]
  · simp [complexCoordinates, Pi.single_eq_of_ne h]

/-- The simultaneous centralizer of the two real coordinate currents is the real Cartan. -/
theorem mem_realCartan_iff_basis_centralizes (x : momentumRealLie) :
    x ∈ realCartan ↔ ∀ i : Fin 2, ⁅realCartanClass (Pi.single i 1), x⁆ = 0 := by
  rw [mem_realCartan_iff, RealRootBracket.mem_zero_momentum_range_iff_cartan_centralizer]
  constructor
  · intro h i
    apply Subtype.ext
    change ⁅cartanClass (complexCoordinates (Pi.single i 1)), momentumRealValue x⁆ = 0
    rw [complexCoordinates_single]
    exact h i
  · intro h i
    have hi := congrArg momentumRealValue (h i)
    change ⁅cartanClass (complexCoordinates (Pi.single i 1)), momentumRealValue x⁆ = 0 at hi
    simpa only [complexCoordinates_single] using hi

/-- The real Cartan is self-centralizing in the fixed Lie algebra. -/
theorem realCartan_selfCentralizing (x : momentumRealLie) :
    x ∈ realCartan ↔ ∀ h : realCartan, ⁅(h : momentumRealLie), x⁆ = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ ⟨_, g, rfl⟩
    apply Subtype.ext
    exact zero_momentum_lie_eq_zero _ _
  · intro h
    exact (mem_realCartan_iff_basis_centralizes x).mpr fun i =>
      h ⟨_, LinearMap.mem_range_self realCartanClass (Pi.single i 1)⟩

/-- The signed native BPZ restriction has the hyperbolic Gram matrix. -/
theorem momentumRealBPZ_cartan (f g : Fin 2 → ℝ) :
    momentumRealBPZ (realCartanClass f) (realCartanClass g) = f 0 * g 1 + f 1 * g 0 := by
  apply Complex.ofReal_injective
  rw [ofReal_momentumRealBPZ, momentumRealValue_realCartanClass,
    momentumRealValue_realCartanClass, nativeRelativeBPZ_cartan]
  simp only [complexCoordinates, Complex.ofReal_add, Complex.ofReal_mul]

private def diagonalToNullCoordinates : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun f := ![f 0 + f 1, f 0 - f 1]
  invFun f := ![(f 0 + f 1) / 2, (f 0 - f 1) / 2]
  left_inv := by
    intro f
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro f
    funext i
    fin_cases i <;> simp <;> ring
  map_add' := by
    intro f g
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro r f
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- The diagonal basis has the sum and the difference of the two null currents. -/
def realCartanDiagonalEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] realCartan :=
  diagonalToNullCoordinates.trans realCartanEquiv

/-- In the diagonal basis the actual signed form has one positive and one negative square. -/
theorem momentumRealBPZ_cartan_diagonal (f g : Fin 2 → ℝ) :
    momentumRealBPZ (realCartanDiagonalEquiv f : momentumRealLie)
      (realCartanDiagonalEquiv g : momentumRealLie) = 2 * f 0 * g 0 - 2 * f 1 * g 1 := by
  change momentumRealBPZ (realCartanClass ![f 0 + f 1, f 0 - f 1])
    (realCartanClass ![g 0 + g 1, g 0 - g 1]) = _
  rw [momentumRealBPZ_cartan]
  simp
  ring

/-- The momentum functional on the real Cartan, in the ordered null basis. -/
def realMomentumWeight (p : Momentum) : realCartan →ₗ[ℝ] ℝ :=
  LinearMap.comp
    ((p (1 : Fin 2) : ℝ) • (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) +
      (p (0 : Fin 2) : ℝ) • (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ))
    realCartanEquiv.symm.toLinearMap

theorem realMomentumWeight_coordinates (p : Momentum) (f : Fin 2 → ℝ) :
    realMomentumWeight p (realCartanEquiv f) =
      f 0 * (p (1 : Fin 2) : ℝ) + f 1 * (p (0 : Fin 2) : ℝ) := by
  simp only [realMomentumWeight, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

/-- Raising the momentum functional with the signed BPZ form gives the Cartan vector p. -/
theorem momentumRealBPZ_raises_weight (p : Momentum) (h : realCartan) :
    momentumRealBPZ (h : momentumRealLie) (realCartanClass (fun i => (p i : ℝ))) =
      realMomentumWeight p h := by
  obtain ⟨f, rfl⟩ := realCartanEquiv.surjective h
  rw [realMomentumWeight_coordinates]
  exact momentumRealBPZ_cartan f (fun i => (p i : ℝ))

/-- The raised momentum vectors have the signed form of the native hyperbolic lattice. -/
theorem momentumRealBPZ_momentum (p q : Momentum) :
    momentumRealBPZ (realCartanClass (fun i => (p i : ℝ))) (realCartanClass (fun i => (q i : ℝ))) =
      (bilinear hyperbolicPlane p q : ℝ) := by
  rw [momentumRealBPZ_cartan, plane_pairing]
  simp only [Int.cast_add, Int.cast_mul]

/-- Squared length of the raised momentum in the ordered null basis. -/
theorem momentumRealBPZ_momentum_norm (p : Momentum) :
    momentumRealBPZ (realCartanClass (fun i => (p i : ℝ))) (realCartanClass (fun i => (p i : ℝ))) =
      2 * ((p (0 : Fin 2) : ℝ) * (p (1 : Fin 2) : ℝ)) := by
  rw [momentumRealBPZ_cartan]
  ring

/-- The simultaneous real eigenspace for the momentum functional. -/
def realMomentumWeightSpace (p : Momentum) : LieSubmodule ℝ realCartan momentumRealLie :=
  LieModule.weightSpace momentumRealLie (realMomentumWeight p)

/-- The two real coordinate operators recover exactly the complex momentum support condition. -/
theorem mem_realMomentumWeightSpace (p : Momentum) (x : momentumRealLie) :
    x ∈ realMomentumWeightSpace p ↔ momentumRealValue x ∈ LinearMap.range (incl p) := by
  rw [realMomentumWeightSpace, LieModule.mem_weightSpace]
  constructor
  · intro hx
    apply (mem_momentum_range_iff_cartan_eigenvectors p (momentumRealValue x)).mpr
    intro i
    have hi := congrArg momentumRealValue (hx (realCartanEquiv (Pi.single i 1)))
    change ⁅cartanClass (complexCoordinates (Pi.single i 1)), momentumRealValue x⁆ =
      (realMomentumWeight p (realCartanEquiv (Pi.single i 1)) : ℂ) • momentumRealValue x at hi
    rw [complexCoordinates_single, realMomentumWeight_coordinates] at hi
    fin_cases i
    · simpa [Pi.single_apply, (cartanEigenvalue_coordinates p).1] using hi
    · simpa [Pi.single_apply, (cartanEigenvalue_coordinates p).2] using hi
  · rintro ⟨a, ha⟩ h
    obtain ⟨f, rfl⟩ := realCartanEquiv.surjective h
    apply Subtype.ext
    change ⁅cartanClass (complexCoordinates f), momentumRealValue x⁆ =
      (realMomentumWeight p (realCartanEquiv f) : ℂ) • momentumRealValue x
    rw [realMomentumWeight_coordinates, ← ha, lie_cartanClass_incl]
    simp only [complexCoordinates, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]

/-- A real eigenspace consists of the included fixed classes in its native momentum quotient. -/
theorem mem_realMomentumWeightSpace_iff_fixed (p : Momentum) (x : momentumRealLie) :
    x ∈ realMomentumWeightSpace p ↔
      ∃ a : H p, coefficientConjugationCohomology p a = a ∧ incl p a = momentumRealValue x :=
  (mem_realMomentumWeightSpace p x).trans (momentumRealValue_mem_incl_range_iff p x)

set_option maxHeartbeats 1000000 in
-- The real and complex brackets must be compared on the concrete cohomology quotients.
/-- Opposite real eigenspaces bracket to the raised momentum with the actual signed coefficient. -/
theorem lie_realMomentumWeightSpace_neg (p : Momentum) (x y : momentumRealLie)
    (hx : x ∈ realMomentumWeightSpace p) (hy : y ∈ realMomentumWeightSpace (-p)) :
    ⁅x, y⁆ = momentumRealBPZ x y • realCartanClass (fun i => (p i : ℝ)) := by
  obtain ⟨a, ha⟩ := (mem_realMomentumWeightSpace p x).mp hx
  obtain ⟨b, hb⟩ := (mem_realMomentumWeightSpace (-p) y).mp hy
  apply Subtype.ext
  change ⁅momentumRealValue x, momentumRealValue y⁆ =
    (momentumRealBPZ x y : ℂ) • cartanClass (complexCoordinates (fun i => (p i : ℝ)))
  have hcoords : complexCoordinates (fun i => (p i : ℝ)) = (fun i : Fin 2 => (p i : ℂ)) :=
    funext fun i => Complex.ofReal_intCast (p i)
  rw [ofReal_momentumRealBPZ, ← ha, ← hb, hcoords]
  exact lie_incl_neg_incl p a b

/-- Every momentum supporting a nonzero real eigenspace vector has squared norm at most two. -/
theorem realMomentumWeight_norm_le_two (p : Momentum) (x : momentumRealLie)
    (hx : x ∈ realMomentumWeightSpace p) (hne : x ≠ 0) :
    momentumRealBPZ (realCartanClass (fun i => (p i : ℝ)))
      (realCartanClass (fun i => (p i : ℝ))) ≤ 2 := by
  obtain ⟨a, ha⟩ := (mem_realMomentumWeightSpace p x).mp hx
  have hane : a ≠ 0 := by
    intro haz
    apply hne
    apply Subtype.ext
    change momentumRealValue x = 0
    rw [← ha, haz, map_zero]
  rw [momentumRealBPZ_momentum]
  exact_mod_cast momentum_norm_le_two_of_ghostOne_ne_zero p a hane

/-- Nonzero null momenta carry no real root vectors. -/
theorem realMomentumWeightSpace_eq_bot_of_null (p : Momentum) (hp : p ≠ 0)
    (hnull : momentumRealBPZ (realCartanClass (fun i => (p i : ℝ)))
      (realCartanClass (fun i => (p i : ℝ))) = 0) :
    realMomentumWeightSpace p = ⊥ := by
  rw [momentumRealBPZ_momentum_norm] at hnull
  have hprod := (mul_eq_zero.mp hnull).resolve_left two_ne_zero
  have hpnull : p (0 : Fin 2) * p (1 : Fin 2) = 0 := by exact_mod_cast hprod
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, ha⟩ := (mem_realMomentumWeightSpace p x).mp hx
  have haz := ghostOne_eq_zero_of_nonzero_null p hp hpnull a
  have hxz : x = 0 := by
    apply Subtype.ext
    change momentumRealValue x = 0
    rw [← ha, haz, map_zero]
  exact (LieSubmodule.mem_bot x).mpr hxz

private def realMomentumComponent (p : Momentum) : momentumRealLie →ₗ[ℝ] H p where
  toFun x := component p (momentumRealValue x)
  map_add' x y := (component p).map_add (momentumRealValue x) (momentumRealValue y)
  map_smul' r x := by
    change component p ((r : ℂ) • momentumRealValue x) =
      (r : ℂ) • component p (momentumRealValue x)
    exact (component p).map_smul (r : ℂ) (momentumRealValue x)

private theorem incl_realMomentumComponent (p : Momentum) {x : momentumRealLie}
    (hx : x ∈ realMomentumWeightSpace p) :
    incl p (realMomentumComponent p x) = momentumRealValue x := by
  classical
  obtain ⟨a, ha⟩ := (mem_realMomentumWeightSpace p x).mp hx
  change incl p (component p (momentumRealValue x)) = _
  rw [← ha, DirectSum.component.lof_self]

/-- Projection into the complex momentum quotient bounds the real weight-space dimension. -/
theorem realMomentumWeightSpace_finiteDimensional (p : Momentum) :
    FiniteDimensional ℝ (realMomentumWeightSpace p) := by
  have := ghostOneMomentum_finiteDimensional p
  have : FiniteDimensional ℝ (H p) := FiniteDimensional.trans ℝ ℂ (H p)
  apply FiniteDimensional.of_injective
    ((realMomentumComponent p).comp (realMomentumWeightSpace p).toSubmodule.subtype)
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  change momentumRealValue x.val = momentumRealValue y.val
  rw [← incl_realMomentumComponent p x.property, ← incl_realMomentumComponent p y.property]
  exact congrArg (incl p) hxy

set_option maxHeartbeats 2500000 in
-- Both direct sums are dependent families of concrete cohomology subquotients.
open scoped Classical in
/-- The real weight spaces give the internal direct sum of the fixed Lie algebra. -/
theorem realMomentumWeightSpace_isInternal :
    DirectSum.IsInternal (fun p : Momentum => (realMomentumWeightSpace p).toSubmodule) := by
  classical
  let A := fun p : Momentum => (realMomentumWeightSpace p).toSubmodule
  let total := DirectSum.coeLinearMap A
  change Function.Bijective total
  have readout (d : ⨁ q, A q) (p : Momentum) :
      realMomentumComponent p (total d) = realMomentumComponent p (d p).val := by
    induction d using DirectSum.induction_on with
    | zero => simp [total]
    | of q a =>
      change realMomentumComponent p (DirectSum.coeLinearMap A (DirectSum.of _ q a)) = _
      rw [DirectSum.coeLinearMap_of]
      by_cases h : p = q
      · subst q
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ h]
        change component p (momentumRealValue a.val) = component p 0
        rw [← incl_realMomentumComponent q a.property, DirectSum.component.of,
          dite_eq_right (Ne.symm h), map_zero]
    | add a b ha hb =>
      simp only [map_add, DirectSum.add_apply, Submodule.coe_add, ha, hb]
  constructor
  · intro a b hab
    apply (DirectSum.ext (ι := Momentum) (β := fun p => A p))
    intro p
    apply Subtype.ext
    apply Subtype.ext
    change momentumRealValue (a p).val = momentumRealValue (b p).val
    have hc : realMomentumComponent p (total a) = realMomentumComponent p (total b) :=
      congrArg (realMomentumComponent p) hab
    exact (incl_realMomentumComponent p (a p).property).symm.trans
      ((congrArg (incl p) ((readout a p).symm.trans (hc.trans (readout b p)))).trans
        (incl_realMomentumComponent p (b p).property))
  · intro x
    have fixed (p : Momentum) :
        coefficientConjugationCohomology p (momentumRealValue x p) = momentumRealValue x p := by
      have h := congrArg (fun z : MomentumH1 => z p) (momentumConjugation_realValue x)
      exact (momentumConjugationAddHom_apply p (momentumRealValue x)).symm.trans h
    let entry (p : Momentum) : A p :=
      let a := momentumRealValue x p
      let y : momentumRealLie := ⟨incl p a, by
        change coefficientConjugationMomentum (incl p a) = incl p a
        rw [coefficientConjugationMomentum_incl, fixed p]⟩
      ⟨y, (mem_realMomentumWeightSpace p y).mpr ⟨a, rfl⟩⟩
    refine ⟨DirectSum.mk (fun q => ↥(A q)) (momentumRealValue x).support
      (fun p => entry p.val), ?_⟩
    apply Subtype.ext
    apply DirectSum.ext_component ℂ
    intro p
    change realMomentumComponent p (total _) = component p (momentumRealValue x)
    rw [readout]
    by_cases hp : p ∈ (momentumRealValue x).support
    · rw [DirectSum.mk_apply_of_mem hp]
      exact DirectSum.component.lof_self ℂ p _
    · rw [DirectSum.mk_apply_of_notMem hp]
      change component p 0 = momentumRealValue x p
      rw [map_zero, DFinsupp.notMem_support_iff.mp hp]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
