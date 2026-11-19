/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescent
   mirror-E: none(waiver:algebraic-original-brst-descent)
   anchors: []
   utility: none
   digest: Native descent preserves relative BRST cycles and both boundary ideals. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTModeDerivation
import D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

/-!
The negative-two vacuum residue removes translation from the BRST identity.
The actual antighost CAR and Ward identities then put both boundary
primitives in the relative state space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescent

open D5.S3.Quantum.Fermionic
open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries Cohomology boundaryMap)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum matterVacuum vacuum
  Q_squared Q_ward_b)
open OriginalOrbifoldBRSTStateField (Y J Y_vacuum b_modes current_zero_mode)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTFieldAxioms (translation translation_eq_total_mode translation_vacuum
  parity_involution stateField_covariance stateField_creation stateField_parity)
open OriginalOrbifoldBRSTModeDerivation (Q_mode b_minus_one_mode b_zero_mode)
open OriginalOrbifoldBRSTSuperJacobi (residueClosure)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open private identity_ncoeff from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField
open private of_parity_eigenspaces antighost_odd current_odd from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTModeDerivation
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev L0 : Module.End ℂ State := VirasoroBRST.Ltotal matterDatum 0

private theorem parity_square (x : State) : parity (parity x) = x :=
  LinearMap.congr_fun parity_involution x

private theorem parity_vacuum : parity vacuum = (-1 : ℂ) ^ 0 • vacuum := by
  simp [parity, vacuum, TensorProduct.map_tmul, CountableOccupationFock.vacuum, parity_ket]

private theorem translation_creation (x : State) : ((Y x)[[-2]]) vacuum = translation x := by
  have eq := LinearMap.congr_fun (stateField_covariance x (-1)) vacuum
  simpa [Module.End.mul_apply, stateField_creation, translation_vacuum] using eq.symm

/-- The actual field of a translated state has zero residue. -/
theorem translation_zero_mode (x y : State) : ((Y (translation x))[[0]]) y = 0 := by
  apply of_parity_eigenspaces (fun a => ((Y (translation a))[[0]]) y = 0) _ _ x
  · intro u v hu hv
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hu, hv, add_zero]
  · intro a p ha
    have law := residueClosure a vacuum p 0 ha parity_vacuum (-2)
    rw [translation_creation, Y_vacuum] at law
    rw [law, (residueField _ _ _ _).coefficient, residueCoefficient]
    have leftZero : residueLeft (-2) 0 (Y a) FieldNormalProduct.identityField y = 0 := by
      unfold residueLeft
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      simp only [identity_ncoeff, ite_eq_right (show (0 : ℤ) + i ≠ -1 by omega),
        LinearMap.zero_apply, map_zero, smul_zero]
    have rightZero : residueRight (-2) 0 (Y a) FieldNormalProduct.identityField y = 0 := by
      unfold residueRight
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      simp only [identity_ncoeff, ite_eq_right (show (-2 : ℤ) + 0 - i ≠ -1 by omega),
        LinearMap.zero_apply, smul_zero]
    rw [leftZero, rightZero, smul_zero, sub_zero]

private theorem Q_parity (x : State) : Q (parity x) = -parity (Q x) := by
  have law := LinearMap.congr_fun (stateField_parity J 0) x
  rw [current_odd] at law
  simp only [pow_one, neg_one_smul, map_neg, Pi.neg_apply, Module.End.mul_apply,
    LinearMap.neg_apply, current_zero_mode] at law
  rw [law, neg_neg]

private theorem b_parity (r : ℤ) (x : State) : parity (b r x) = -b r (parity x) := by
  have law := LinearMap.congr_fun
    (stateField_parity (matterVacuum ⊗ₜ[ℂ] CountableOccupationFock.ket {0}) (r + 1)) x
  rw [antighost_odd] at law
  simpa only [pow_one, neg_one_smul, map_neg, Pi.neg_apply, Module.End.mul_apply,
    LinearMap.neg_apply, b_modes, add_sub_cancel_right] using law

private theorem b_zero_parity (x : State) : b 0 (parity x) = -parity (b 0 x) := by
  rw [b_parity, neg_neg]

private theorem b_car (m n : ℤ) (x : State) :
    b m (b n x) + b n (b m x) = 0 := by
  have law : b m * b n + b n * b m = 0 := by
    apply TensorProduct.ext'
    intro v w
    have ghost := LinearMap.congr_fun (BcGhostFock.ghost_b_car m n) w
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at ghost
    simp only [b, VirasoroBRST.ghostB, BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost,
      LinearMap.add_apply, Module.End.mul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_add, ghost, TensorProduct.tmul_zero]
  exact LinearMap.congr_fun law x

private theorem b_square (m : ℤ) (x : State) : b m (b m x) = 0 := by
  have twice : (2 : ℂ) • b m (b m x) = 0 := by
    rw [two_smul]
    exact b_car m m x
  exact (smul_eq_zero.mp twice).resolve_left (by norm_num)

private theorem ward (r : ℤ) (x : State) :
    Q (b r x) + b r (Q x) = VirasoroBRST.Ltotal matterDatum r x :=
  LinearMap.congr_fun (Q_ward_b r) x

/-- The conventional unsigned descent product on the actual state space. -/
def descent : State →ₗ[ℂ] Module.End ℂ State where
  toFun x := (Y (b (-1) x))[[0]]
  map_add' x y := by simp only [map_add, Pi.add_apply]
  map_smul' c x := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The BRST superderivation law for the odd descent product. -/
theorem descent_Q (x y : State) :
    Q (descent x y) = -descent (Q x) y - descent (parity x) (Q y) := by
  have qb : Q (b (-1) x) = translation x - b (-1) (Q x) :=
    eq_sub_of_add_eq (by rw [translation_eq_total_mode]; exact ward (-1) x)
  change Q (((Y (b (-1) x))[[0]]) y) = _
  rw [Q_mode, qb, b_parity]
  simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, translation_zero_mode, zero_sub,
    map_neg, Pi.neg_apply, LinearMap.neg_apply]
  rfl

/-- The normalized zeroth antighost mode acts on descent by the odd product law. -/
theorem descent_b_minus_one (x y : State) :
    b (-1) (descent x y) = -descent (parity x) (b (-1) y) := by
  change b (-1) (((Y (b (-1) x))[[0]]) y) = _
  rw [b_minus_one_mode, b_square, b_parity]
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, zero_add,
    map_neg, Pi.neg_apply, LinearMap.neg_apply]
  rfl

/-- The extra mode in the native b(0) commutator vanishes by the antighost CAR. -/
theorem descent_b_zero (x y : State) :
    b 0 (descent x y) = -descent (b 0 x) y - descent (parity x) (b 0 y) := by
  have cross := eq_neg_iff_add_eq_zero.mpr (b_car 0 (-1) x)
  change b 0 (((Y (b (-1) x))[[0]]) y) = _
  rw [b_zero_mode, cross, b_square, b_parity]
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply, map_zero, Pi.zero_apply,
    LinearMap.zero_apply, add_zero, sub_eq_add_neg]
  rfl

/-- Total energy acts on descent by the ordinary product law. -/
theorem descent_L0 (x y : State) :
    VirasoroBRST.Ltotal matterDatum 0 (descent x y) =
      descent (VirasoroBRST.Ltotal matterDatum 0 x) y +
        descent x (VirasoroBRST.Ltotal matterDatum 0 y) := by
  rw [← ward 0 (descent x y), ← ward 0 x, ← ward 0 y, descent_b_zero, descent_Q]
  rw [Q.map_sub, Q.map_neg, (b 0).map_sub, (b 0).map_neg,
    descent_Q (b 0 x) y, descent_Q (parity x) (b 0 y),
    descent_b_zero (Q x) y, descent_b_zero (parity x) (Q y),
    Q_parity, b_zero_parity, parity_square,
    LinearMap.congr_fun (descent.map_add (Q (b 0 x)) (b 0 (Q x))) y,
    LinearMap.add_apply (descent (Q (b 0 x))) (descent (b 0 (Q x))) y,
    (descent x).map_add]
  simp only [map_neg, LinearMap.neg_apply]
  abel

/-- The space of native relative states across all hyperbolic momenta. -/
def relativeStates : Submodule ℂ State := LinearMap.ker (b 0) ⊓ LinearMap.ker L0

private theorem parity_mem_relativeStates (x : State) (hx : x ∈ relativeStates) :
    parity x ∈ relativeStates := by
  change b 0 x = 0 ∧ L0 x = 0 at hx
  change b 0 (parity x) = 0 ∧ L0 (parity x) = 0
  have hb : b 0 (parity x) = 0 := by
    rw [b_zero_parity, hx.1, map_zero, neg_zero]
  have hQ : b 0 (Q x) = 0 := by
    simpa only [hx.1, hx.2, map_zero, zero_add] using ward 0 x
  refine ⟨hb, ?_⟩
  rw [← ward 0 (parity x), hb, Q_parity, Q.map_zero, zero_add,
    (b 0).map_neg, b_zero_parity, hQ, map_zero, neg_zero, neg_zero]

/-- The native Q preserves the two relative constraints. -/
theorem Q_mem_relativeStates (x : State) (hx : x ∈ relativeStates) :
    Q x ∈ relativeStates := by
  change b 0 x = 0 ∧ L0 x = 0 at hx
  change b 0 (Q x) = 0 ∧ L0 (Q x) = 0
  have hb : b 0 (Q x) = 0 := by
    simpa only [hx.1, hx.2, map_zero, zero_add] using ward 0 x
  have hQ : Q (Q x) = 0 := by
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun Q_squared x
  exact ⟨hb, by rw [← ward 0 (Q x), hb, hQ, Q.map_zero, (b 0).map_zero, add_zero]⟩

/-- Descent preserves the relative constraints even for primitives that are not cycles. -/
theorem descent_mem_relativeStates (x y : State) (hx : x ∈ relativeStates)
    (hy : y ∈ relativeStates) : descent x y ∈ relativeStates := by
  change b 0 x = 0 ∧ L0 x = 0 at hx
  change b 0 y = 0 ∧ L0 y = 0 at hy
  change b 0 (descent x y) = 0 ∧ L0 (descent x y) = 0
  refine ⟨?_, ?_⟩
  · rw [descent_b_zero, hx.1, hy.1]
    simp only [map_zero, LinearMap.zero_apply, neg_zero, sub_zero]
  · rw [descent_L0, hx.2, hy.2]
    simp only [map_zero, LinearMap.zero_apply, add_zero]

/-- Two native relative cycles descend to a native relative cycle. -/
theorem descent_cycle (x y : State) (hx : x ∈ relativeStates) (hy : y ∈ relativeStates)
    (hQx : Q x = 0) (hQy : Q y = 0) :
    descent x y ∈ relativeStates ∧ Q (descent x y) = 0 :=
  ⟨descent_mem_relativeStates x y hx hy, by
    rw [descent_Q, hQx, hQy]
    simp only [map_zero, LinearMap.zero_apply, neg_zero, sub_zero]⟩

/-- A left relative boundary has the explicit relative primitive -D(z,y). -/
theorem descent_left_boundary (z y : State) (hz : z ∈ relativeStates)
    (hy : y ∈ relativeStates) (hQy : Q y = 0) :
    -descent z y ∈ relativeStates ∧ Q (-descent z y) = descent (Q z) y :=
  ⟨relativeStates.neg_mem (descent_mem_relativeStates z y hz hy),
    by rw [Q.map_neg, descent_Q, hQy, map_zero, sub_zero, neg_neg]⟩

/-- A right relative boundary has the explicit relative primitive -D(parity x,z). -/
theorem descent_right_boundary (x z : State) (hx : x ∈ relativeStates)
    (hz : z ∈ relativeStates) (hQx : Q x = 0) :
    -descent (parity x) z ∈ relativeStates ∧
      Q (-descent (parity x) z) = descent x (Q z) := by
  refine ⟨relativeStates.neg_mem
    (descent_mem_relativeStates (parity x) z (parity_mem_relativeStates x hx) hz), ?_⟩
  rw [Q.map_neg, descent_Q, Q_parity, hQx, map_zero, neg_zero, parity_square]
  simp only [map_zero, LinearMap.zero_apply, neg_zero, zero_sub, neg_neg]

/-- The actual charge restricted to its relative state space. -/
def relativeDifferential : Module.End ℂ relativeStates := Q.restrict Q_mem_relativeStates

theorem relativeDifferential_square : relativeDifferential * relativeDifferential = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (by simpa only [pow_two] using Q_squared) (x : State)

abbrev relativeCycles := LinearMap.ker relativeDifferential

abbrev relativeBoundaries := Boundaries relativeDifferential relativeDifferential_square

/-- The kernel modulo the actual relative image, using the existing cohomology construction. -/
abbrev RelativeCohomology := Cohomology relativeDifferential relativeDifferential_square

private theorem cycle_closed (x : relativeCycles) : Q (x.1 : State) = 0 :=
  congrArg Subtype.val (LinearMap.mem_ker.mp x.property)

/-- Restriction of the native descent product to the relative cycles. -/
def cycleDescent : relativeCycles →ₗ[ℂ] Module.End ℂ relativeCycles where
  toFun x := {
    toFun y := by
      have h := descent_cycle (x.1 : State) (y.1 : State) x.1.property y.1.property
        (cycle_closed x) (cycle_closed y)
      exact ⟨⟨_, h.1⟩, LinearMap.mem_ker.mpr (Subtype.ext h.2)⟩
    map_add' y z := Subtype.ext (Subtype.ext (map_add (descent (x.1 : State)) _ _))
    map_smul' c y := Subtype.ext (Subtype.ext (map_smul (descent (x.1 : State)) _ _)) }
  map_add' x y := by
    ext z
    exact congrArg (fun f : Module.End ℂ State => f (z.1 : State))
      (map_add descent (x.1 : State) (y.1 : State))
  map_smul' c x := by
    ext y
    exact congrArg (fun f : Module.End ℂ State => f (y.1 : State))
      (map_smul descent c (x.1 : State))

private def cycleClassDescent : relativeCycles →ₗ[ℂ] relativeCycles →ₗ[ℂ] RelativeCohomology where
  toFun x := relativeBoundaries.mkQ.comp (cycleDescent x)
  map_add' x y := by ext z; simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c x := by
    ext y
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Descent induces a complex-bilinear operation on the all-momentum relative quotient. -/
def cohomologyDescent : RelativeCohomology →ₗ[ℂ] Module.End ℂ RelativeCohomology :=
  cycleClassDescent.liftQ₂ relativeBoundaries relativeBoundaries
    (by
      rintro x ⟨z, rfl⟩
      apply LinearMap.mem_ker.mpr
      ext y
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have h := descent_left_boundary (z : State) (y.1 : State) z.property y.1.property
        (cycle_closed y)
      exact ⟨⟨_, h.1⟩, Subtype.ext (Subtype.ext h.2)⟩)
    (by
      rintro y ⟨z, rfl⟩
      apply LinearMap.mem_ker.mpr
      ext x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have h := descent_right_boundary (x.1 : State) (z : State) x.1.property z.property
        (cycle_closed x)
      exact ⟨⟨_, h.1⟩, Subtype.ext (Subtype.ext h.2)⟩)

/-- On representatives the induced operation is the class of the original descent product. -/
theorem cohomologyDescent_mk (x y : relativeCycles) :
    cohomologyDescent (relativeBoundaries.mkQ x) (relativeBoundaries.mkQ y) =
      relativeBoundaries.mkQ (cycleDescent x y) := rfl

#print axioms translation_zero_mode
#print axioms descent
#print axioms descent_Q
#print axioms descent_b_minus_one
#print axioms descent_b_zero
#print axioms descent_L0
#print axioms Q_mem_relativeStates
#print axioms descent_mem_relativeStates
#print axioms descent_cycle
#print axioms descent_left_boundary
#print axioms descent_right_boundary
#print axioms relativeDifferential_square
#print axioms cycleDescent
#print axioms cohomologyDescent
#print axioms cohomologyDescent_mk

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescent
