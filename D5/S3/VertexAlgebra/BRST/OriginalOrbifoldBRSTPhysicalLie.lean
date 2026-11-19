/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalLie
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalLie
   mirror-E: none(waiver:algebraic-native-brst-physical-lie)
   anchors: []
   utility: none
   digest: The native odd relative Lie algebra and its integer ghost-number covariance. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentJacobi
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance
import Mathlib.Algebra.Lie.Basic

/-! The native relative bracket and its restriction by the original bc ghost number. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalLie

open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum)
open OriginalOrbifoldBRSTStateField (Y modeSummand modeSummand_finite Y_ncoeff_apply)
open OriginalOrbifoldBRSTDescent
open OriginalOrbifoldBRSTDescentJacobi
open D5.S3.Quantum.Fermionic
open Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance (ghost_number_field)

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

instance oddLieRing : LieRing oddRelativeCohomology where
  bracket x y := ⟨cohomologyDescent x y, cohomologyDescent_mem_odd x y x.property y.property⟩
  add_lie x y z := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add cohomologyDescent (x : RelativeCohomology) y) z
  lie_add x y z := by
    apply Subtype.ext
    exact map_add (cohomologyDescent x) (y : RelativeCohomology) z
  lie_self x := by
    apply Subtype.ext
    have h := cohomologyDescent_skew x x x.property x.property
    have hz : (2 : ℂ) • cohomologyDescent x x = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h
    change cohomologyDescent x x = 0
    have hhalf : (2 : ℂ)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by norm_num)
    have hz' := congrArg (fun z : RelativeCohomology => (2 : ℂ)⁻¹ • z) hz
    simpa only [smul_smul, hhalf, one_smul, smul_zero] using hz'
  leibniz_lie x y z :=
    Subtype.ext (cohomologyDescent_leftLeibniz x y z x.property y.property)

instance oddLieAlgebra : LieAlgebra ℂ oddRelativeCohomology where
  lie_smul t x y := Subtype.ext (map_smul (cohomologyDescent x) t (y : RelativeCohomology))

/-- The original ghost number on the Monster-matter tensor with the bc state space. -/
abbrev N : Module.End ℂ State := VirasoroBRST.N matterDatum

open private modeSummand_tmul from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField

private theorem number_modeSummand (x : State) (n k : ℤ) :
    N * modeSummand n k x - modeSummand n k x * N = modeSummand n k (N x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v w
    have h := LinearMap.congr_fun (ghost_number_field a (n - 1 - k)) w
    simpa only [N, VirasoroBRST.N, VirasoroBRST.number, BcGhostChargeTensor.number,
      BcGhostChargeTensor.liftGhost, modeSummand_tmul, Module.End.mul_apply,
      LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      ← TensorProduct.tmul_sub] using
      congrArg (fun t => ((OriginalOrbifoldMatterTensorField.stateField u)[[k]]) v ⊗ₜ[ℂ] t) h
  | add x y hx hy =>
    simp only [map_add, mul_add, add_mul]
    rw [show ∀ A B C D : Module.End ℂ State, A + B - (C + D) = (A - C) + (B - D) by
      intros
      abel, hx, hy]

/-- Ghost number obeys the derivation law for each mode of the native state-field map. -/
theorem number_mode (x y : State) (n : ℤ) :
    N (((Y x)[[n]]) y) = ((Y (N x))[[n]]) y + ((Y x)[[n]]) (N y) := by
  apply sub_eq_iff_eq_add.mp
  simp only [Y_ncoeff_apply]
  rw [map_finsum N (modeSummand_finite x y n),
    ← finsum_sub_distrib ((modeSummand_finite x y n).fun_comp (map_zero N))
      (modeSummand_finite x (N y) n)]
  exact finsum_congr (fun k => LinearMap.congr_fun (number_modeSummand x n k) y)

private theorem number_b_commutator (m : ℤ) :
    N * b m - b m * N = -b m := by
  apply TensorProduct.ext'
  intro u w
  have h := LinearMap.congr_fun (BcGhostCharge.ghost_number_relations.2.1 m) w
  simpa only [N, VirasoroBRST.N, VirasoroBRST.number, b, VirasoroBRST.ghostB,
    BcGhostChargeTensor.number, BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    Module.End.mul_apply, ← TensorProduct.tmul_sub, TensorProduct.tmul_neg] using
    congrArg (fun t => u ⊗ₜ[ℂ] t) h

/-- Every native antighost mode lowers ghost number by one. -/
theorem number_b (m : ℤ) (x : State) : N (b m x) = b m (N x) - b m x := by
  have h : N (b m x) - b m (N x) = -b m x :=
    LinearMap.congr_fun (number_b_commutator m) x
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- The native descent has degree minus one, before taking the quotient. -/
theorem number_descent (x y : State) :
    N (descent x y) = descent (N x) y + descent x (N y) - descent x y := by
  change N (((Y (b (-1) x))[[0]]) y) =
    ((Y (b (-1) (N x)))[[0]]) y + ((Y (b (-1) x))[[0]]) (N y) -
      ((Y (b (-1) x))[[0]]) y
  rw [number_mode, number_b]
  simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply]
  abel

/-- The literal native descent adds the two integer ghost numbers and subtracts one. -/
theorem descent_number (x y : State) (p q : ℤ)
    (hx : N x = (p : ℂ) • x) (hy : N y = (q : ℂ) • y) :
    N (descent x y) = ((p + q - 1 : ℤ) : ℂ) • descent x y := by
  rw [number_descent, hx, hy]
  simp only [map_smul, LinearMap.smul_apply, Int.cast_sub, Int.cast_add, Int.cast_one]
  module

/-- The original BRST charge raises ghost number by one on the native carrier. -/
theorem number_Q (x : State) : N (Q x) = Q (N x) + Q x :=
  (sub_eq_iff_eq_add.mp (LinearMap.congr_fun (VirasoroBRST.N_Q matterDatum) x)).trans
    (add_comm _ _)

open OriginalOrbifoldBRSTZeroEnergy (totalL0)
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open private ward cycle_closed from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

private theorem number_totalL0 (x : State) : N (totalL0 x) = totalL0 (N x) := by
  rw [← ward 0 (N x), ← ward 0 x, map_add, number_Q (b 0 x), number_b 0 x,
    number_b 0 (Q x), number_Q x, Q.map_sub, (b 0).map_add]
  abel

private theorem number_mem_relativeStates (x : State) (hx : x ∈ relativeStates) :
    N x ∈ relativeStates := by
  change b 0 x = 0 ∧ totalL0 x = 0 at hx
  change b 0 (N x) = 0 ∧ totalL0 (N x) = 0
  constructor
  · simpa only [hx.1, map_zero, sub_zero] using (number_b 0 x).symm
  · rw [← number_totalL0, hx.2, map_zero]

private def relativeNumber : Module.End ℂ relativeStates :=
  N.restrict number_mem_relativeStates

/-- The native ghost number restricted to relative cycles. -/
def cycleNumber : Module.End ℂ relativeCycles :=
  relativeNumber.restrict (by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Q (N (x : State)) = 0
    simpa only [cycle_closed ⟨x, hx⟩, map_zero, add_zero] using (number_Q (x : State)).symm)

/-- Ghost number on the same relative kernel modulo the relative boundary image. -/
def cohomologyNumber : Module.End ℂ RelativeCohomology :=
  relativeBoundaries.mapQ relativeBoundaries cycleNumber (by
    intro x hx
    change ∃ z, boundaryMap relativeDifferential relativeDifferential_square z = x at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨relativeNumber z + z, Subtype.ext (Subtype.ext ?_)⟩
    change Q (N (z : State) + (z : State)) = N (Q (z : State))
    rw [map_add, number_Q])

/-- The quotient endomorphism acts by the native operator on cycle representatives. -/
theorem cohomologyNumber_mk (x : relativeCycles) :
    cohomologyNumber (relativeBoundaries.mkQ x) =
      relativeBoundaries.mkQ (cycleNumber x) := rfl

/-- Ghost number obeys the degree-minus-one rule on arbitrary relative classes. -/
theorem cohomologyNumber_descent (x y : RelativeCohomology) :
    cohomologyNumber (cohomologyDescent x y) =
      cohomologyDescent (cohomologyNumber x) y + cohomologyDescent x (cohomologyNumber y) -
        cohomologyDescent x y := by
  refine Exists.elim (relativeBoundaries.mkQ_surjective x) fun u hu => ?_
  refine Exists.elim (relativeBoundaries.mkQ_surjective y) fun v hv => ?_
  rw [← hu, ← hv]
  simp only [cohomologyDescent_mk, cohomologyNumber_mk, ← map_sub, ← map_add]
  apply congrArg relativeBoundaries.mkQ
  exact Subtype.ext (Subtype.ext (number_descent (u.1 : State) (v.1 : State)))

/-- The integer eigenspaces of the native ghost number on relative cohomology. -/
def grade (p : ℤ) : Submodule ℂ RelativeCohomology :=
  cohomologyNumber.eigenspace (p : ℂ)

/-- Integer ghost numbers add with a shift of minus one under the existing quotient product. -/
theorem cohomologyDescent_mem_grade (x y : RelativeCohomology) (p q : ℤ)
    (hx : x ∈ grade p) (hy : y ∈ grade q) : cohomologyDescent x y ∈ grade (p + q - 1) := by
  change cohomologyDescent x y ∈ cohomologyNumber.eigenspace ((p + q - 1 : ℤ) : ℂ)
  have hxp := Module.End.mem_eigenspace_iff.mp
    (show x ∈ cohomologyNumber.eigenspace (p : ℂ) from hx)
  have hyq := Module.End.mem_eigenspace_iff.mp
    (show y ∈ cohomologyNumber.eigenspace (q : ℂ) from hy)
  apply (Module.End.mem_eigenspace_iff (f := cohomologyNumber)).mpr
  calc
    _ = cohomologyDescent (cohomologyNumber x) y +
        cohomologyDescent x (cohomologyNumber y) - cohomologyDescent x y :=
      cohomologyNumber_descent x y
    _ = cohomologyDescent ((p : ℂ) • x) y +
        cohomologyDescent x ((q : ℂ) • y) - cohomologyDescent x y :=
      congrArg (fun z : RelativeCohomology => z - cohomologyDescent x y)
        (congrArg₂ (fun a b : RelativeCohomology => a + b)
          (congrArg (fun a : RelativeCohomology => cohomologyDescent a y) hxp)
          (congrArg (cohomologyDescent x) hyq))
    _ = _ := by
      simp only [map_smul, LinearMap.smul_apply, Int.cast_sub, Int.cast_add, Int.cast_one,
        add_smul, sub_smul, one_smul]

open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldBRSTSignedLocality (parity)
open BcGhostCharge (charge)
open private fullBasis_apply from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private charge_one_sign from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance
open private cycleParity cohomologyParity_mk from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescentJacobi

private theorem number_basis (i : FullLabel) :
    N (fullBasis i) = (charge i.2.2 : ℂ) • fullBasis i := by
  rw [fullBasis_apply]
  simp only [N, VirasoroBRST.N, VirasoroBRST.number, BcGhostChargeTensor.number,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply, number_ket,
    TensorProduct.tmul_smul]

private theorem number_coordinate (x : State) (i : FullLabel) :
    fullBasis.repr (N x) i = (charge i.2.2 : ℂ) * fullBasis.repr x i := by
  classical
  let c : State →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp fullBasis.repr.toLinearMap
  have h : c.comp N = (charge i.2.2 : ℂ) • c := by
    apply fullBasis.ext
    intro j
    rw [LinearMap.comp_apply, number_basis, map_smul, LinearMap.smul_apply]
    by_cases hji : j = i
    · subst j
      rfl
    · have hz : c (fullBasis j) = 0 := by
        simp [c, Module.Basis.repr_self, hji]
      simp [hz]
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 500000 in
-- The finite-support induction elaborates through both relative subtypes.
/-- A relative eigenclass has a relative cycle representative of the same native ghost number. -/
theorem homogeneous_cycle_lift (p : ℤ) (a : RelativeCohomology) (ha : a ∈ grade p) :
    ∃ z : relativeCycles, relativeBoundaries.mkQ z = a ∧
      N (z.1 : State) = (p : ℂ) • (z.1 : State) := by
  classical
  let cl := relativeBoundaries.mkQ
  have ha' : cohomologyNumber a = (p : ℂ) • a :=
    Module.End.mem_eigenspace_iff.mp
      (show a ∈ cohomologyNumber.eigenspace (p : ℂ) from ha)
  -- Apply normalized linear factors in N to erase the unwanted degrees of a lift.
  -- The corresponding factors on the quotient fix the target eigenclass.
  have lift : ∀ (S : Finset ℤ) (z : relativeCycles), cl z = a →
      (∀ i : FullLabel, charge i.2.2 ≠ p → charge i.2.2 ∉ S →
        fullBasis.repr (z.1 : State) i = 0) →
      ∃ w : relativeCycles, cl w = a ∧ N (w.1 : State) = (p : ℂ) • (w.1 : State) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hz hs
      refine ⟨z, hz, ?_⟩
      apply fullBasis.repr.injective
      ext i
      rw [number_coordinate, map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hi : charge i.2.2 = p
      · rw [hi]
      · simp [hs i hi (Finset.notMem_empty _)]
    | @insert q S hq ih =>
      intro z hz hs
      by_cases he : q = p
      · apply ih z hz
        intro i hi hiS
        exact hs i hi (by simp [he, hi, hiS])
      · let d : ℂ := (p : ℂ) - (q : ℂ)
        have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => he ((Int.cast_injective (α := ℂ) h).symm))
        let w : relativeCycles := d⁻¹ • (cycleNumber z - (q : ℂ) • z)
        apply ih w
        · have hN : cl (cycleNumber z) = (p : ℂ) • a :=
            (cohomologyNumber_mk z).symm.trans ((congrArg cohomologyNumber hz).trans ha')
          have hqz : cl ((q : ℂ) • z) = (q : ℂ) • a :=
            (cl.map_smul (q : ℂ) z).trans
              (congrArg (fun t : RelativeCohomology => (q : ℂ) • t) hz)
          have hdiff : cl (cycleNumber z - (q : ℂ) • z) = d • a :=
            (cl.map_sub _ _).trans
              ((congrArg₂ (fun s t : RelativeCohomology => s - t) hN hqz).trans
                (sub_smul (p : ℂ) (q : ℂ) a).symm)
          calc
            cl w = d⁻¹ • cl (cycleNumber z - (q : ℂ) • z) := cl.map_smul _ _
            _ = d⁻¹ • (d • a) := congrArg (fun t : RelativeCohomology => d⁻¹ • t) hdiff
            _ = a := by simp only [smul_smul, inv_mul_cancel₀ hd, one_smul]
        · intro i hi hiS
          let c : State →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp fullBasis.repr.toLinearMap
          change c (d⁻¹ • (N (z.1 : State) - (q : ℂ) • (z.1 : State))) = 0
          rw [c.map_smul d⁻¹, c.map_sub, c.map_smul (q : ℂ)]
          change d⁻¹ * (fullBasis.repr (N (z.1 : State)) i -
            (q : ℂ) * fullBasis.repr (z.1 : State) i) = 0
          rw [number_coordinate]
          by_cases hqi : charge i.2.2 = q
          · simp only [hqi, sub_self, mul_zero]
          · have hout : charge i.2.2 ∉ insert q S :=
              fun hm => (Finset.mem_insert.mp hm).elim hqi hiS
            simp only [hs i hi hout, mul_zero, sub_self]
  obtain ⟨z, hz⟩ := relativeBoundaries.mkQ_surjective a
  refine lift ((fullBasis.repr (z.1 : State)).support.image fun i => charge i.2.2) z hz ?_
  intro i _ hi
  apply Finsupp.notMem_support_iff.mp
  exact fun h => hi (Finset.mem_image.mpr ⟨i, h, rfl⟩)

private theorem parity_basis (i : FullLabel) :
    parity (fullBasis i) = (-1 : ℂ) ^ i.2.2.card • fullBasis i := by
  rw [fullBasis_apply]
  simp only [parity, TensorProduct.map_tmul, LinearMap.id_apply, parity_ket,
    TensorProduct.tmul_smul]

private theorem number_one_parity (x : State) (hx : N x = x) : parity x = -x := by
  classical
  have expand : x = ∑ i ∈ (fullBasis.repr x).support, fullBasis.repr x i • fullBasis i := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (fullBasis.linearCombination_repr x).symm
  conv_lhs => rw [expand]
  rw [map_sum]
  conv_rhs => rw [expand]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have nz := Finsupp.mem_support_iff.mp hi
  have h : (charge i.2.2 : ℂ) * fullBasis.repr x i = 1 * fullBasis.repr x i := by
    rw [← number_coordinate, hx, one_mul]
  have hc : charge i.2.2 = 1 := by
    exact_mod_cast mul_right_cancel₀ nz h
  rw [map_smul, parity_basis, charge_one_sign i.2.2 hc, neg_one_smul, smul_neg]

set_option maxHeartbeats 500000 in
-- Coercions from the relative cycle to the native state run through two subtypes.
/-- A native relative ghost-number-one class belongs to the odd Lie algebra. -/
theorem grade_one_le_odd : grade 1 ≤ oddRelativeCohomology := by
  intro a ha
  refine Exists.elim (homogeneous_cycle_lift 1 a ha) fun z ⟨hz, hn⟩ => ?_
  have hn' : N (z.1 : State) = (z.1 : State) := by
    simpa only [Int.cast_one, one_smul] using hn
  have hp : cycleParity z = -z := by
    apply Subtype.ext
    apply Subtype.ext
    change parity (z.1 : State) = -(z.1 : State)
    exact number_one_parity (z.1 : State) hn'
  have hc : cohomologyParity (relativeBoundaries.mkQ z) = -relativeBoundaries.mkQ z :=
    (cohomologyParity_mk z).trans
      ((congrArg relativeBoundaries.mkQ hp).trans (relativeBoundaries.mkQ.map_neg z))
  apply LinearMap.mem_ker.mpr
  change cohomologyParity a + a = 0
  exact eq_neg_iff_add_eq_zero.mp
    ((congrArg cohomologyParity hz).symm.trans
      (hc.trans (congrArg (fun t : RelativeCohomology => -t) hz)))

/-- The physical component is the actual ghost-number-one eigenspace of the relative quotient. -/
abbrev DegreeOne := grade 1

private def toOdd (x : DegreeOne) : oddRelativeCohomology :=
  ⟨x, grade_one_le_odd x.property⟩

instance degreeOneLieRing : LieRing DegreeOne where
  bracket x y := ⟨cohomologyDescent x y, by
    simpa only [show (1 + 1 - 1 : ℤ) = 1 by decide] using
      cohomologyDescent_mem_grade x y 1 1 x.property y.property⟩
  add_lie x y z := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add cohomologyDescent (x : RelativeCohomology) y) z
  lie_add x y z := by
    apply Subtype.ext
    exact map_add (cohomologyDescent x) (y : RelativeCohomology) z
  lie_self x := Subtype.ext
    (congrArg (fun w : oddRelativeCohomology => (w : RelativeCohomology)) (lie_self (toOdd x)))
  leibniz_lie x y z := Subtype.ext
    (congrArg (fun w : oddRelativeCohomology => (w : RelativeCohomology))
      (leibniz_lie (toOdd x) (toOdd y) (toOdd z)))

instance degreeOneLieAlgebra : LieAlgebra ℂ DegreeOne where
  lie_smul t x y := Subtype.ext (map_smul (cohomologyDescent x) t (y : RelativeCohomology))

/-- The degree-one inclusion preserves the existing odd relative Lie bracket. -/
def degreeOneInclusion : DegreeOne →ₗ⁅ℂ⁆ oddRelativeCohomology where
  toFun := toOdd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

/-- Forgetting the degree-one proof gives the original relative descent of the two classes. -/
theorem degreeOne_bracket (x y : DegreeOne) :
    (↑⁅x, y⁆ : RelativeCohomology) = cohomologyDescent x y := rfl

#print axioms oddLieRing
#print axioms oddLieAlgebra
#print axioms N
#print axioms number_mode
#print axioms number_b
#print axioms number_descent
#print axioms descent_number
#print axioms number_Q
#print axioms cycleNumber
#print axioms cohomologyNumber
#print axioms cohomologyNumber_mk
#print axioms cohomologyNumber_descent
#print axioms grade
#print axioms cohomologyDescent_mem_grade
#print axioms homogeneous_cycle_lift
#print axioms grade_one_le_odd
#print axioms DegreeOne
#print axioms degreeOneLieRing
#print axioms degreeOneLieAlgebra
#print axioms degreeOneInclusion
#print axioms degreeOne_bracket

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalLie
