/- GID: D5/S3/HomologicalAlgebra/ParityOddKunneth
   generality: T
   mirror-B: D5/B/S3/HomologicalAlgebra/ParityOddKunneth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic Künneth equivalence for parity-odd differentials over the complex numbers. -/

import D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
import Mathlib.Algebra.Module.Projective
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.Module

/-!
# Algebraic Künneth for parity-odd differentials over ℂ

The proof uses parity-equivariant sections and a tensor homotopy.
The cohomology in each factor and on the tensor is the literal kernel modulo
the range of the differential restricted to its kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.HomologicalAlgebra.ParityOddKunneth

open FinitePerturbation (boundaryMap Boundaries Cohomology)

noncomputable section

/-- A square-zero endomorphism together with an anticommuting parity involution. -/
structure OddDifferential (V : Type*) [AddCommGroup V] [Module ℂ V] where
  d : Module.End ℂ V
  parity : Module.End ℂ V
  square : d * d = 0
  parity_square : parity * parity = 1
  odd : d * parity = -(parity * d)

namespace OddDifferential

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : OddDifferential V)

abbrev cycles := LinearMap.ker c.d
abbrev boundaries := Boundaries c.d c.square
abbrev cohomology := Cohomology c.d c.square

local notation "Z" => c.cycles
local notation "B" => c.boundaries
local notation "HC" => c.cohomology
local notation "d" => c.d
local notation "σ" => c.parity
local notation "q" => c.boundaries.mkQ
local notation "d₀" => boundaryMap c.d c.square

theorem d_twice (x : V) : d (d x) = 0 :=
  DFunLike.congr_fun c.square x

theorem parity_twice (x : V) : σ (σ x) = x :=
  DFunLike.congr_fun c.parity_square x

theorem d_parity (x : V) : d (σ x) = -σ (d x) :=
  DFunLike.congr_fun c.odd x

/-- The parity involution restricted to the actual cycle subspace. -/
def cycleParity : Module.End ℂ Z :=
  (σ).restrict (fun x hx => by
    change d (σ x) = 0
    rw [c.d_parity, LinearMap.mem_ker.mp hx, map_zero, neg_zero])

@[simp] theorem cycleParity_val (a : Z) : (c.cycleParity a : V) = σ (a : V) := rfl

theorem cycleParity_square (a : Z) : c.cycleParity (c.cycleParity a) = a :=
  Subtype.ext (c.parity_twice (a : V))

private theorem cycleParity_mem_boundaries (a : Z) (ha : a ∈ B) :
    c.cycleParity a ∈ B := by
  change ∃ x : V, d₀ x = a at ha
  obtain ⟨x, rfl⟩ := ha
  refine ⟨-σ x, ?_⟩
  apply Subtype.ext
  change d (-σ x) = σ (d x)
  rw [map_neg, c.d_parity, neg_neg]

/-- The involution induced by parity on the actual cohomology quotient. -/
def cohomologyParity : Module.End ℂ HC :=
  (B).mapQ B c.cycleParity c.cycleParity_mem_boundaries

theorem cohomologyParity_mk (a : Z) :
    c.cohomologyParity (q a) = q (c.cycleParity a) := rfl

theorem cohomologyParity_involution (a : HC) :
    c.cohomologyParity (c.cohomologyParity a) = a := by
  obtain ⟨z, rfl⟩ := c.boundaries.mkQ_surjective a
  rw [c.cohomologyParity_mk, c.cohomologyParity_mk, c.cycleParity_square]

local notation "σZ" => c.cycleParity
local notation "σH" => c.cohomologyParity

private def boundaryParity : Module.End ℂ B :=
  (σZ).restrict c.cycleParity_mem_boundaries

private theorem boundaryParity_square (a : B) :
    c.boundaryParity (c.boundaryParity a) = a :=
  Subtype.ext (c.cycleParity_square (a : Z))

private abbrev boundaryToImage : V →ₗ[ℂ] B := (d₀).rangeRestrict

private theorem boundaryToImage_odd (x : V) :
    c.boundaryToImage (σ x) = -c.boundaryParity (c.boundaryToImage x) := by
  apply Subtype.ext
  apply Subtype.ext
  change d (σ x) = -σ (d x)
  exact c.d_parity x

private theorem rangeSection_exists :
    ∃ t : B →ₗ[ℂ] V, c.boundaryToImage.comp t = LinearMap.id :=
  c.boundaryToImage.exists_rightInverse_of_surjective (d₀).range_rangeRestrict

private def rangeSection : B →ₗ[ℂ] V := Classical.choose c.rangeSection_exists

private theorem rangeSection_charge (a : B) :
    d (c.rangeSection a) = ((a : Z) : V) :=
  congrArg (fun u : B => ((u : Z) : V))
    (LinearMap.congr_fun (Classical.choose_spec c.rangeSection_exists) a)

/-- Average the section of the actual boundary image into an odd section. -/
private def chiralT : B →ₗ[ℂ] V :=
  (2 : ℂ)⁻¹ • (c.rangeSection - (σ).comp (c.rangeSection.comp c.boundaryParity))

private theorem chiralT_charge (a : B) : d (c.chiralT a) = ((a : Z) : V) := by
  change d ((2 : ℂ)⁻¹ • (c.rangeSection a - σ (c.rangeSection (c.boundaryParity a)))) = _
  simp only [map_smul, map_sub, c.d_parity, c.rangeSection_charge]
  change (2 : ℂ)⁻¹ • (((a : Z) : V) - -σ (σ ((a : Z) : V))) = ((a : Z) : V)
  rw [c.parity_twice]
  module

private theorem chiralT_odd (a : B) : c.chiralT (c.boundaryParity a) = -σ (c.chiralT a) := by
  change (2 : ℂ)⁻¹ •
      (c.rangeSection (c.boundaryParity a) -
        σ (c.rangeSection (c.boundaryParity (c.boundaryParity a)))) =
    -σ ((2 : ℂ)⁻¹ • (c.rangeSection a - σ (c.rangeSection (c.boundaryParity a))))
  rw [c.boundaryParity_square, map_smul, map_sub, c.parity_twice]
  module

private def chiralR : V →ₗ[ℂ] Z :=
  (LinearMap.id - c.chiralT.comp c.boundaryToImage).codRestrict Z (fun x => by
    change d (x - c.chiralT (c.boundaryToImage x)) = 0
    rw [map_sub, c.chiralT_charge]
    exact sub_self (d x))

private theorem chiralR_cycle (a : Z) : c.chiralR (a : V) = a := by
  apply Subtype.ext
  change (a : V) - c.chiralT (c.boundaryToImage (a : V)) = (a : V)
  have hz : c.boundaryToImage (a : V) = 0 :=
    Subtype.ext (Subtype.ext (LinearMap.mem_ker.mp a.property))
  rw [hz, map_zero, sub_zero]

private theorem chiralR_even (x : V) : c.chiralR (σ x) = σZ (c.chiralR x) := by
  apply Subtype.ext
  change σ x - c.chiralT (c.boundaryToImage (σ x)) = σ (x - c.chiralT (c.boundaryToImage x))
  rw [c.boundaryToImage_odd, map_neg, c.chiralT_odd, neg_neg, map_sub]

private theorem cycleSection_exists : ∃ s : HC →ₗ[ℂ] Z, (q).comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective q
    (LinearMap.range_eq_top.mpr c.boundaries.mkQ_surjective)

private def cycleSection : HC →ₗ[ℂ] Z := Classical.choose c.cycleSection_exists

private theorem cycleSection_class (a : HC) : q (c.cycleSection a) = a :=
  LinearMap.congr_fun (Classical.choose_spec c.cycleSection_exists) a

/-- Average the section of the actual quotient into an even section. -/
private def chiralS : HC →ₗ[ℂ] Z :=
  (2 : ℂ)⁻¹ • (c.cycleSection + (σZ).comp (c.cycleSection.comp σH))

private theorem chiralS_class (a : HC) : q (c.chiralS a) = a := by
  change q ((2 : ℂ)⁻¹ • (c.cycleSection a + σZ (c.cycleSection (σH a)))) = a
  simp only [map_smul, map_add, ← c.cohomologyParity_mk, c.cycleSection_class,
    c.cohomologyParity_involution]
  module

private theorem chiralS_even (a : HC) : c.chiralS (σH a) = σZ (c.chiralS a) := by
  change (2 : ℂ)⁻¹ • (c.cycleSection (σH a) + σZ (c.cycleSection (σH (σH a)))) =
    σZ ((2 : ℂ)⁻¹ • (c.cycleSection a + σZ (c.cycleSection (σH a))))
  rw [c.cohomologyParity_involution, map_smul, map_add, c.cycleParity_square]
  module

private def chiralI : HC →ₗ[ℂ] V := c.cycles.subtype.comp c.chiralS
private def chiralP : V →ₗ[ℂ] HC := (q).comp c.chiralR
private def chiralE : Module.End ℂ V := c.chiralI.comp c.chiralP

private theorem chiralP_cycle (a : Z) : c.chiralP (a : V) = q a := by
  change q (c.chiralR (a : V)) = q a
  rw [c.chiralR_cycle]

private theorem chiralPI (a : HC) : c.chiralP (c.chiralI a) = a := by
  change c.chiralP (c.chiralS a : V) = a
  rw [c.chiralP_cycle, c.chiralS_class]

private theorem chiralQI (a : HC) : d (c.chiralI a) = 0 := (c.chiralS a).property

private theorem chiralPQ (x : V) : c.chiralP (d x) = 0 := by
  change c.chiralP ((d₀ x : Z) : V) = 0
  rw [c.chiralP_cycle]
  exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨x, rfl⟩

private theorem chiralI_even (a : HC) : c.chiralI (σH a) = σ (c.chiralI a) :=
  congrArg (fun u : Z => (u : V)) (c.chiralS_even a)

private theorem chiralP_even (x : V) : c.chiralP (σ x) = σH (c.chiralP x) := by
  change q (c.chiralR (σ x)) = σH (q (c.chiralR x))
  rw [c.chiralR_even, c.cohomologyParity_mk]

private theorem chiralQE (x : V) : d (c.chiralE x) = 0 := c.chiralQI (c.chiralP x)

private theorem chiralE_even (x : V) : c.chiralE (σ x) = σ (c.chiralE x) := by
  change c.chiralI (c.chiralP (σ x)) = σ (c.chiralI (c.chiralP x))
  rw [c.chiralP_even, c.chiralI_even]

private theorem chiralE_parity_twice (x : V) : σ (c.chiralE (σ x)) = c.chiralE x := by
  rw [c.chiralE_even, c.parity_twice]

private theorem chiralE_parity_charge (x : V) : c.chiralE (σ (d x)) = 0 := by
  rw [c.chiralE_even]
  change σ (c.chiralI (c.chiralP (d x))) = 0
  rw [c.chiralPQ, map_zero, map_zero]

private def cycleDifference : V →ₗ[ℂ] Z := c.chiralR - c.chiralS.comp c.chiralP

private theorem cycleDifference_class (x : V) : q (c.cycleDifference x) = 0 := by
  change q (c.chiralR x - c.chiralS (c.chiralP x)) = 0
  rw [map_sub, c.chiralS_class]
  exact sub_self (c.chiralP x)

private def differenceInBoundaries : V →ₗ[ℂ] B :=
  c.cycleDifference.codRestrict B (fun x =>
    (Submodule.Quotient.mk_eq_zero B).mp (c.cycleDifference_class x))

private theorem differenceInBoundaries_charge (x : V) :
    c.differenceInBoundaries (d x) = c.boundaryToImage x := by
  apply Subtype.ext
  change c.chiralR (d x) - c.chiralS (c.chiralP (d x)) = d₀ x
  have hr : c.chiralR (d x) = d₀ x := c.chiralR_cycle (d₀ x)
  rw [hr, c.chiralPQ, map_zero, sub_zero]

private theorem differenceInBoundaries_even (x : V) :
    c.differenceInBoundaries (σ x) = c.boundaryParity (c.differenceInBoundaries x) := by
  apply Subtype.ext
  change c.chiralR (σ x) - c.chiralS (c.chiralP (σ x)) =
    σZ (c.chiralR x - c.chiralS (c.chiralP x))
  rw [c.chiralR_even, c.chiralP_even, c.chiralS_even, map_sub]

private def chiralH : Module.End ℂ V := c.chiralT.comp c.differenceInBoundaries

private theorem chiralH_odd (x : V) : c.chiralH (σ x) = -σ (c.chiralH x) := by
  change c.chiralT (c.differenceInBoundaries (σ x)) = -σ (c.chiralT (c.differenceInBoundaries x))
  rw [c.differenceInBoundaries_even, c.chiralT_odd]

private theorem chiralHomotopy (x : V) :
    d (c.chiralH x) + c.chiralH (d x) = x - c.chiralE x := by
  have hd : d (c.chiralH x) = x - c.chiralT (c.boundaryToImage x) - c.chiralE x :=
    c.chiralT_charge (c.differenceInBoundaries x)
  have hh : c.chiralH (d x) = c.chiralT (c.boundaryToImage x) := by
    change c.chiralT (c.differenceInBoundaries (d x)) = _
    rw [c.differenceInBoundaries_charge]
  rw [hd, hh]
  abel

end OddDifferential

section Tensor

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (left : OddDifferential V) (right : OddDifferential W)

local notation "T" => V ⊗[ℂ] W
local notation "HT" => left.cohomology ⊗[ℂ] right.cohomology
local notation "dL" => left.d
local notation "dR" => right.d
local notation "σL" => left.parity
local notation "σR" => right.parity
local notation "qL" => left.boundaries.mkQ
local notation "qR" => right.boundaries.mkQ

/-- The algebraic tensor differential with the Koszul sign on the second summand. -/
def closedDifferential : Module.End ℂ T :=
  TensorProduct.map dL LinearMap.id + TensorProduct.map σL dR

local notation "K" => closedDifferential left right

theorem closedDifferential_tmul (x : V) (y : W) :
    K (x ⊗ₜ[ℂ] y) = dL x ⊗ₜ[ℂ] y + σL x ⊗ₜ[ℂ] dR y := by
  simp only [closedDifferential, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem closedDifferential_tmul_of_parity (x : V) (y : W) (p : ℕ)
    (hx : σL x = (-1 : ℂ) ^ p • x) :
    K (x ⊗ₜ[ℂ] y) = dL x ⊗ₜ[ℂ] y + (-1 : ℂ) ^ p • (x ⊗ₜ[ℂ] dR y) := by
  rw [closedDifferential_tmul, hx, ← TensorProduct.smul_tmul']

theorem closedDifferential_square : K * K = 0 := by
  apply TensorProduct.ext'
  intro x y
  change K (K (x ⊗ₜ[ℂ] y)) = 0
  simp only [closedDifferential_tmul, map_add, left.d_twice, right.d_twice,
    left.d_parity, left.parity_twice, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    TensorProduct.neg_tmul, zero_add, add_zero]
  abel

/-- The total parity on the tensor complex. -/
def closedParity : Module.End ℂ T := TensorProduct.map σL σR

theorem closedParity_square : closedParity left right * closedParity left right = 1 := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, Module.End.one_apply, closedParity, TensorProduct.map_tmul,
    left.parity_twice, right.parity_twice]

theorem closedDifferential_closedParity :
    K * closedParity left right = -(closedParity left right * K) := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.neg_apply, closedParity, TensorProduct.map_tmul,
    closedDifferential_tmul, map_add, left.d_parity, right.d_parity, left.parity_twice,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  abel

/-- The tensor complex carries the same cycle and quotient parity construction. -/
def closedComplex : OddDifferential T where
  d := K
  parity := closedParity left right
  square := closedDifferential_square left right
  parity_square := closedParity_square left right
  odd := closedDifferential_closedParity left right

abbrev closedCycles := LinearMap.ker K
abbrev closedBoundaries := Boundaries K (closedDifferential_square left right)
abbrev ClosedCohomology := Cohomology K (closedDifferential_square left right)

local notation "CC" => closedCycles left right
local notation "BC" => closedBoundaries left right
local notation "CH" => ClosedCohomology left right
local notation "qc" => Submodule.mkQ (closedBoundaries left right)

private def tensorI : HT →ₗ[ℂ] T := TensorProduct.map left.chiralI right.chiralI
private def tensorP : T →ₗ[ℂ] HT := TensorProduct.map left.chiralP right.chiralP

local notation "I" => tensorI left right
local notation "P" => tensorP left right

private theorem tensorQI (a : HT) : K (I a) = 0 := by
  have h : (K).comp I = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, tensorI, TensorProduct.map_tmul, closedDifferential_tmul,
      left.chiralQI, right.chiralQI, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      add_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h a

private theorem tensorPQ (z : T) : P (K z) = 0 := by
  have h : (P).comp K = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, closedDifferential_tmul, map_add, tensorP,
      TensorProduct.map_tmul, left.chiralPQ, right.chiralPQ, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h z

private theorem tensorPI (a : HT) : P (I a) = a := by
  have h : (P).comp I = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, tensorI, tensorP, TensorProduct.map_tmul,
      left.chiralPI, right.chiralPI, LinearMap.id_apply]
  exact LinearMap.congr_fun h a

private def closedHomotopy : Module.End ℂ T :=
  TensorProduct.map left.chiralH LinearMap.id +
    TensorProduct.map (left.chiralE.comp σL) right.chiralH

local notation "hT" => closedHomotopy left right

private theorem closedHomotopy_tmul (x : V) (y : W) :
    hT (x ⊗ₜ[ℂ] y) =
      left.chiralH x ⊗ₜ[ℂ] y + left.chiralE (σL x) ⊗ₜ[ℂ] right.chiralH y := by
  simp only [closedHomotopy, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.comp_apply]

private theorem closedHomotopy_map :
    (K).comp hT + (hT).comp K = LinearMap.id - (I).comp P := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    closedHomotopy_tmul, closedDifferential_tmul, map_add, left.chiralQE,
    left.chiralE_parity_twice, left.chiralE_parity_charge, left.chiralH_odd, left.parity_twice,
    TensorProduct.zero_tmul, TensorProduct.neg_tmul, zero_add, add_zero,
    tensorI, tensorP, TensorProduct.map_tmul]
  calc
    _ = (dL (left.chiralH x) + left.chiralH (dL x)) ⊗ₜ[ℂ] y +
        left.chiralE x ⊗ₜ[ℂ] (dR (right.chiralH y) + right.chiralH (dR y)) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
    _ = (x - left.chiralE x) ⊗ₜ[ℂ] y +
        left.chiralE x ⊗ₜ[ℂ] (y - right.chiralE y) := by
      rw [left.chiralHomotopy, right.chiralHomotopy]
    _ = _ := by
      change (x - left.chiralE x) ⊗ₜ[ℂ] y + left.chiralE x ⊗ₜ[ℂ] (y - right.chiralE y) =
        x ⊗ₜ[ℂ] y - left.chiralE x ⊗ₜ[ℂ] right.chiralE y
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel

private theorem closedHomotopy_identity (z : T) :
    K (hT z) + hT (K z) = z - I (P z) :=
  LinearMap.congr_fun (closedHomotopy_map left right) z

private def tensorICycle : HT →ₗ[ℂ] CC :=
  (I).codRestrict CC (tensorQI left right)

local notation "IC" => tensorICycle left right

/-- The cross product of classes in the actual cohomology quotients. -/
def crossProduct : HT →ₗ[ℂ] CH := (qc).comp IC

local notation "X" => crossProduct left right

private def descendP : CH →ₗ[ℂ] HT :=
  (BC).liftQ ((P).comp (CC).subtype) (by
    intro z hz
    change ∃ w : T, boundaryMap K (closedDifferential_square left right) w = z at hz
    obtain ⟨w, rfl⟩ := hz
    exact tensorPQ left right w)

local notation "Y" => descendP left right

private theorem descendP_class (z : CC) : Y (qc z) = P (z : T) := rfl

private theorem descendP_cross (a : HT) : Y (X a) = a := by
  change Y (qc (IC a)) = a
  rw [descendP_class]
  exact tensorPI left right a

private theorem cross_descendP_class (z : CC) : X (P (z : T)) = qc z := by
  change qc (IC (P (z : T))) = qc z
  symm
  apply (Submodule.Quotient.eq BC).mpr
  refine ⟨hT (z : T), ?_⟩
  apply Subtype.ext
  change K (hT (z : T)) = (z : T) - I (P (z : T))
  simpa only [show K (z : T) = 0 from z.property, map_zero, add_zero] using
    closedHomotopy_identity left right (z : T)

private theorem cross_descendP (a : CH) : X (Y a) = a := by
  obtain ⟨z, rfl⟩ := (BC).mkQ_surjective a
  rw [descendP_class]
  exact cross_descendP_class left right z

/-- The canonical algebraic Künneth equivalence over ℂ. -/
def kunnethEquiv : HT ≃ₗ[ℂ] CH :=
  { X with
    invFun := Y
    left_inv := descendP_cross left right
    right_inv := cross_descendP left right }

/-- The tensor of two arbitrary cycles is an actual closed cycle. -/
def cycleTensor (x : left.cycles) (y : right.cycles) : CC :=
  ⟨(x : V) ⊗ₜ[ℂ] (y : W), by
    change K ((x : V) ⊗ₜ[ℂ] (y : W)) = 0
    rw [closedDifferential_tmul, show dL (x : V) = 0 from x.property,
      show dR (y : W) = 0 from y.property]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]⟩

theorem crossProduct_classOf_tmul (x : left.cycles) (y : right.cycles) :
    X (qL x ⊗ₜ[ℂ] qR y) = qc (cycleTensor left right x y) := by
  have h : P (cycleTensor left right x y : T) = qL x ⊗ₜ[ℂ] qR y := by
    change left.chiralP (x : V) ⊗ₜ[ℂ] right.chiralP (y : W) = _
    simp only [left.chiralP_cycle, right.chiralP_cycle]
  rw [← h]
  exact cross_descendP_class left right (cycleTensor left right x y)

theorem kunnethEquiv_classOf_tmul (x : left.cycles) (y : right.cycles) :
    kunnethEquiv left right (qL x ⊗ₜ[ℂ] qR y) = qc (cycleTensor left right x y) :=
  crossProduct_classOf_tmul left right x y

theorem kunnethEquiv_symm_classOf_cycleTensor (x : left.cycles) (y : right.cycles) :
    (kunnethEquiv left right).symm (qc (cycleTensor left right x y)) = qL x ⊗ₜ[ℂ] qR y := by
  rw [← kunnethEquiv_classOf_tmul, LinearEquiv.symm_apply_apply]

/-- The pure-cycle value determines the map, independently of the chosen sections. -/
theorem crossProduct_unique (f : HT →ₗ[ℂ] CH)
    (hf : ∀ x y, f (qL x ⊗ₜ[ℂ] qR y) = qc (cycleTensor left right x y)) : f = X := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨a, rfl⟩ := left.boundaries.mkQ_surjective x
  obtain ⟨b, rfl⟩ := right.boundaries.mkQ_surjective y
  rw [hf, crossProduct_classOf_tmul]

end Tensor

section SelfTensor

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (d σ : Module.End ℂ V)
  (square : d * d = 0) (paritySquare : σ * σ = 1) (odd : d * σ = -(σ * d))

local notation "C" => (OddDifferential.mk d σ square paritySquare odd)
local notation "K" => closedDifferential C C

/-- The self-tensor endpoint with exactly the square, involution and oddness hypotheses. -/
def selfKunnethEquiv :
    (Cohomology d square ⊗[ℂ] Cohomology d square) ≃ₗ[ℂ]
      Cohomology K (closedDifferential_square C C) :=
  kunnethEquiv C C

theorem selfKunnethEquiv_classOf_tmul (x y : LinearMap.ker d) :
    selfKunnethEquiv d σ square paritySquare odd
      ((Boundaries d square).mkQ x ⊗ₜ[ℂ] (Boundaries d square).mkQ y) =
      (Boundaries K (closedDifferential_square C C)).mkQ (cycleTensor C C x y) :=
  kunnethEquiv_classOf_tmul C C x y

end SelfTensor

end
end D5.S3.HomologicalAlgebra.ParityOddKunneth

#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.OddDifferential.cycleParity
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.OddDifferential.cohomologyParity
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.OddDifferential.cohomologyParity_involution
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.closedDifferential_square
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.closedComplex
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.kunnethEquiv
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.kunnethEquiv_classOf_tmul
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.kunnethEquiv_symm_classOf_cycleTensor
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.crossProduct_unique
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.selfKunnethEquiv
#print axioms D5.S3.HomologicalAlgebra.ParityOddKunneth.selfKunnethEquiv_classOf_tmul
