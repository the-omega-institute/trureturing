/- GID: D5/S3/Combinatorics/Matroids/RationalJointCircuitImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/RationalJointCircuitImage
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Rational cycle representatives of saturated joint circuit readouts. -/

module

public import D5.S3.Combinatorics.Matroids.JointCircuitLiftingObstruction
public import D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Rational representatives for simultaneous circuit restriction -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped nonZeroDivisors
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.RationalJointCircuitImage

open CircuitCycleDecomposition (topCycles)
open IntegralCircuitImage (aggregateRestrict)
open CircuitPairInnerProduct (rationalTopCycles rationalAggregate castChain
  mem_rationalTopCycles_iff exists_integral_multiple rationalAggregate_cast rationalAggregate_mem
  aggregateRestriction)
open JointCircuitGramCertificate (Circuit)
open DirectSumCircuitTorsion (JointTarget jointRestriction jointRestriction_apply
  jointRestriction_injective)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Rational coefficients modulo integral coefficients. -/
abbrev RationalResidue := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- Take a rational coefficient modulo the integers. -/
def rationalResidue : ℚ →+ RationalResidue :=
  QuotientAddGroup.mk' _

/-- The residue vanishes exactly on the embedded integers. -/
lemma rationalResidue_eq_zero {q : ℚ} :
    rationalResidue q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [rationalResidue, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  simp only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one]

/-- Rational top cycles whose simultaneous restriction has integral coefficients. -/
def rationalIntegralReadoutCycles (M : Matroid V) : Submodule ℤ (Finset V → ℚ) where
  carrier := {z | z ∈ rationalTopCycles M ∧ ∀ C : Circuit M, ∀ F : Finset V,
    rationalResidue (rationalAggregate M C.val z F) = 0}
  zero_mem' := ⟨(rationalTopCycles M).zero_mem, by simp⟩
  add_mem' ha hb := ⟨(rationalTopCycles M).add_mem ha.1 hb.1, by
    intro C F
    simp only [map_add, Pi.add_apply, ha.2 C F, hb.2 C F, add_zero]⟩
  smul_mem' d z hz := ⟨(rationalTopCycles M).restrictScalars ℤ |>.smul_mem d hz.1, by
    intro C F
    simp only [map_zsmul, Pi.smul_apply, hz.2 C F, zsmul_zero]⟩

private noncomputable def integerReadout {M : Matroid V}
    (z : rationalIntegralReadoutCycles M) (C : Circuit M) :
    topCycles (M ／ (C.val : Set V)) := by
  let chain : Finset V → ℤ := fun F => (rationalResidue_eq_zero.mp (z.prop.2 C F)).choose
  have hc : castChain chain = rationalAggregate M C.val z.val :=
    funext fun F => (rationalResidue_eq_zero.mp (z.prop.2 C F)).choose_spec
  exact ⟨chain, mem_rationalTopCycles_iff.mp
    (hc.symm ▸ rationalAggregate_mem C.prop ⟨z.val, z.prop.1⟩)⟩

private lemma integerReadout_cast {M : Matroid V} (z : rationalIntegralReadoutCycles M)
    (C : Circuit M) (F : Finset V) :
    ((integerReadout z C).val F : ℚ) = rationalAggregate M C.val z.val F :=
  (rationalResidue_eq_zero.mp (z.prop.2 C F)).choose_spec

private noncomputable def integerReadouts (M : Matroid V) :
    rationalIntegralReadoutCycles M →ₗ[ℤ] JointTarget M where
  toFun z C := integerReadout z C
  map_add' z w := by
    funext C
    apply Subtype.ext
    funext F
    apply Int.cast_injective (α := ℚ)
    change ((integerReadout (z + w) C).val F : ℚ) =
      (((integerReadout z C).val F + (integerReadout w C).val F : ℤ) : ℚ)
    simp only [Int.cast_add, integerReadout_cast, Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' d z := by
    funext C
    apply Subtype.ext
    funext F
    apply Int.cast_injective (α := ℚ)
    change ((integerReadout (d • z) C).val F : ℚ) =
      (((d * (integerReadout z C).val F) : ℤ) : ℚ)
    rw [Int.cast_mul, integerReadout_cast, Submodule.coe_smul, map_zsmul]
    simp only [integerReadout_cast, Pi.smul_apply, zsmul_eq_mul]

/-- Include integral cycles among rational cycles with integral readouts. -/
def integralCycleInRational (M : Matroid V) :
    topCycles M →ₗ[ℤ] rationalIntegralReadoutCycles M where
  toFun z := ⟨castChain z.val, mem_rationalTopCycles_iff.mpr z.prop, by
    intro C F
    rw [rationalAggregate_cast]
    exact rationalResidue_eq_zero.mpr ⟨aggregateRestriction M C.val z.val F, rfl⟩⟩
  map_add' z w := by
    apply Subtype.ext
    funext F
    exact Int.cast_add (z.val F) (w.val F)
  map_smul' d z := by
    refine Subtype.ext (funext fun F => ?_)
    change (((d • z).val F : ℤ) : ℚ) = (d • castChain z.val) F
    simp only [castChain, Submodule.coe_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
    norm_cast

private lemma rationalAggregate_cast_joint (M : Matroid V) (z : topCycles M)
    (C : Circuit M) (F : Finset V) :
    rationalAggregate M C.val (castChain z.val) F = ((jointRestriction M z C).val F : ℚ) := by
  rw [rationalAggregate_cast]
  rw [jointRestriction_apply]
  simp only [castChain, aggregateRestriction, aggregateRestrict, Finset.sum_apply]

private lemma integerReadouts_integral (M : Matroid V) (z : topCycles M) :
    integerReadouts M (integralCycleInRational M z) = jointRestriction M z := by
  funext C
  apply Subtype.ext
  funext F
  apply Int.cast_injective (α := ℚ)
  change ((integerReadout (integralCycleInRational M z) C).val F : ℚ) = _
  rw [integerReadout_cast]
  exact rationalAggregate_cast_joint M z C F

private lemma exists_integral_scalar {M : Matroid V} (z : rationalIntegralReadoutCycles M) :
    ∃ (d : ℤ) (w : topCycles M), d ≠ 0 ∧ d • z = integralCycleInRational M w := by
  obtain ⟨q, x, hq, hx⟩ := exists_integral_multiple
    (⟨z.val, z.prop.1⟩ : rationalTopCycles M)
  refine ⟨q.num, q.den • x, Rat.num_ne_zero.mpr hq, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hnum : (q.den : ℚ) * q = q.num := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
        congrArg ((q.den : ℚ) * ·) q.num_div_den.symm
      _ = _ := mul_div_cancel₀ _ hden
  apply Subtype.ext
  funext F
  have hf : (x.val F : ℚ) = q * z.val F := congrFun hx F
  change (q.num • z.val) F = castChain (q.den • x.val) F
  rw [Pi.smul_apply, castChain, Pi.smul_apply, zsmul_eq_mul, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, hf, ← mul_assoc, hnum]

private lemma exists_scaled_image_iff (M : Matroid V) (y : JointTarget M) :
    y ∈ JointSaturatedImage M ↔
      ∃ (d : ℤ) (x : topCycles M), d ≠ 0 ∧ jointRestriction M x = d • y := by
  change ((jointRestriction M).range.mkQ y) ∈ Submodule.torsion ℤ _ ↔ _
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨d, hd⟩
    have hz : (jointRestriction M).range.mkQ ((d : ℤ) • y) = 0 := by
      rw [map_smul]
      exact hd
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨d, x, mem_nonZeroDivisors_iff_ne_zero.mp d.prop, hx⟩
  · rintro ⟨d, x, hd, hx⟩
    refine ⟨⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩, ?_⟩
    change d • (jointRestriction M).range.mkQ y = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hx⟩

private lemma integerReadouts_mem {M : Matroid V} (z : rationalIntegralReadoutCycles M) :
    integerReadouts M z ∈ JointSaturatedImage M := by
  obtain ⟨d, x, hd, hx⟩ := exists_integral_scalar z
  have h := congrArg (integerReadouts M) hx
  rw [map_smul, integerReadouts_integral] at h
  exact (exists_scaled_image_iff M _).mpr ⟨d, x, hd, h.symm⟩

private lemma integerReadouts_injective {M : Matroid V} {e : V} (he : e ∈ M.E) :
    Function.Injective (integerReadouts M) := by
  apply (injective_iff_map_eq_zero (integerReadouts M)).mpr
  intro z hz
  obtain ⟨d, x, hd, hx⟩ := exists_integral_scalar z
  have h := congrArg (integerReadouts M) hx
  rw [map_smul, hz, smul_zero, integerReadouts_integral] at h
  have hx0 : x = 0 := (jointRestriction_injective he) (h.symm.trans (map_zero _).symm)
  rw [hx0, map_zero] at hx
  exact (smul_eq_zero.mp hx).resolve_left hd

private lemma integerReadouts_exists {M : Matroid V} (y : JointSaturatedImage M) :
    ∃ z : rationalIntegralReadoutCycles M, integerReadouts M z = y.val := by
  obtain ⟨d, x, hd, hxy⟩ := (exists_scaled_image_iff M _).mp y.prop
  let source := (d : ℚ)⁻¹ • castChain x.val
  have hnonzero : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hsource : source ∈ rationalTopCycles M :=
    (rationalTopCycles M).smul_mem _ (mem_rationalTopCycles_iff.mpr x.prop)
  have hread (C : Circuit M) (F : Finset V) :
      rationalAggregate M C.val source F = (y.val C).val F := by
    have hcoord : (jointRestriction M x C).val F = d * (y.val C).val F := by
      have h := congrArg (fun t : JointTarget M => (t C).val F) hxy
      simp only [Pi.smul_apply, Submodule.coe_smul, zsmul_eq_mul] at h
      norm_cast at h
    dsimp only [source]
    rw [map_smul, Pi.smul_apply, rationalAggregate_cast_joint, hcoord, Int.cast_mul,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hnonzero, one_mul]
  let cycle : rationalIntegralReadoutCycles M := ⟨source, hsource, fun C F =>
    rationalResidue_eq_zero.mpr ⟨(y.val C).val F, (hread C F).symm⟩⟩
  refine ⟨cycle, ?_⟩
  funext C
  apply Subtype.ext
  funext F
  apply Int.cast_injective (α := ℚ)
  change ((integerReadout cycle C).val F : ℚ) = _
  rw [integerReadout_cast]
  exact hread C F

/-- Rational cycles with integral readouts identify with the saturation of the integral
joint image. The comparison intertwines integral cycles and the original restriction. -/
theorem rationalJointRestriction_equiv (M : Matroid V) {e : V} (he : e ∈ M.E) :
    ∃ comparison : rationalIntegralReadoutCycles M ≃ₗ[ℤ] JointSaturatedImage M,
      (∀ z C F, (((comparison z).val C).val F : ℚ) =
        rationalAggregate M C.val z.val F) ∧
      (∀ x, (comparison (integralCycleInRational M x)).val = jointRestriction M x) ∧
      Nonempty ((rationalIntegralReadoutCycles M ⧸ (integralCycleInRational M).range) ≃ₗ[ℤ]
        (JointSaturatedImage M ⧸ JointImageInSaturation M)) := by
  let signedMap := (integerReadouts M).codRestrict _ integerReadouts_mem
  have hinjective : Function.Injective signedMap :=
    fun _ _ h => integerReadouts_injective he (congrArg Subtype.val h)
  have hsurjective : Function.Surjective signedMap := by
    intro y
    obtain ⟨z, hz⟩ := integerReadouts_exists y
    exact ⟨z, Subtype.ext hz⟩
  let comparison := LinearEquiv.ofBijective signedMap ⟨hinjective, hsurjective⟩
  have hcompare (x : topCycles M) : (comparison (integralCycleInRational M x)).val =
      jointRestriction M x := integerReadouts_integral M x
  refine ⟨comparison, ?_, hcompare, ?_⟩
  · intro z C F
    exact integerReadout_cast z C F
  · refine ⟨Submodule.Quotient.equiv _ _ comparison ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (hcompare x).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨integralCycleInRational M x, ⟨x, rfl⟩, Subtype.ext ((hcompare x).trans hx)⟩

end D5.S3.Combinatorics.Matroids.RationalJointCircuitImage
