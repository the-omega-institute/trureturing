/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed C₂ quotient acts on the actual negative twisted relative quotient. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

/-! The negative twisted relative quotient carries the actual fixed-source product action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2

open FixedSourceIsing (odd_commutator odd_iterate)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open Lattice.ActualFixedC2 (FixedC2Quotient fixedC2 fixedQuotientProduct
  fixed_quotient_product_mk)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeInvolution (FixedCarrier fixedMode fixedSpace fixedTranslation)
open OriginalOrbifoldField (fixedParitySlice_borcherds)
open OriginalOrbifoldTranslation (vm_translation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open scoped VertexOperator BigOperators

variable (D : LatticeData) (hu : IsUnit D.G.det)

private local instance : AddCommGroup (FixedCarrier D) := (fixedSpace D).addCommGroup

private local instance : AddCommGroup (paritySpace D hu (-1)) :=
  (paritySpace D hu (-1)).addCommGroup

local notation "Odd" => paritySpace D hu (-1)
local notation "C₂" => relativeOddC2 D hu
local notation "OddQ" => (Odd ⧸ C₂)
local notation "ρ" => fun u n => (fixedParitySlice D hu (-1) u)[[n]]

private theorem higher_mode_mem (r : ℕ) (a : FixedCarrier D) (t : Odd) :
    ρ a (-((r : ℤ) + 2)) t ∈ C₂ := by
  induction r generalizing a with
  | zero => exact Submodule.subset_span ⟨a, t, rfl⟩
  | succ r ih =>
    let n : ℤ := -((r : ℤ) + 2)
    have h : ρ (fixedTranslation D a) n t ∈ C₂ := ih (fixedTranslation D a)
    rw [vm_translation] at h
    have hn : -(n : ℂ) ≠ 0 :=
      neg_ne_zero.mpr (Int.cast_ne_zero.mpr (show n ≠ 0 by dsimp [n]; omega))
    have hnext := (C₂).smul_mem (-(n : ℂ))⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul,
      show n - 1 = -(((r + 1 : ℕ) : ℤ) + 2) by dsimp [n]; omega] using hnext

/-- Every fixed-source mode of index at most `-2` lands in the relative C₂ subspace. -/
theorem fixed_odd_mode_mem_relativeOddC2 (a : FixedCarrier D) (t : Odd)
    {n : ℤ} (hn : n ≤ -2) : ρ a n t ∈ C₂ := by
  have h := higher_mode_mem D hu (-n - 2).toNat a t
  rwa [Int.toNat_of_nonneg (show 0 ≤ -n - 2 by omega),
    show -(-n - 2 + 2) = n by omega] at h

set_option maxHeartbeats 600000 in
-- The finite commutator is elaborated through the actual parity-restricted linear maps.
private theorem minus_one_generator_mem (u v : FixedCarrier D) (t : Odd) :
    ρ u (-1) (ρ v (-2) t) ∈ C₂ := by
  let term (i : ℕ) := integerBinomial (-1) i • ρ (fixedMode D u i v) (-3 - i) t
  have finite : Function.HasFiniteSupport term := by
    simpa only [term, zero_add, show (-1 : ℤ) + -2 = -3 by decide]
      using (fixedParitySlice_borcherds D hu u v t (-1) (-2) 0).1
  have correction : (∑ᶠ i, term i) ∈ C₂ := by
    rw [finsum_eq_sum _ finite]
    exact (C₂).sum_mem fun i _ => (C₂).smul_mem _
      (fixed_odd_mode_mem_relativeOddC2 D hu _ _ (by omega))
  have comm : ρ u (-1) (ρ v (-2) t) - ρ v (-2) (ρ u (-1) t) = ∑ᶠ i, term i := by
    simpa only [term, show (-1 : ℤ) + -2 = -3 by decide] using
      (odd_commutator u v t (-1) (-2))
  rw [← comm] at correction
  simpa only [sub_add_cancel] using (C₂).add_mem correction
    (fixed_odd_mode_mem_relativeOddC2 D hu v (ρ u (-1) t) le_rfl)

private theorem iterate_class (u v : FixedCarrier D) (t : Odd) {r : ℤ} (hr : r ≤ -1) :
    (C₂).mkQ (ρ (fixedMode D u r v) (-1) t) = (C₂).mkQ (ρ u r (ρ v (-1) t)) := by
  let weight (i : ℕ) := (-1 : ℂ)^i * integerBinomial r i
  let first (i : ℕ) := weight i • ρ u (r - i) (ρ v (-1 + i) t)
  let second (i : ℕ) := weight i • (epsilon r • ρ v (-1 + r - i) (ρ u i t))
  have h := fixedParitySlice_borcherds D hu u v t 0 (-1) r
  have hfirst : Function.HasFiniteSupport first := by
    simpa only [first, weight, zero_add] using h.2.1
  have hsecond : Function.HasFiniteSupport second := by
    simpa only [second, weight, zero_add] using h.2.2.1
  have it := odd_iterate u v t r (-1)
  change ρ (fixedMode D u r v) (-1) t =
    ∑ᶠ i, weight i • (ρ u (r - i) (ρ v (-1 + i) t) -
      epsilon r • ρ v (-1 + r - i) (ρ u i t)) at it
  simp_rw [smul_sub] at it
  change ρ (fixedMode D u r v) (-1) t = ∑ᶠ i, (first i - second i) at it
  rw [it, finsum_sub_distrib hfirst hsecond, map_sub, map_finsum _ hfirst,
    map_finsum _ hsecond]
  have second_zero (i : ℕ) : (C₂).mkQ (second i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero C₂).mpr
    exact (C₂).smul_mem _ ((C₂).smul_mem _
      (fixed_odd_mode_mem_relativeOddC2 D hu _ _ (by omega)))
  rw [finsum_eq_zero_of_forall_eq_zero second_zero, sub_zero, finsum_eq_single _ 0]
  · simp only [first, weight, pow_zero, integerBinomial, Ring.choose_zero_right,
      Int.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, add_zero]
  · intro i hi
    apply (Submodule.Quotient.mk_eq_zero C₂).mpr
    exact (C₂).smul_mem _ (fixed_odd_mode_mem_relativeOddC2 D hu _ _ (by omega))

private def minusOneToQuotient : FixedCarrier D →ₗ[ℂ] Odd →ₗ[ℂ] OddQ :=
  LinearMap.mk₂ ℂ (fun u t => (C₂).mkQ (ρ u (-1) t))
    (fun u v t => by
      rw [← map_add]
      congr 1
      apply Subtype.ext
      change (correctedField D hu (u.val + v.val)).coeff 0 t.val =
        (correctedField D hu u.val).coeff 0 t.val + (correctedField D hu v.val).coeff 0 t.val
      simp only [map_add, Pi.add_apply, LinearMap.add_apply])
    (fun c u t => by
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      change (correctedField D hu (c • u.val)).coeff 0 t.val =
        c • (correctedField D hu u.val).coeff 0 t.val
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply])
    (fun u t s => ((C₂).mkQ.comp (ρ u (-1))).map_add t s)
    (fun c u t => ((C₂).mkQ.comp (ρ u (-1))).map_smul c t)

private theorem fixedC2_le_ker : fixedC2 D ≤ (minusOneToQuotient D hu).ker := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, v, rfl⟩
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro t
  change (C₂).mkQ (ρ (fixedMode D u (-2) v) (-1) t) = 0
  rw [iterate_class D hu u v t (by decide : (-2 : ℤ) ≤ -1)]
  exact (Submodule.Quotient.mk_eq_zero C₂).mpr
    (fixed_odd_mode_mem_relativeOddC2 D hu u (ρ v (-1) t) le_rfl)

private theorem relativeOddC2_le_ker : C₂ ≤ (minusOneToQuotient D hu).flip.ker := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, t, rfl⟩
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro u
  change (C₂).mkQ (ρ u (-1) (relativeOddMinusTwo D hu v t)) = 0
  exact (Submodule.Quotient.mk_eq_zero C₂).mpr (minus_one_generator_mem D hu u v t)

/-- The actual `(-1)`-action descended through both C₂ subspaces. -/
def relativeOddQuotientAction : FixedC2Quotient D →ₗ[ℂ] Module.End ℂ OddQ :=
  (minusOneToQuotient D hu).liftQ₂ (fixedC2 D) C₂ (fixedC2_le_ker D hu)
    (relativeOddC2_le_ker D hu)

@[simp]
theorem relativeOddQuotientAction_mk (u : FixedCarrier D) (t : Odd) :
    relativeOddQuotientAction D hu ((fixedC2 D).mkQ u) ((C₂).mkQ t) =
      (C₂).mkQ (ρ u (-1) t) := rfl

/-- The fixed `(-1)` product acts by composition on the negative relative quotient. -/
theorem relativeOddQuotientAction_product (x y : FixedC2Quotient D) (t : OddQ) :
    relativeOddQuotientAction D hu (fixedQuotientProduct D x y) t =
      relativeOddQuotientAction D hu x (relativeOddQuotientAction D hu y t) := by
  obtain ⟨u, rfl⟩ := (fixedC2 D).mkQ_surjective x
  obtain ⟨v, rfl⟩ := (fixedC2 D).mkQ_surjective y
  obtain ⟨w, rfl⟩ := (C₂).mkQ_surjective t
  simp only [fixed_quotient_product_mk, relativeOddQuotientAction_mk]
  exact iterate_class D hu u v w (by decide : (-1 : ℤ) ≤ -1)

#print axioms fixed_odd_mode_mem_relativeOddC2
#print axioms relativeOddQuotientAction
#print axioms relativeOddQuotientAction_mk
#print axioms relativeOddQuotientAction_product

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
