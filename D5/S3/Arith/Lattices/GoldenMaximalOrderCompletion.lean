/- GID: D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/GoldenMaximalOrderCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Hodge lattice has a minimal full-rank golden-stable saturation of index two. -/

import D5.S0.Carrier.Ring
import D5.S3.Arith.Lattices.ExactDualLatticeFormula
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index

/- Library-search audit trail (2026-08-28):
   * Current-tree body-shape searches found the source's integral Hodge matrix and lattice only in
     `ExactDualLatticeFormula`; those canonical primitives are imported below.
   * No D5 declaration constructs `(I + J) / 2`, its saturation, or either index-two bridge.
   * Pinned Mathlib supplies generic span, quotient, and subgroup-index infrastructure, including
     `Submodule.mem_span_range_iff_exists_fun`, `AddSubgroup.relIndex_ker`, and
     `AddSubgroup.index_ker`; the concrete parity calculation is proved locally.
-/

namespace D5.S3.Arith.Lattices.GoldenMaximalOrderCompletion

open D5.S0.Carrier
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open Module Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The source operator `Phi = (I + J) / 2` in the chosen `Lambda^2 A4` basis. -/
def goldenOperatorMatrix : Matrix LatticeIndex LatticeIndex Real :=
  (1 / 2 : Real) • (1 + hodgeMatrix)

/-- The integer-linear endomorphism of the ambient real space induced by `Phi`. -/
def goldenOperator : AmbientSpace →ₗ[Int] AmbientSpace :=
  (Matrix.mulVecLin goldenOperatorMatrix).restrictScalars Int

/-- The source saturation `W_Z + Phi W_Z`. -/
def maximalLattice : Submodule Int AmbientSpace :=
  lattice ⊔ lattice.map goldenOperator

/-- The nonintegral parity generator forced by `I + J` modulo two. -/
def halfVector : AmbientSpace := fun _ => 1 / 2

/-- The source inclusion `Z[sqrt 5] -> Z[phi]`, in exact integral coordinates. -/
def sqrtFiveOrderEmbedding : Zsqrtd 5 →+* GoldenInt where
  toFun x := ⟨x.re - x.im, 2 * x.im⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

/-- Reduction of the golden coefficient modulo two. Its kernel is `Z[sqrt 5]`. -/
def goldenParity : GoldenInt →+ ZMod 2 where
  toFun x := x.b
  map_zero' := by simp
  map_add' x y := by simp

private lemma golden_operator_sq_apply (x : AmbientSpace) :
    goldenOperator (goldenOperator x) = goldenOperator x + x := by
  ext i
  fin_cases i <;>
    simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private lemma golden_operator_basis_sub_half_mem (j : LatticeIndex) :
    goldenOperator (chosenBasis j) - halfVector ∈ lattice := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  fin_cases j
  · refine ⟨![0, -1, 0, -1, 0, -2], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring
  · refine ⟨![0, 0, -1, -1, 1, -1], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring
  · refine ⟨![-1, 0, 0, -2, 0, -1], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring
  · refine ⟨![0, 0, -2, 0, 0, 0], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring
  · refine ⟨![-1, 1, -1, -1, 0, 0], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring
  · refine ⟨![-2, 0, 0, -1, -1, 0], ?_⟩
    ext i
    fin_cases i <;>
      simp [goldenOperator, goldenOperatorMatrix, hodgeMatrix, integralHodgeMatrix,
        halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply]
    all_goals ring

private lemma golden_operator_lattice_le_parity :
    lattice.map goldenOperator ≤ lattice ⊔ Int ∙ halfVector := by
  rw [Submodule.map_le_iff_le_comap, lattice, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change goldenOperator (chosenBasis j) ∈ lattice ⊔ Int ∙ halfVector
  have hdifference : goldenOperator (chosenBasis j) - halfVector ∈ lattice :=
    golden_operator_basis_sub_half_mem j
  have hhalf : halfVector ∈ Int ∙ halfVector := Submodule.mem_span_singleton_self halfVector
  convert Submodule.add_mem _ (Submodule.mem_sup_left hdifference)
    (Submodule.mem_sup_right hhalf) using 1
  abel

private lemma half_vector_mem_maximal : halfVector ∈ maximalLattice := by
  have hbasis : chosenBasis (0 : LatticeIndex) ∈ lattice := by
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hphi : goldenOperator (chosenBasis (0 : LatticeIndex)) ∈ maximalLattice := by
    exact Submodule.mem_sup_right ⟨chosenBasis 0, hbasis, rfl⟩
  have hdifference : goldenOperator (chosenBasis (0 : LatticeIndex)) - halfVector ∈
      maximalLattice :=
    Submodule.mem_sup_left (golden_operator_basis_sub_half_mem 0)
  convert Submodule.sub_mem _ hphi hdifference using 1
  abel

private lemma maximal_lattice_eq_parity :
    maximalLattice = lattice ⊔ Int ∙ halfVector := by
  apply le_antisymm
  · exact sup_le le_sup_left golden_operator_lattice_le_parity
  · exact sup_le le_sup_left (Submodule.span_le.mpr fun _ h => by
      simpa only [Set.mem_singleton_iff] using h ▸ half_vector_mem_maximal)

private lemma half_vector_not_mem_lattice : halfVector ∉ lattice := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  rintro ⟨coeff, hcoeff⟩
  have hzero := congrFun hcoeff (0 : LatticeIndex)
  norm_num [halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply,
    Finsupp.single_apply, Fin.sum_univ_succ] at hzero
  have hreal : (((2 * coeff 0 : Int) : Real)) = 1 := by
    push_cast
    linarith
  have hint : 2 * coeff 0 = 1 := by
    exact_mod_cast hreal
  omega

private lemma twice_half_vector_mem_lattice : (2 : Int) • halfVector ∈ lattice := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun _ => 1, ?_⟩
  ext i
  fin_cases i <;>
    norm_num [halfVector, chosenBasis, Pi.basisFun_apply, Pi.single_apply,
      Finsupp.single_apply, Fin.sum_univ_succ]

private lemma quotient_half_order :
    addOrderOf (lattice.mkQ halfVector) = 2 := by
  apply addOrderOf_eq_prime
  · change lattice.mkQ ((2 : Int) • halfVector) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact twice_half_vector_mem_lattice
  · intro h
    apply half_vector_not_mem_lattice
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h

private lemma maximal_lattice_relative_index :
    lattice.toAddSubgroup.relIndex maximalLattice.toAddSubgroup = 2 := by
  let quotientMap : AmbientSpace →+ AmbientSpace ⧸ lattice := lattice.mkQ.toAddMonoidHom
  have hker : quotientMap.ker = lattice.toAddSubgroup := by
    ext x
    simp [quotientMap, Submodule.Quotient.mk_eq_zero]
  rw [← hker, AddSubgroup.relIndex_ker]
  have hmap : maximalLattice.map lattice.mkQ = Int ∙ lattice.mkQ halfVector := by
    rw [maximal_lattice_eq_parity, Submodule.map_sup, Submodule.map_span,
      Set.image_singleton]
    simp [Submodule.mkQ_map_self]
    rfl
  change Nat.card (maximalLattice.map lattice.mkQ) = 2
  rw [hmap]
  calc
    Nat.card (Int ∙ lattice.mkQ halfVector) =
        Nat.card (Int ⧸ Ideal.span {(addOrderOf (lattice.mkQ halfVector) : Int)}) :=
      Nat.card_congr
        (CharacterModule.intSpanEquivQuotAddOrderOf (lattice.mkQ halfVector)).toEquiv
    _ = Nat.card (ZMod 2) := by
      rw [quotient_half_order]
      exact Nat.card_congr (Int.quotientSpanEquivZMod 2).toEquiv
    _ = 2 := Nat.card_zmod 2

private lemma maximal_lattice_full_rank :
    Submodule.span Real (maximalLattice : Set AmbientSpace) = ⊤ := by
  apply top_unique
  rw [← chosenBasis.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  have hb : chosenBasis i ∈ lattice :=
    Submodule.subset_span (Set.mem_range_self i)
  have hm : chosenBasis i ∈ maximalLattice := Submodule.mem_sup_left hb
  exact hm

private lemma golden_operator_maximal_le :
    maximalLattice.map goldenOperator ≤ maximalLattice := by
  rw [maximalLattice, Submodule.map_sup]
  apply sup_le
  · exact le_sup_right
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    rw [golden_operator_sq_apply]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨z, hz, rfl⟩)
      (Submodule.mem_sup_left hz)

private lemma maximal_lattice_golden_stable (a : GoldenInt) :
    maximalLattice.map
        (a.a • LinearMap.id + a.b • goldenOperator) ≤ maximalLattice := by
  rintro _ ⟨x, hx, rfl⟩
  change a.a • x + a.b • goldenOperator x ∈ maximalLattice
  have hphi : goldenOperator x ∈ maximalLattice :=
    golden_operator_maximal_le ⟨x, hx, rfl⟩
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx)
    (Submodule.smul_mem _ _ hphi)

private lemma sqrt_five_order_range_eq_parity_kernel :
    sqrtFiveOrderEmbedding.toAddMonoidHom.range = goldenParity.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change ((2 * y.im : Int) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨y.im, rfl⟩
  · intro hx
    change (x.b : ZMod 2) = 0 at hx
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.b 2).mp hx
    refine ⟨(⟨x.a + b, b⟩ : Zsqrtd 5), ?_⟩
    apply GoldenInt.ext
    · simp [sqrtFiveOrderEmbedding]
    · simp [sqrtFiveOrderEmbedding, hb]

private lemma sqrt_five_order_index :
    sqrtFiveOrderEmbedding.toAddMonoidHom.range.index = 2 := by
  rw [sqrt_five_order_range_eq_parity_kernel, AddSubgroup.index_ker]
  have hsurjective : Function.Surjective goldenParity := by
    intro value
    refine ⟨⟨0, value.val⟩, ?_⟩
    change ((value.val : Int) : ZMod 2) = value
    exact_mod_cast ZMod.natCast_zmod_val value
  have hrange : goldenParity.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr hsurjective
  rw [hrange]
  simpa using Nat.card_zmod 2

/- **Golden maximal-order completion.** The explicitly constructed saturation of the source's
`Lambda^2 A4` lattice is full rank, is stable under every `a + b Phi` from `Z[phi]`, and is
minimal among submodules with those two containment/stability properties. Both the lattice
extension and the canonical inclusion `Z[sqrt 5] -> Z[phi]` have additive index two. -/
theorem golden_maximal_order_completion :
    lattice ≤ maximalLattice ∧
      Submodule.span Real (maximalLattice : Set AmbientSpace) = ⊤ ∧
      (∀ a : GoldenInt,
        maximalLattice.map (a.a • LinearMap.id + a.b • goldenOperator) ≤ maximalLattice) ∧
      (∀ completed : Submodule Int AmbientSpace,
        lattice ≤ completed ->
        (∀ a : GoldenInt,
          completed.map (a.a • LinearMap.id + a.b • goldenOperator) ≤ completed) ->
        maximalLattice ≤ completed) ∧
      lattice.toAddSubgroup.relIndex maximalLattice.toAddSubgroup = 2 ∧
      sqrtFiveOrderEmbedding.toAddMonoidHom.range.index = 2 := by
  refine ⟨le_sup_left, maximal_lattice_full_rank, maximal_lattice_golden_stable, ?_,
    maximal_lattice_relative_index, sqrt_five_order_index⟩
  intro completed hlattice hstable
  rw [maximalLattice]
  apply sup_le hlattice
  have hphi := hstable phi
  have haction : phi.a • LinearMap.id + phi.b • goldenOperator = goldenOperator := by
    ext y
    simp [phi]
  rw [haction] at hphi
  exact (Submodule.map_mono hlattice).trans hphi

#print axioms golden_maximal_order_completion

end

end D5.S3.Arith.Lattices.GoldenMaximalOrderCompletion
