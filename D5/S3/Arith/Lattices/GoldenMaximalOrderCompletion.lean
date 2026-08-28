/- GID: D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/GoldenMaximalOrderCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Hodge lattice completes to a stable index-two maximal-order lattice. -/

import D5.S0.Carrier.GoldenDiscriminant
import D5.S0.Carrier.Ring
import D5.S3.Arith.Lattices.ExactDualLatticeFormula
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Int.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Topology.Algebra.Module.Basic

-- Library-search audit trail (2026-08-28):
-- Repository search found the exact golden ring in `D5.S0.Carrier.Ring`, the golden
-- discriminant in `D5.S0.Carrier.GoldenDiscriminant`, and the source's concrete
-- `Lambda^2 A4` basis and Hodge matrix in `ExactDualLatticeFormula`; all are imported.
-- Pinned Mathlib's `AddSubgroup.relIndex_eq_two_iff_exists_notMem_and` is the exact
-- two-coset index theorem used below. General determinant-index APIs were also found,
-- but the two-coset theorem is the thinner match for this parity completion.
-- Loogle returned those Mathlib index declarations. LeanSearch, Reservoir, and
-- unauthenticated GitHub searches produced no specialized `Z[sqrt 5]` to `Z[phi]`
-- maximal-order theorem. The complete receipt is `/tmp/SEARCH-q3.md`.

namespace D5.S3.Arith.Lattices.GoldenMaximalOrderCompletion

open D5.S0.Carrier
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open Module Set
open scoped NumberField QuadraticAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

private instance goldenPolynomialNoRationalRoot :
    Fact (∀ r : ℚ, r ^ 2 ≠ (1 : ℚ) + 1 * r) := by
  refine ⟨fun r hr => ?_⟩
  have hsq : (5 : ℚ) = (2 * r - 1) ^ 2 := by
    nlinarith
  have hfive : IsSquare (5 : ℚ) := ⟨2 * r - 1, by nlinarith⟩
  have hfiveNat : IsSquare (5 : ℕ) := Rat.isSquare_natCast_iff.mp hfive
  exact (show Nat.Prime 5 by norm_num).not_isSquare hfiveNat

-- The source's named golden number field `Q(sqrt 5)`, presented by `omega^2 = omega + 1`.
abbrev GoldenNumberField := QuadraticAlgebra ℚ 1 1

noncomputable instance goldenNumberField : NumberField GoldenNumberField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

-- The ordered rational basis `(1, omega)` of the golden number field.
noncomputable def goldenFieldBasis : Basis (Fin 2) ℚ GoldenNumberField :=
  QuadraticAlgebra.basis 1 1

@[simp] private theorem goldenFieldBasis_zero :
    goldenFieldBasis 0 = (1 : GoldenNumberField) := by
  apply goldenFieldBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]

@[simp] private theorem goldenFieldBasis_one :
    goldenFieldBasis 1 = (QuadraticAlgebra.omega : GoldenNumberField) := by
  apply goldenFieldBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]

private theorem golden_field_trace (z : GoldenNumberField) :
    Algebra.trace ℚ GoldenNumberField z = 2 * z.re + z.im := by
  rw [Algebra.trace_eq_matrix_trace goldenFieldBasis, Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, goldenFieldBasis_zero,
    goldenFieldBasis_one, mul_one]
  simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]
  ring_nf

private theorem golden_field_basis_discr :
    Algebra.discr ℚ goldenFieldBasis = 5 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  norm_num [Algebra.traceMatrix_apply, Algebra.traceForm_apply, golden_field_trace]

private theorem golden_omega_isIntegral :
    IsIntegral ℤ (QuadraticAlgebra.omega : GoldenNumberField) := by
  let p : Polynomial ℤ :=
    (Polynomial.X ^ 2 - Polynomial.C 1) - Polynomial.X
  have hp : p.Monic := by
    apply (Polynomial.monic_X_pow_sub_C (1 : ℤ) (by norm_num : 2 ≠ 0)).sub_of_left
    rw [Polynomial.degree_X, Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2)]
    norm_num
  refine ⟨p, hp, ?_⟩
  simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_one, Polynomial.eval₂_X, map_one]
  rw [pow_two]
  rw [QuadraticAlgebra.omega_mul_omega_eq_add]
  norm_num

private theorem golden_field_basis_isIntegral (i : Fin 2) :
    IsIntegral ℤ (goldenFieldBasis i) := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simpa using
      (isIntegral_one : IsIntegral ℤ (1 : GoldenNumberField))
  · simpa using golden_omega_isIntegral

private noncomputable def goldenFieldBasisOnIntegralIndex :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 GoldenNumberField)) ℚ GoldenNumberField :=
  goldenFieldBasis.reindex
    (goldenFieldBasis.indexEquiv (NumberField.integralBasis GoldenNumberField))

private theorem golden_change_entry_isIntegral
    (i j : Module.Free.ChooseBasisIndex ℤ (𝓞 GoldenNumberField)) :
    IsIntegral ℤ
      ((NumberField.integralBasis GoldenNumberField).toMatrix
        goldenFieldBasisOnIntegralIndex i j) := by
  rw [Basis.toMatrix_apply]
  have hx : IsIntegral ℤ (goldenFieldBasisOnIntegralIndex j) := by
    simpa [goldenFieldBasisOnIntegralIndex, Basis.reindex_apply] using
      golden_field_basis_isIntegral
        ((goldenFieldBasis.indexEquiv
          (NumberField.integralBasis GoldenNumberField)).symm j)
  let x : 𝓞 GoldenNumberField := ⟨goldenFieldBasisOnIntegralIndex j, hx⟩
  change IsIntegral ℤ
    ((NumberField.integralBasis GoldenNumberField).repr
      (algebraMap (𝓞 GoldenNumberField) GoldenNumberField x) i)
  rw [NumberField.integralBasis_repr_apply]
  exact isIntegral_algebraMap

private theorem golden_numberField_discr :
    NumberField.discr GoldenNumberField = 5 := by
  let P := (NumberField.integralBasis GoldenNumberField).toMatrix
    goldenFieldBasisOnIntegralIndex
  have hP : ∀ i j, IsIntegral ℤ (P i j) := golden_change_entry_isIntegral
  have hdet : IsIntegral ℤ P.det := IsIntegral.det hP
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  have hchange :
      Algebra.discr ℚ goldenFieldBasisOnIntegralIndex =
        P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis GoldenNumberField) := by
    rw [← Algebra.discr_of_matrix_vecMul
      (NumberField.integralBasis GoldenNumberField) P]
    congr 1
    exact ((NumberField.integralBasis GoldenNumberField).toMatrix_map_vecMul
      goldenFieldBasisOnIntegralIndex).symm
  have hreindex :
      Algebra.discr ℚ goldenFieldBasisOnIntegralIndex =
        Algebra.discr ℚ goldenFieldBasis := by
    simpa [goldenFieldBasisOnIntegralIndex, Basis.coe_reindex] using
      Algebra.discr_reindex goldenFieldBasis
        (goldenFieldBasis.indexEquiv (NumberField.integralBasis GoldenNumberField))
  have hrat :
      (5 : ℚ) = (d : ℚ) ^ 2 * (NumberField.discr GoldenNumberField : ℚ) := by
    rw [← golden_field_basis_discr, ← hreindex, hchange, ← hd,
      NumberField.coe_discr]
    norm_num
  have hint : (5 : ℤ) = d ^ 2 * NumberField.discr GoldenNumberField := by
    exact_mod_cast hrat
  have hdvd : d ^ 2 ∣ (5 : ℤ) := ⟨NumberField.discr GoldenNumberField, hint⟩
  have habs := Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (5 : ℤ) ≠ 0)
  have hfourth : (d ^ 2) * (d ^ 2) ≤ (5 : ℤ) * 5 :=
    Int.natAbs_le_iff_mul_self_le.mp habs
  have hsq : d ^ 2 ≤ (5 : ℤ) := by
    nlinarith [sq_nonneg d]
  have hdle : d ≤ 2 := by
    by_contra h
    have : 3 ≤ d := by omega
    nlinarith
  have hdge : -2 ≤ d := by
    by_contra h
    have : d ≤ -3 := by omega
    nlinarith
  interval_cases d <;> omega

-- The rational scalar extension of the source lattice in its ordered six-element basis.
abbrev GoldenSpace := LatticeIndex -> ℚ

-- The chosen ordered basis after scalar extension from the integers to the rationals.
noncomputable def goldenBasis : Basis LatticeIndex ℚ GoldenSpace :=
  Pi.basisFun ℚ LatticeIndex

-- The source's integral Hodge matrix, now acting over the rationals.
def rationalHodgeMatrix : Matrix LatticeIndex LatticeIndex ℚ :=
  integralHodgeMatrix.map (Int.castRingHom ℚ)

-- The source operator `J` on the rational scalar extension.
def hodgeOperator : GoldenSpace →ₗ[ℚ] GoldenSpace :=
  Matrix.mulVecLin rationalHodgeMatrix

-- The golden operator `Phi = (I + J) / 2`.
noncomputable def goldenOperator : GoldenSpace →ₗ[ℚ] GoldenSpace :=
  (1 / 2 : ℚ) • (LinearMap.id + hodgeOperator)

-- The integral lattice `W_Z = Lambda^2 A4` in the source basis.
noncomputable def integerLattice : Submodule ℤ GoldenSpace :=
  Submodule.span ℤ (Set.range goldenBasis)

-- The same golden operator regarded as an integer-linear map.
noncomputable def goldenOperatorInt : GoldenSpace →ₗ[ℤ] GoldenSpace :=
  goldenOperator.restrictScalars ℤ

-- The source-defined saturation `W_max = W_Z + Phi W_Z`.
noncomputable def maximalOrderLattice : Submodule ℤ GoldenSpace :=
  integerLattice ⊔ integerLattice.map goldenOperatorInt

-- Full rank means that rational scalar extension spans the whole six-dimensional space.
def IsFullRank (L : Submodule ℤ GoldenSpace) : Prop :=
  Submodule.span ℚ (L : Set GoldenSpace) = ⊤

-- The concrete action of `a + b phi` through `Phi` on the Hodge space.
noncomputable def goldenIntegerOperator (r : GoldenInt) : GoldenSpace →ₗ[ℤ] GoldenSpace :=
  r.a • LinearMap.id + r.b • goldenOperatorInt

-- A lattice is preserved by the concrete `Z[phi]` action.
def IsGoldenStable (L : Submodule ℤ GoldenSpace) : Prop :=
  ∀ r : GoldenInt, L.map (goldenIntegerOperator r) ≤ L

private def goldenBCoord : GoldenInt →+ ℤ where
  toFun x := x.b
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] private theorem golden_b_zsmul (z : ℤ) (x : GoldenInt) :
    (z • x).b = z * x.b := by
  change goldenBCoord (z • x) = z * goldenBCoord x
  rw [map_zsmul]
  simp [goldenBCoord]

-- The nonmaximal order `Z[sqrt 5]`, namely the golden integers with even
-- `phi` coordinate because `sqrt 5 = 2 phi - 1`.
def sqrtFiveOrder : Subring GoldenInt where
  carrier := {x | ∃ k : ℤ, x.b = 2 * k}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨kx, hkx⟩ ⟨ky, hky⟩
    refine ⟨kx + ky, ?_⟩
    simp only [b_add, hkx, hky]
    ring
  neg_mem' := by
    rintro x ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    simp only [b_neg, hk]
    ring
  mul_mem' := by
    rintro x y ⟨kx, hkx⟩ ⟨ky, hky⟩
    refine ⟨x.a * ky + kx * y.a + 2 * kx * ky, ?_⟩
    simp only [b_mul, hkx, hky]
    ring

private theorem hodge_operator_sq (x : GoldenSpace) :
    hodgeOperator (hodgeOperator x) = 5 • x := by
  funext i
  fin_cases i <;>
    simp [hodgeOperator, rationalHodgeMatrix, integralHodgeMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private theorem golden_operator_sq (x : GoldenSpace) :
    goldenOperator (goldenOperator x) = goldenOperator x + x := by
  unfold goldenOperator
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
  rw [map_smul, map_add]
  rw [hodge_operator_sq]
  module

private theorem mem_integerLattice_iff (x : GoldenSpace) :
    x ∈ integerLattice ↔ ∀ i, ∃ z : ℤ, x i = (z : ℚ) := by
  constructor
  · intro hx
    rw [integerLattice, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    intro i
    refine ⟨c i, ?_⟩
    have hi := congrArg (fun y : GoldenSpace => y i) hc
    simpa [goldenBasis, Pi.basisFun_apply, Pi.single_apply] using hi.symm
  · intro hx
    classical
    choose z hz using hx
    rw [integerLattice, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨z, ?_⟩
    funext i
    simpa [goldenBasis, Pi.basisFun_apply, Pi.single_apply] using (hz i).symm

-- The nonintegral class added by completion, represented by `Phi(u12)`.
noncomputable def parityHalfClass : GoldenSpace :=
  goldenOperator (goldenBasis 0)

-- The cyclic subgroup generated by the added half-integral class.
noncomputable def parityHalfLattice : Submodule ℤ GoldenSpace :=
  ℤ ∙ parityHalfClass

private theorem phi_basis_sub_half_mem (j : LatticeIndex) :
    goldenOperator (goldenBasis j) - parityHalfClass ∈ integerLattice := by
  rw [mem_integerLattice_iff]
  intro i
  fin_cases j <;> fin_cases i <;>
    norm_num [parityHalfClass, goldenOperator, hodgeOperator, rationalHodgeMatrix,
      integralHodgeMatrix, goldenBasis, Matrix.mulVecLin_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    first
    | (refine ⟨-3, ?_⟩; norm_num) <;> done
    | (refine ⟨-2, ?_⟩; norm_num) <;> done
    | (refine ⟨-1, ?_⟩; norm_num) <;> done
    | (refine ⟨0, ?_⟩; norm_num) <;> done
    | (refine ⟨1, ?_⟩; norm_num) <;> done
    | (refine ⟨2, ?_⟩; norm_num) <;> done
    | (refine ⟨3, ?_⟩; norm_num) <;> done

private theorem two_parityHalf_mem :
    (2 : ℤ) • parityHalfClass ∈ integerLattice := by
  rw [mem_integerLattice_iff]
  intro i
  fin_cases i <;>
    norm_num [parityHalfClass, goldenOperator, hodgeOperator, rationalHodgeMatrix,
      integralHodgeMatrix, goldenBasis, Matrix.mulVecLin_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    first
    | (refine ⟨-3, ?_⟩; norm_num) <;> done
    | (refine ⟨-2, ?_⟩; norm_num) <;> done
    | (refine ⟨-1, ?_⟩; norm_num) <;> done
    | (refine ⟨0, ?_⟩; norm_num) <;> done
    | (refine ⟨1, ?_⟩; norm_num) <;> done
    | (refine ⟨2, ?_⟩; norm_num) <;> done
    | (refine ⟨3, ?_⟩; norm_num) <;> done

private theorem parityHalf_not_mem :
    parityHalfClass ∉ integerLattice := by
  intro hmem
  obtain ⟨z, hz⟩ := (mem_integerLattice_iff parityHalfClass).mp hmem 0
  have hcoordinate : parityHalfClass 0 = (1 / 2 : ℚ) := by
    norm_num [parityHalfClass, goldenOperator, hodgeOperator, rationalHodgeMatrix,
      integralHodgeMatrix, goldenBasis, Matrix.mulVecLin_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hcoordinate] at hz
  have hcast : (2 * z : ℚ) = 1 := by linarith
  have hint : 2 * z = 1 := by exact_mod_cast hcast
  omega

private theorem maximal_eq_integer_sup_half :
    maximalOrderLattice = integerLattice ⊔ parityHalfLattice := by
  apply le_antisymm
  · rw [maximalOrderLattice]
    apply sup_le
    · exact le_sup_left
    · rw [Submodule.map_le_iff_le_comap, integerLattice, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change goldenOperator (goldenBasis j) ∈
        integerLattice ⊔ parityHalfLattice
      have hdifference : goldenOperator (goldenBasis j) - parityHalfClass ∈
          integerLattice ⊔ parityHalfLattice :=
        Submodule.mem_sup_left (phi_basis_sub_half_mem j)
      have hhalf : parityHalfClass ∈ integerLattice ⊔ parityHalfLattice :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self parityHalfClass)
      convert Submodule.add_mem _ hdifference hhalf using 1 <;> module
  · apply sup_le
    · exact le_sup_left
    · rw [parityHalfLattice, Submodule.span_le]
      intro x hx
      rcases hx with rfl
      rw [maximalOrderLattice]
      apply Submodule.mem_sup_right
      exact ⟨goldenBasis 0,
        Submodule.subset_span (Set.mem_range_self 0), rfl⟩

private theorem integer_le_maximal : integerLattice ≤ maximalOrderLattice := by
  rw [maximalOrderLattice]
  exact le_sup_left

private theorem maximal_full_rank : IsFullRank maximalOrderLattice := by
  apply top_unique
  rw [← goldenBasis.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact integer_le_maximal (Submodule.subset_span (Set.mem_range_self i))

private theorem golden_operator_preserves_maximal :
    maximalOrderLattice.map goldenOperatorInt ≤ maximalOrderLattice := by
  rintro _ ⟨x, hx, rfl⟩
  rw [maximalOrderLattice] at hx ⊢
  rcases (Submodule.mem_sup.mp hx) with ⟨a, ha, b, hb, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  change goldenOperator (a + goldenOperator y) ∈ _
  rw [map_add, golden_operator_sq]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right ⟨a, ha, rfl⟩)
    (Submodule.add_mem _ (Submodule.mem_sup_right ⟨y, hy, rfl⟩)
      (Submodule.mem_sup_left hy))

private theorem golden_ring_preserves_maximal : IsGoldenStable maximalOrderLattice := by
  intro r
  rintro _ ⟨x, hx, rfl⟩
  change r.a • x + r.b • goldenOperator x ∈ maximalOrderLattice
  exact Submodule.add_mem _ (Submodule.smul_mem _ r.a hx)
    (Submodule.smul_mem _ r.b (golden_operator_preserves_maximal ⟨x, hx, rfl⟩))

private theorem maximal_minimal :
    ∀ M : Submodule ℤ GoldenSpace,
      integerLattice ≤ M → IsGoldenStable M → maximalOrderLattice ≤ M := by
  intro M hInteger hStable
  rw [maximalOrderLattice]
  apply sup_le hInteger
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  have hPhi := hStable phi
  have hop : goldenIntegerOperator phi = goldenOperatorInt := by
    ext y i
    simp [goldenIntegerOperator, phi, goldenOperatorInt]
  rw [hop] at hPhi
  exact hPhi ⟨x, hInteger hx, rfl⟩

private theorem two_coset_index :
    integerLattice.toAddSubgroup.relIndex maximalOrderLattice.toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨parityHalfClass, ?_, parityHalf_not_mem, ?_⟩
  · rw [maximal_eq_integer_sup_half]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self parityHalfClass)
  · intro b hb
    rw [maximal_eq_integer_sup_half] at hb
    rcases (Submodule.mem_sup.mp hb) with ⟨a, ha, c, hc, rfl⟩
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hc
    by_cases heven : ∃ k : ℤ, n = 2 * k
    · right
      rcases heven with ⟨k, rfl⟩
      exact Submodule.add_mem _ ha <| by
        simpa [mul_smul, mul_comm] using
          Submodule.smul_mem integerLattice k two_parityHalf_mem
    · left
      have hnotEven : ¬ Even n := by
        rintro ⟨k, hk⟩
        apply heven
        exact ⟨k, by omega⟩
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hnotEven
      have hodd : n + 1 = 2 * (k + 1) := by omega
      have hcombine : n • parityHalfClass + parityHalfClass =
          (n + 1) • parityHalfClass := by module
      rw [add_assoc, hcombine, hodd]
      exact Submodule.add_mem _ ha <| by
        simpa [mul_smul, mul_comm] using
          Submodule.smul_mem integerLattice (k + 1) two_parityHalf_mem

private theorem strict_sqrtFiveOrder : sqrtFiveOrder < (⊤ : Subring GoldenInt) := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hphi : phi ∈ sqrtFiveOrder := by rw [htop]; trivial
  rcases hphi with ⟨k, hk⟩
  norm_num [phi] at hk
  omega

private theorem sqrtFiveOrder_index_two :
    sqrtFiveOrder.toAddSubgroup.relIndex (⊤ : Subring GoldenInt).toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨phi, by trivial, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    norm_num [phi] at hk
    omega
  · intro x _
    by_cases heven : ∃ k : ℤ, x.b = 2 * k
    · exact Or.inr heven
    · left
      change ∃ k : ℤ, (x + phi).b = 2 * k
      have hnotEven : ¬ Even x.b := by
        rintro ⟨k, hk⟩
        apply heven
        exact ⟨k, by omega⟩
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hnotEven
      refine ⟨k + 1, ?_⟩
      simp only [b_add, phi_b]
      omega

private theorem two_repairs_order_parity :
    ∀ x : GoldenInt, (2 : ℤ) • x ∈ sqrtFiveOrder := by
  intro x
  refine ⟨x.b, ?_⟩
  exact golden_b_zsmul 2 x

-- The coordinate embedding `Z[phi] -> Q(sqrt 5)` sending `phi` to `omega`.
def goldenIntegerEmbedding : GoldenInt →+* GoldenNumberField where
  toFun x := ⟨(x.a : ℚ), (x.b : ℚ)⟩
  map_zero' := by ext <;> norm_num
  map_one' := by ext <;> norm_num
  map_add' x y := by ext <;> norm_num
  map_mul' x y := by ext <;> norm_num <;> push_cast <;> ring

private theorem goldenIntegerEmbedding_injective :
    Function.Injective goldenIntegerEmbedding := by
  intro x y hxy
  apply GoldenInt.ext
  · have ha := congrArg QuadraticAlgebra.re hxy
    change (x.a : ℚ) = (y.a : ℚ) at ha
    exact_mod_cast ha
  · have hb := congrArg QuadraticAlgebra.im hxy
    change (x.b : ℚ) = (y.b : ℚ) at hb
    exact_mod_cast hb

private instance goldenTwoPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- The rational prime ideal `(2)` whose extensions define the source's 2-adic channel.
def goldenTwoBaseIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private instance goldenTwoBaseIdeal_isMaximal : goldenTwoBaseIdeal.IsMaximal := by
  change (Ideal.span {(2 : ℤ)}).IsMaximal
  exact Int.ideal_span_isMaximal_of_prime 2

private theorem exists_goldenTwoPrimeIdeal :
    ∃ Q : Ideal (𝓞 GoldenNumberField),
      Q.IsMaximal ∧ Q.LiesOver goldenTwoBaseIdeal :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 GoldenNumberField) goldenTwoBaseIdeal

-- A named prime of the golden integer ring above `(2)`.
noncomputable def goldenTwoPrimeIdeal : Ideal (𝓞 GoldenNumberField) :=
  Classical.choose exists_goldenTwoPrimeIdeal

private theorem goldenTwoPrimeIdeal_isMaximal : goldenTwoPrimeIdeal.IsMaximal :=
  (Classical.choose_spec exists_goldenTwoPrimeIdeal).1

private theorem goldenTwoPrimeIdeal_liesOver :
    goldenTwoPrimeIdeal.LiesOver goldenTwoBaseIdeal :=
  (Classical.choose_spec exists_goldenTwoPrimeIdeal).2

private theorem goldenTwoPrimeIdeal_ne_bot : goldenTwoPrimeIdeal ≠ ⊥ := by
  intro hbot
  letI : goldenTwoPrimeIdeal.LiesOver goldenTwoBaseIdeal :=
    goldenTwoPrimeIdeal_liesOver
  have htwo : (2 : ℤ) ∈ goldenTwoBaseIdeal := by
    exact Ideal.subset_span (by simp)
  have hmap : algebraMap ℤ (𝓞 GoldenNumberField) (2 : ℤ) ∈ goldenTwoPrimeIdeal :=
    (Ideal.mem_of_liesOver goldenTwoPrimeIdeal goldenTwoBaseIdeal 2).mp htwo
  rw [hbot] at hmap
  norm_num at hmap

-- The source-specific finite place of `Q(sqrt 5)` lying above the rational prime 2.
noncomputable def goldenTwoFinitePlace :
    IsDedekindDomain.HeightOneSpectrum (𝓞 GoldenNumberField) where
  asIdeal := goldenTwoPrimeIdeal
  isPrime := goldenTwoPrimeIdeal_isMaximal.isPrime
  ne_bot := goldenTwoPrimeIdeal_ne_bot

-- The concluding finite-place completion in theorem 28.1.
abbrev GoldenTwoAdicCompletion :=
  goldenTwoFinitePlace.adicCompletion GoldenNumberField
abbrev GoldenTwoAdicSpace := LatticeIndex → GoldenTwoAdicCompletion
noncomputable def goldenTwoAdicEmbedding :
    GoldenNumberField →+* GoldenTwoAdicCompletion :=
  NumberField.FinitePlace.embedding goldenTwoFinitePlace
noncomputable def goldenSpaceTwoAdicEmbeddingInt :
    GoldenSpace →ₗ[ℤ] GoldenTwoAdicSpace :=
  (LinearMap.pi fun i => (Algebra.linearMap ℚ GoldenTwoAdicCompletion).comp
    (LinearMap.proj i : GoldenSpace →ₗ[ℚ] ℚ)).restrictScalars ℤ
noncomputable def integerLatticeTwoAdicCompletion : Submodule ℤ GoldenTwoAdicSpace :=
  (integerLattice.map goldenSpaceTwoAdicEmbeddingInt).topologicalClosure
noncomputable def maximalOrderLatticeTwoAdicCompletion : Submodule ℤ GoldenTwoAdicSpace :=
  (maximalOrderLattice.map goldenSpaceTwoAdicEmbeddingInt).topologicalClosure
-- The golden integers inside the same named 2-adic finite-place completion.
noncomputable def goldenIntegerTwoAdicEmbedding :
    GoldenInt →+* GoldenTwoAdicCompletion :=
  goldenTwoAdicEmbedding.comp goldenIntegerEmbedding
private theorem goldenIntegerTwoAdicEmbedding_injective :
    Function.Injective goldenIntegerTwoAdicEmbedding :=
  goldenTwoAdicEmbedding.injective.comp goldenIntegerEmbedding_injective

-- The image of the nonmaximal order in the named finite-place completion above 2.
noncomputable def completedSqrtFiveOrder : Subring GoldenTwoAdicCompletion :=
  sqrtFiveOrder.map goldenIntegerTwoAdicEmbedding

private theorem two_repairs_order_parity_in_completion :
    ∀ x : GoldenInt,
      goldenIntegerTwoAdicEmbedding ((2 : ℤ) • x) ∈ completedSqrtFiveOrder := by
  intro x
  change ∃ y, y ∈ sqrtFiveOrder ∧
    goldenIntegerTwoAdicEmbedding y = goldenIntegerTwoAdicEmbedding ((2 : ℤ) • x)
  exact ⟨(2 : ℤ) • x, two_repairs_order_parity x, rfl⟩
private theorem two_smul_maximal_mem_integer (x : GoldenSpace) (hx : x ∈ maximalOrderLattice) :
    (2 : ℤ) • x ∈ integerLattice := by
  rw [maximal_eq_integer_sup_half] at hx
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have haTwo : (2 : ℤ) • a ∈ integerLattice := Submodule.smul_mem integerLattice 2 ha
  have hhalfTwo : n • ((2 : ℤ) • parityHalfClass) ∈ integerLattice :=
    Submodule.smul_mem integerLattice n two_parityHalf_mem
  convert Submodule.add_mem integerLattice haTwo hhalfTwo using 1 <;> module
private theorem two_repairs_lattice_parity_in_completion :
    ∀ x : maximalOrderLatticeTwoAdicCompletion,
      (2 : ℤ) • (x : GoldenTwoAdicSpace) ∈ integerLatticeTwoAdicCompletion := by
  intro x
  have hMaps : Set.MapsTo (fun y : GoldenTwoAdicSpace => (2 : ℤ) • y)
      (maximalOrderLattice.map goldenSpaceTwoAdicEmbeddingInt : Set GoldenTwoAdicSpace)
      (integerLattice.map goldenSpaceTwoAdicEmbeddingInt : Set GoldenTwoAdicSpace) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.mem_map.mpr ⟨(2 : ℤ) • y, two_smul_maximal_mem_integer y hy,
      goldenSpaceTwoAdicEmbeddingInt.map_smul (2 : ℤ) y⟩
  change (2 : ℤ) • (x : GoldenTwoAdicSpace) ∈ closure
    (integerLattice.map goldenSpaceTwoAdicEmbeddingInt : Set GoldenTwoAdicSpace)
  exact hMaps.closure (continuous_const_smul (2 : ℤ)) x.property
-- The exterior-square matrix induced by the even five-cycle
-- `(1 2 3 4 5)` on the `A4` root coordinates.
def fiveCycleMatrix : Matrix LatticeIndex LatticeIndex ℤ :=
  !![1, 1, 1, 0, 0, 0;
     -1, 0, 0, 1, 1, 0;
     0, -1, 0, -1, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0]

-- The five-cycle acting on the rational scalar extension.
def fiveCycleRationalMatrix : Matrix LatticeIndex LatticeIndex ℚ :=
  fiveCycleMatrix.map (Int.castRingHom ℚ)

-- The five-cycle acting on the rational scalar extension.
def fiveCycleOperator : GoldenSpace →ₗ[ℚ] GoldenSpace :=
  Matrix.mulVecLin fiveCycleRationalMatrix

set_option maxHeartbeats 1000000 in
-- Expanding the 36 entries of the fifth matrix power exceeds the default budget.
private theorem five_cycle_matrix_pow_five : fiveCycleRationalMatrix ^ 5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveCycleRationalMatrix, fiveCycleMatrix, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ]

private theorem five_cycle_fifth_power (x : GoldenSpace) :
    fiveCycleOperator
      (fiveCycleOperator
        (fiveCycleOperator
          (fiveCycleOperator (fiveCycleOperator x)))) = x := by
  have h := congrArg
    (fun (M : Matrix LatticeIndex LatticeIndex ℚ) => M.mulVec x)
    five_cycle_matrix_pow_five
  simpa [fiveCycleOperator, pow_succ, mul_assoc] using h

private theorem five_cycle_hodge_commute :
    fiveCycleRationalMatrix * rationalHodgeMatrix =
      rationalHodgeMatrix * fiveCycleRationalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveCycleRationalMatrix, fiveCycleMatrix, rationalHodgeMatrix,
      integralHodgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem five_cycle_commutes_phi (x : GoldenSpace) :
    fiveCycleOperator (goldenOperator x) =
      goldenOperator (fiveCycleOperator x) := by
  change fiveCycleRationalMatrix.mulVec
      ((1 / 2 : ℚ) • (x + rationalHodgeMatrix.mulVec x)) =
    (1 / 2 : ℚ) •
      (fiveCycleRationalMatrix.mulVec x +
        rationalHodgeMatrix.mulVec (fiveCycleRationalMatrix.mulVec x))
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, five_cycle_hodge_commute]

private theorem five_cycle_preserves_integer :
    integerLattice.map (fiveCycleOperator.restrictScalars ℤ) ≤ integerLattice := by
  rw [Submodule.map_le_iff_le_comap, integerLattice, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change fiveCycleOperator (goldenBasis j) ∈ integerLattice
  rw [mem_integerLattice_iff]
  intro i
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveCycleOperator, fiveCycleMatrix, goldenBasis,
      Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, fiveCycleRationalMatrix, Pi.single_apply] <;>
    first
    | (refine ⟨-1, ?_⟩; norm_num) <;> done
    | (refine ⟨0, ?_⟩; norm_num) <;> done
    | (refine ⟨1, ?_⟩; norm_num) <;> done

private theorem five_cycle_preserves_maximal (x : GoldenSpace)
    (hx : x ∈ maximalOrderLattice) : fiveCycleOperator x ∈ maximalOrderLattice := by
  rw [maximalOrderLattice] at hx ⊢
  rcases (Submodule.mem_sup.mp hx) with ⟨a, ha, b, hb, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  change fiveCycleOperator (a + goldenOperator y) ∈
    integerLattice ⊔ integerLattice.map goldenOperatorInt
  rw [map_add, five_cycle_commutes_phi]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (five_cycle_preserves_integer ⟨a, ha, rfl⟩))
    (Submodule.mem_sup_right ⟨fiveCycleOperator y,
      five_cycle_preserves_integer ⟨y, hy, rfl⟩, rfl⟩)

-- The concrete five-cycle restricted to the completed lattice.
noncomputable def fiveCycleOnCompletionLinear :
    maximalOrderLattice →ₗ[ℤ] maximalOrderLattice where
  toFun x := ⟨fiveCycleOperator x, five_cycle_preserves_maximal x x.property⟩
  map_add' x y := by ext i; simp
  map_smul' z x := by
    ext i
    change fiveCycleOperator ((z : ℚ) • (x : GoldenSpace)) i =
      ((z : ℚ) • fiveCycleOperator (x : GoldenSpace)) i
    rw [map_smul]

private theorem fiveCycleOnCompletion_bijective :
    Function.Bijective fiveCycleOnCompletionLinear := by
  constructor
  · intro x y hxy
    have h := congrArg (fun z : maximalOrderLattice =>
      fiveCycleOnCompletionLinear
        (fiveCycleOnCompletionLinear
          (fiveCycleOnCompletionLinear
            (fiveCycleOnCompletionLinear z)))) hxy
    apply Subtype.ext
    have hval := congrArg (fun z : maximalOrderLattice => (z : GoldenSpace)) h
    change fiveCycleOperator
        (fiveCycleOperator
          (fiveCycleOperator
            (fiveCycleOperator (fiveCycleOperator (x : GoldenSpace))))) =
      fiveCycleOperator
        (fiveCycleOperator
          (fiveCycleOperator
            (fiveCycleOperator (fiveCycleOperator (y : GoldenSpace))))) at hval
    rw [five_cycle_fifth_power, five_cycle_fifth_power] at hval
    exact hval
  · intro y
    let x1 : maximalOrderLattice := fiveCycleOnCompletionLinear y
    let x2 : maximalOrderLattice := fiveCycleOnCompletionLinear x1
    let x3 : maximalOrderLattice := fiveCycleOnCompletionLinear x2
    let x4 : maximalOrderLattice := fiveCycleOnCompletionLinear x3
    refine ⟨x4, ?_⟩
    apply Subtype.ext
    simpa [x1, x2, x3, x4, fiveCycleOnCompletionLinear] using
      five_cycle_fifth_power y.1

-- The order-five automorphism of the completed `Lambda^2 A4` lattice.
noncomputable def fiveCycleOnCompletion :
    maximalOrderLattice ≃ₗ[ℤ] maximalOrderLattice :=
  LinearEquiv.ofBijective fiveCycleOnCompletionLinear fiveCycleOnCompletion_bijective

private theorem fiveCycleOnCompletion_order : orderOf fiveCycleOnCompletion = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simpa [pow_succ, fiveCycleOnCompletion, fiveCycleOnCompletionLinear] using
      five_cycle_fifth_power x.1
  · intro hone
    let e0 : maximalOrderLattice :=
      ⟨goldenBasis 0, integer_le_maximal
        (Submodule.subset_span (Set.mem_range_self 0))⟩
    have hvalue := congrArg (fun e : maximalOrderLattice ≃ₗ[ℤ] maximalOrderLattice =>
      ((e e0 : maximalOrderLattice) : GoldenSpace) 1) hone
    norm_num [fiveCycleOnCompletion, fiveCycleOnCompletionLinear, e0,
      fiveCycleOperator, fiveCycleMatrix, goldenBasis, Matrix.mulVecLin_apply,
      Pi.basisFun_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      fiveCycleRationalMatrix, Pi.single_apply] at hvalue

-- Golden maximal-order completion. The ten conjuncts correspond, in order,
-- to the ten semantic assertions counted in OACTC theorem 28.1.
theorem golden_maximal_order_completion :
    maximalOrderLattice =
        integerLattice ⊔ integerLattice.map goldenOperatorInt ∧
      IsFullRank maximalOrderLattice ∧
      integerLattice ≤ maximalOrderLattice ∧
      IsGoldenStable maximalOrderLattice ∧
      (∀ M : Submodule ℤ GoldenSpace,
        integerLattice ≤ M → IsGoldenStable M → maximalOrderLattice ≤ M) ∧
      sqrtFiveOrder < (⊤ : Subring GoldenInt) ∧
      sqrtFiveOrder.toAddSubgroup.relIndex
        (⊤ : Subring GoldenInt).toAddSubgroup = 2 ∧
      NumberField.discr GoldenNumberField = 5 ∧
      orderOf fiveCycleOnCompletion = 5 ∧
      (∀ x : maximalOrderLatticeTwoAdicCompletion,
        (2 : ℤ) • (x : GoldenTwoAdicSpace) ∈ integerLatticeTwoAdicCompletion) := by
  refine ⟨rfl, maximal_full_rank, integer_le_maximal,
    golden_ring_preserves_maximal, maximal_minimal, strict_sqrtFiveOrder,
    sqrtFiveOrder_index_two, golden_numberField_discr, fiveCycleOnCompletion_order,
    two_repairs_lattice_parity_in_completion⟩

-- Reverse probe: the public statement exposes the strict index-two order inclusion and symmetry.
example :
    sqrtFiveOrder < (⊤ : Subring GoldenInt) ∧
      sqrtFiveOrder.toAddSubgroup.relIndex
        (⊤ : Subring GoldenInt).toAddSubgroup = 2 ∧
      orderOf fiveCycleOnCompletion = 5 := by
  rcases golden_maximal_order_completion with
    ⟨_, _, _, _, _, hstrict, hindex, _, horder, _⟩
  exact ⟨hstrict, hindex, horder⟩

-- Reverse probe for the repaired carriers: field discriminant and the lattice completion above 2.
example :
    NumberField.discr GoldenNumberField = 5 ∧
      ∀ x : maximalOrderLatticeTwoAdicCompletion,
        (2 : ℤ) • (x : GoldenTwoAdicSpace) ∈ integerLatticeTwoAdicCompletion := by
  rcases golden_maximal_order_completion with
    ⟨_, _, _, _, _, _, _, hdisc, _, hcompletion⟩
  exact ⟨hdisc, hcompletion⟩
example : CompleteSpace maximalOrderLatticeTwoAdicCompletion := by
  unfold maximalOrderLatticeTwoAdicCompletion; infer_instance
-- Trivialization probe: the added class is genuinely absent from the original lattice.
example : parityHalfClass ∈ maximalOrderLattice ∧ parityHalfClass ∉ integerLattice := by
  constructor
  · rw [maximal_eq_integer_sup_half]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self parityHalfClass)
  · exact parityHalf_not_mem

#print axioms golden_maximal_order_completion

end D5.S3.Arith.Lattices.GoldenMaximalOrderCompletion
