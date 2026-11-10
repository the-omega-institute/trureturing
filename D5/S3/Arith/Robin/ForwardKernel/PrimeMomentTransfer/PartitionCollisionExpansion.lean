/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite mixed moment admits a kernel-partition quadratic collision expansion. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs

/-! Grouping by equality partitions is the classical fiber decomposition of a finite sum
(equivalently, the set-partition expansion of power sums). The quadratic reduction below
extends the finite-order algebraic moment identities to arbitrary order. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]

/-- Coefficients of the remainder of `X^m` modulo `X^2 - a*X - b`.
The initial value also handles the empty product. -/
def quadraticPowerCoeffs (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | m + 1 => (a * (quadraticPowerCoeffs a b m).1 +
      (quadraticPowerCoeffs a b m).2, b * (quadraticPowerCoeffs a b m).1)

/-- The quadratic relation reduces every power in any commutative real algebra. -/
theorem quadraticPowerCoeffs_pow (a b : ℝ) (y : A)
    (hy : y ^ 2 = a • y + b • (1 : A)) (m : ℕ) :
    y ^ m = (quadraticPowerCoeffs a b m).1 • y +
      (quadraticPowerCoeffs a b m).2 • (1 : A) := by
  induction m with
  | zero => simp [quadraticPowerCoeffs]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [quadraticPowerCoeffs, Algebra.smul_def, map_add, map_mul, mul_one] at *
    linear_combination (algebraMap ℝ A (quadraticPowerCoeffs a b m).1) * hy

/-- Equality patterns realized by tuples of the given order and index type.
Omitted partitions have no index assignments and hence contribute zero. -/
def tupleKernelPatterns (k : ℕ) (ι : Type*) [Fintype ι] : Finset (Setoid (Fin k)) :=
  Finset.univ.image (fun d : Fin k → ι => Setoid.ker d)

/-- Mathlib's fiber sum, specialized to the kernel partition of a tuple. -/
theorem sum_eq_tupleKernel_sums {k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin k → ι) → M) :
    (∑ d, F d) = ∑ σ ∈ tupleKernelPatterns k ι,
      ∑ d : Fin k → ι with Setoid.ker d = σ, F d := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun d _ => Finset.mem_image.mpr
    ⟨d, Finset.mem_univ _, rfl⟩) F

/-- The size of an equality block, viewed as a class of the position type. -/
def kernelBlockSize {k : ℕ} (σ : Setoid (Fin k)) (B : Quotient σ) : ℕ :=
  (Finset.univ.filter (fun i => Quotient.mk σ i = B)).card

omit [Fintype ι] [Algebra ℝ A] in
private theorem tuple_product_eq_block_powers {k : ℕ} (σ : Setoid (Fin k))
    (d : Fin k → ι) (hd : Setoid.ker d = σ) (Y : ι → A) :
    (∏ i, Y (d i)) = ∏ B : Quotient σ, Y (d B.out) ^ kernelBlockSize σ B := by
  rw [← Finset.prod_fiberwise Finset.univ (Quotient.mk σ) (fun i => Y (d i))]
  apply Finset.prod_congr rfl
  intro B hB
  calc
    (∏ i ∈ Finset.univ with Quotient.mk σ i = B, Y (d i)) =
        ∏ _i ∈ Finset.univ with Quotient.mk σ _i = B, Y (d B.out) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      change (Setoid.ker d) i B.out
      rw [hd]
      exact Quotient.exact ((Finset.mem_filter.mp hi).2.trans (Quotient.out_eq B).symm)
    _ = _ := by simp [kernelBlockSize]

omit [Fintype ι] in
private theorem tuple_quadratic_reduction {k : ℕ} (σ : Setoid (Fin k))
    (d : Fin k → ι) (hd : Setoid.ker d = σ)
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hquad : ∀ e, Y e ^ 2 = a • Y e + b • (1 : A)) :
    ℓ (∏ i, Y (d i)) = ∑ S : Finset (Quotient σ),
      ((∏ B ∈ S, (quadraticPowerCoeffs a b (kernelBlockSize σ B)).1) *
       (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (kernelBlockSize σ B)).2)) *
      ℓ (∏ B ∈ S, Y (d B.out)) := by
  rw [tuple_product_eq_block_powers σ d hd Y]
  simp_rw [quadraticPowerCoeffs_pow a b _ (hquad _) _]
  rw [Fintype.prod_add, map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_smul, Finset.prod_smul]
  simp only [Finset.prod_const_one, smul_mul_smul_comm, mul_one, map_smul, smul_eq_mul]

/-- The residual moment for a fixed equality pattern and a set of retained blocks.
The exact-kernel condition is the block-injectivity condition: values agree within each
block and differ between distinct blocks. The positional weight product equals the
product of the aggregated weights over the blocks. -/
def kernelDistinctMoment {k : ℕ} (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (f : Fin k → ι → ℝ) (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) : ℝ :=
  ∑ d : Fin k → ι with Setoid.ker d = σ,
    (∏ i, f i (d i)) * ℓ (∏ B ∈ S, Y (d B.out))

/-- At every order, each collision block contributes either its linear coefficient
and one algebra element, or its constant coefficient. No centering, normalization,
positivity, or independence is required. Empty index types and order zero are included. -/
theorem quadratic_moment_eq_partition_expansion {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (f : Fin k → ι → ℝ) :
    quadraticFamilyMoment ℓ Y f =
      ∑ σ ∈ tupleKernelPatterns k ι, ∑ S : Finset (Quotient σ),
        ((∏ B ∈ S, (quadraticPowerCoeffs a b (kernelBlockSize σ B)).1) *
         (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (kernelBlockSize σ B)).2)) *
        kernelDistinctMoment ℓ Y f σ S := by
  rw [quadraticFamilyMoment_eq_tuple_sum, sum_eq_tupleKernel_sums]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [kernelDistinctMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [tuple_quadratic_reduction σ d (Finset.mem_filter.mp hd).2 ℓ Y a b hquad,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
