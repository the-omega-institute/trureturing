/- GID: D5/S3/FiniteGroups/RationalGroupMatrixCutoff
   generality: G
   utility: exact rational block-order cutoff for natural group-matrix uniformization
   digest: Uniformization kills precisely the nontrivial rational blocks, whose division-ring matrix orders give the positive bound n times the largest original block order.
-/
import D5.S3.FiniteGroups.NaturalGroupMatrixUniformization
import D5.S3.FiniteGroups.RationalGroupAlgebraSplitting
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.FiniteGroups.NaturalGroupMatrixUniformization
open D5.S3.FiniteGroups.RationalGroupAlgebraSplitting (RationalDecomposition)

namespace D5.S3.FiniteGroups.RationalGroupMatrixCutoff

section DivisionRingBound

variable {D I : Type*} [DivisionRing D] [Fintype I] [DecidableEq I]

/-- Right multiplication reverses products, but preserves powers of one matrix. -/
private theorem right_power (M : Matrix I I D) (k : ℕ) :
    (M^k).toLinearMapRight' = (M.toLinearMapRight')^k := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
      rw [pow_succ, Matrix.toLinearMapRight'_mul, ih]
      change M.toLinearMapRight' * (M.toLinearMapRight')^k = (M.toLinearMapRight')^(k+1)
      exact (pow_succ' M.toLinearMapRight' k).symm

/-- A nilpotent d by d matrix over an arbitrary division ring vanishes by d. -/
private theorem matrix_power_zero_at_card (M : Matrix I I D)
    {N : ℕ} (hN : M^N = 0) : M^(Fintype.card I) = 0 := by
  let T : Module.End D (I → D) := M.toLinearMapRight'
  have hT : T^N = 0 := by
    change (M.toLinearMapRight')^N = 0
    rw [← right_power, hN, map_zero]
  have hker := Module.End.ker_pow_le_ker_pow_finrank T N
  have hdim : T^(Module.finrank D (I → D)) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker (T^N) := by simp only [hT, LinearMap.ker_zero, Submodule.mem_top]
    exact hker hv
  apply Matrix.toLinearMapRight'.injective
  rw [right_power, map_zero]
  simpa only [Module.finrank_pi] using hdim

/-- Used to pass from the sharp component order n*r to a common k. -/
private theorem matrix_power_zero_mono (M : Matrix I I D)
    {a k : ℕ} (hak : a ≤ k) (ha : M^a = 0) : M^k = 0 := by
  calc
    M^k = M^(a+(k-a)) := by rw [Nat.add_sub_of_le hak]
    _ = M^a * M^(k-a) := pow_add M a (k-a)
    _ = 0 := by rw [ha, zero_mul]

end DivisionRingBound

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

def naturalToRational : MonoidAlgebra ℕ H →+* MonoidAlgebra ℚ H :=
  MonoidAlgebra.mapRingHom H (Nat.castRingHom ℚ)

def rationalMatrix : GroupMat H n n →+* Matrix (Fin n) (Fin n) (MonoidAlgebra ℚ H) :=
  (naturalToRational (H := H)).mapMatrix

/-- The largest ORIGINAL nontrivial rational matrix order. -/
def bH (W : RationalDecomposition H) : ℕ := Finset.univ.sup W.order

private theorem block_order_le (W : RationalDecomposition H) (l : Fin W.count) :
    W.order l ≤ bH W := Finset.le_sup (f := W.order) (Finset.mem_univ l)

private theorem cutoff_positive (W : RationalDecomposition H) (hn : 0 < n) :
    0 < n*bH W := by
  let l : Fin W.count := ⟨0,W.count_pos⟩
  exact Nat.mul_pos hn (lt_of_lt_of_le (W.order_pos l) (block_order_le W l))

private def component (W : RationalDecomposition H) (l : Fin W.count) :
    MonoidAlgebra ℚ H →+* Matrix (Fin (W.order l)) (Fin (W.order l)) (W.DivisionAlgebra l) where
  toFun x := (W.equiv x).2 l
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp

/-- The faithful component map, flattened over the SAME division algebra. -/
def block (W : RationalDecomposition H) (l : Fin W.count) :
    GroupMat H n n →+* Matrix (Fin n × Fin (W.order l)) (Fin n × Fin (W.order l))
      (W.DivisionAlgebra l) :=
  (Matrix.compRingEquiv (Fin n) (Fin (W.order l)) (W.DivisionAlgebra l)).toRingHom.comp
    (((component W l).comp naturalToRational).mapMatrix)

private theorem natural_cast_uniform_iff (x : MonoidAlgebra ℕ H) :
    RationalGroupAlgebraSplitting.Uniform (naturalToRational x) ↔ Uniform x := by
  constructor
  · intro hx g
    have hg := hx g
    simp only [naturalToRational, MonoidAlgebra.coeff_mapRingHom] at hg
    change (x.coeff g : ℚ) = (x.coeff 1 : ℚ) at hg
    exact Nat.cast_injective hg
  · intro hx g
    simp only [naturalToRational, MonoidAlgebra.coeff_mapRingHom]
    change (x.coeff g : ℚ) = (x.coeff 1 : ℚ)
    exact congrArg (fun a : ℕ => (a : ℚ)) (hx g)

/-- This is proved for every natural matrix from the actual rational equivalence;
it is not an additional hypothesis on powers or on the desired cutoff. -/
theorem uniform_iff_blocks_zero (W : RationalDecomposition H) (C : GroupMat H n n) :
    UniformMatrix C ↔ ∀ l, block W l C = 0 := by
  constructor
  · intro hC l
    ext ⟨i,a⟩ ⟨j,b⟩
    have hu := (natural_cast_uniform_iff (C i j)).mpr (hC i j)
    have hz := (RationalGroupAlgebraSplitting.uniform_iff_tail_zero
      W.equiv W.augmentation_first (naturalToRational (C i j))).mp hu
    change (W.equiv (naturalToRational (C i j))).2 l a b = 0
    exact congrArg (fun f : ∀ l, Matrix (Fin (W.order l)) (Fin (W.order l))
      (W.DivisionAlgebra l) => f l a b) hz
  · intro hC i j
    have hz : (W.equiv (naturalToRational (C i j))).2 = 0 := by
      funext l
      ext a b
      exact congrArg (fun M : Matrix (Fin n × Fin (W.order l)) (Fin n × Fin (W.order l))
        (W.DivisionAlgebra l) => M (i,a) (j,b)) (hC l)
    exact (natural_cast_uniform_iff (C i j)).mp
      ((RationalGroupAlgebraSplitting.uniform_iff_tail_zero
        W.equiv W.augmentation_first (naturalToRational (C i j))).mpr hz)

private theorem uniform_at_cutoff (W : RationalDecomposition H)
    (A : GroupMat H n n) (hA : Uniformizes A) : UniformMatrix (A^(n*bH W)) := by
  classical
  obtain ⟨N,hNpos,hN⟩ := hA
  apply (uniform_iff_blocks_zero W (A^(n*bH W))).mpr
  intro l
  have hnil : (block W l A)^N = 0 := by
    simpa only [map_pow] using (uniform_iff_blocks_zero W (A^N)).mp hN l
  have hsharp : (block W l A)^(n*W.order l) = 0 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      matrix_power_zero_at_card (block W l A) hnil
  simpa only [map_pow] using
    matrix_power_zero_mono (block W l A) (Nat.mul_le_mul_left n (block_order_le W l)) hsharp

/-- Least POSITIVE uniformization time is bounded by n*b_H. -/
theorem tau_le_cutoff (W : RationalDecomposition H) (hn : 0 < n)
    (A : GroupMat H n n) (hA : Uniformizes A) : tau A ≤ (n*bH W : WithTop ℕ) :=
  (tau_le_iff_uniform_power A (n*bH W)).mpr
    ⟨cutoff_positive W hn,uniform_at_cutoff W A hA⟩

private theorem augmentation_cast (x : MonoidAlgebra ℕ H) :
    RationalGroupAlgebraSplitting.augmentation (naturalToRational x) =
      (augmentation x : ℚ) := by
  simp [RationalGroupAlgebraSplitting.augmentation_eq_sum, augmentation_eq_sum,
    naturalToRational, MonoidAlgebra.coeff_mapRingHom]

/-- The normalized rational expression is derived from natural uniformity,
without dividing any natural coefficient. -/
theorem uniform_rational_expression (C : GroupMat H n n) (hC : UniformMatrix C) :
    rationalMatrix C = fun i j => (matrixAugmentation C i j : ℚ) •
      RationalGroupAlgebraSplitting.average H := by
  apply Matrix.ext
  intro i j
  have hx := RationalGroupAlgebraSplitting.uniform_eq_augmentation_smul_average
    (naturalToRational (C i j)) ((natural_cast_uniform_iff (C i j)).mpr (hC i j))
  change naturalToRational (C i j) = (augmentation (C i j) : ℚ) •
    RationalGroupAlgebraSplitting.average H
  simpa only [augmentation_cast] using hx

end D5.S3.FiniteGroups.RationalGroupMatrixCutoff
