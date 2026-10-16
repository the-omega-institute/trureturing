/- GID: D5/S3/Arith/Lattices/CofactorKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/CofactorKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive integer kernels determine minimal zero-sum multiplicities. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none; mathematical owners are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17570.
Escape audit unfinished for the public kernel_cross_identity interface:
https://github.com/the-omega-institute/trureturing/issues/17856.
Its whole-commutative-ring-family observation and source binding remain missing.
The box and total are literal expressions; sequence length uses Finsupp.degree in proofs.
The public length set retains the specified sum expression.
IsMinimalZeroSum: proof_shape: bind-only; escape_witness: none; consumers: lengths, lengths_upper_bound, primitive_cofactor_admissible, sequence_cofactor_length, lengths_nonempty, fromWeights_minimal_to_vector, lengths_finite, sequence_cofactor_multiplicities, finite_minimal_on_finset.
lengths: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, lengths_bddAbove, lengths_nonempty, result, D_lower_eventually_of_simplex, lengths_finite, D, D_upper_bound, claim, exists_asymptotic_lower_family.
augment: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, augmented_det_cube_vertex, augment_map, sum_cofactor_eq_det, primitive_cofactor_admissible, _proof_1_4, exists_maximizing_sign_simplex, cofactor_mulVec_eq_zero, sequence_cofactor_length, kernel_pair_cross, augmented_det_ne_zero_of_oriented_cofactors, standardSimplex_det, D_lower_eventually_of_simplex, _proof_1_3, _proof_1_1, kernel_det_ne_zero_of_positive, cofactor_mul_right_cross, augment_succ, interiorSimplex_positive_kernel, augmented_det_integer_box_bound, D_lower_eventually, interiorSimplex_nonsingular, augmented_det_affine, det_flipColumn, primitive_kernel_nonneg_span, det_topRow, sequence_cofactor_multiplicities, _simp_1_1, topRow_mul, columns_injective_of_augmented_det, delta_pos, cofactor_length_identity, augment_affine_eq, normalized_pencil_det_limit, continuous_augmented_det, kernel_cross_identity, delta, positive_kernel_orientation, _proof_1_2, _simp_1_1, augmented_det_box_bound, primitive_kernel_span, augment_zero, augmented_det_smul, det_replace_column_e0, augmented_det_ne_zero_of_full_rank_positive, exists_asymptotic_lower_family, _proof_1_2, cofactor_eq_adjugate, augmented_det_unit_bound, augment_update_flat, _proof_1_1, fromWeights_minimal_of_primitive, transpose_injective_of_augmented_det.
augment_zero: proof_shape: bind-only; escape_witness: none; consumers: augment_map, sum_cofactor_eq_det, standardSimplex_det, det_flipColumn, augment_affine_eq, kernel_cross_identity, augmented_det_smul, augmented_det_ne_zero_of_full_rank_positive, augment_update_flat.
augment_succ: proof_shape: bind-only; escape_witness: none; consumers: augment_map, sum_cofactor_eq_det, cofactor_mulVec_eq_zero, standardSimplex_det, det_flipColumn, det_topRow, topRow_mul, augment_affine_eq, kernel_cross_identity, augmented_det_smul, augmented_det_ne_zero_of_full_rank_positive, augment_update_flat.
cofactor: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, sum_cofactor_eq_det, primitive_cofactor_admissible, exists_maximizing_sign_simplex, cofactor_mulVec_eq_zero, sequence_cofactor_length, primitive_pencil_perturbation, cofactor_gcd_one_mul_right, cofactor_map, kernel_pair_cross, augmented_det_ne_zero_of_oriented_cofactors, _proof_1_3, kernel_det_ne_zero_of_positive, cofactor_mul_right_cross, interiorSimplex_positive_kernel, D_lower_eventually, cofactor_mul_left, det_flipColumn, det_topRow, sequence_cofactor_multiplicities, _simp_1_1, cofactor_length_identity, kernel_cross_identity, smith_staircase_gcd, cofactor_gcd_one_mul_left, positive_kernel_orientation, _proof_1_2, cofactor_smul, _simp_1_1, det_replace_column_e0, continuous_cofactor, exists_asymptotic_lower_family, normalized_pencil_cofactor_limit, cofactor_eq_adjugate, _proof_1_1.
cofactor_eq_adjugate: proof_shape: bind-only; escape_witness: none; consumers: _simp_1_1, _simp_1_1, det_replace_column_e0.
cofactor_mulVec_eq_zero: proof_shape: bind-only; escape_witness: none; consumers: primitive_cofactor_admissible, interiorSimplex_positive_kernel, cofactor_length_identity.
sum_cofactor_eq_det: proof_shape: bind-only; escape_witness: none; consumers: sequence_cofactor_length, augmented_det_ne_zero_of_oriented_cofactors, interiorSimplex_positive_kernel, cofactor_length_identity.
kernel_cross_identity: proof_shape: bind-only; escape_witness: none; consumers: kernel_pair_cross, kernel_det_ne_zero_of_positive, sequence_cofactor_multiplicities, positive_kernel_orientation, D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor.circuit_cofactor_complete.
kernel_pair_cross: proof_shape: bind-only; escape_witness: none; consumers: primitive_kernel_span.
primitive_kernel_span: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: primitive_kernel_nonneg_span, cofactor_length_identity.
primitive_kernel_nonneg_span: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: fromWeights_minimal_of_primitive.
kernel_det_ne_zero_of_positive: proof_shape: bind-only; escape_witness: none; consumers: cofactor_length_identity.
minimal_nonneg_kernel_gcd_one: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.minimal_nonneg_kernel_gcd_one; consumers: cofactor_length_identity.
cofactor_length_identity: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: sequence_cofactor_length.
fromWeights: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, primitive_cofactor_admissible, sequence_cofactor_length, length_fromWeights, fromWeights_minimal_to_vector, fromWeights_support_subset, sequence_cofactor_multiplicities, fromWeights_support_card, total_fromWeights, total_fromWeights_eq_mulVec, fromWeights_restrict, _proof_1_1, fromWeights_minimal_of_primitive.
fromWeights_apply: proof_shape: bind-only; escape_witness: none; consumers: fromWeights_minimal_to_vector, fromWeights_support_card, fromWeights_restrict, fromWeights_minimal_of_primitive.
fromWeights_support_subset: proof_shape: bind-only; escape_witness: none; consumers: primitive_cofactor_admissible, fromWeights_support_card, fromWeights_minimal_of_primitive.
fromWeights_restrict: proof_shape: bind-only; escape_witness: none; consumers: supportEmbedding_reconstruct, fromWeights_minimal_of_primitive.
total_fromWeights: proof_shape: bind-only; escape_witness: none; consumers: total_fromWeights_eq_mulVec, fromWeights_minimal_of_primitive.
length_fromWeights: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, sequence_cofactor_length, sequence_cofactor_multiplicities.
fromWeights_mono: proof_shape: bind-only; escape_witness: none; consumers: fromWeights_minimal_to_vector.
fromWeights_minimal_of_primitive: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: primitive_cofactor_admissible.
total_fromWeights_eq_mulVec: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, sequence_cofactor_length, fromWeights_minimal_to_vector, sequence_cofactor_multiplicities.
fromWeights_minimal_to_vector: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, sequence_cofactor_length.
sequence_cofactor_length: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: lengths_upper_bound, sequence_cofactor_multiplicities.
sequence_cofactor_multiplicities: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.CofactorKernel.0.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span; consumers: primitive_cofactor_admissible.
positive_kernel_orientation: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
augmented_det_ne_zero_of_oriented_cofactors: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
det_topRow: proof_shape: bind-only; escape_witness: none; consumers: cofactor_mul_right_cross.
topRow_mul: proof_shape: bind-only; escape_witness: none; consumers: cofactor_mul_right_cross.
cofactor_mul_right_cross: proof_shape: bind-only; escape_witness: none; consumers: cofactor_gcd_one_mul_right.
cofactor_mul_left: proof_shape: bind-only; escape_witness: none; consumers: cofactor_gcd_one_mul_left.
normalized_gcd_eq_one_of_dvd_one: proof_shape: bind-only; escape_witness: none; consumers: cofactor_gcd_one_mul_right.
cofactor_gcd_one_mul_right: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation.
cofactor_gcd_one_mul_left: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation.
-/


import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
namespace D5.S3.Arith.Lattices.CofactorKernel







/-- A minimal zero-sum sequence: nonempty, zero-sum, and no nonempty proper subsequence sums to zero. -/
def IsMinimalZeroSum {d : ℕ} (f : (Fin d → ℤ) →₀ ℕ) : Prop :=
  f ≠ 0 ∧ (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) f = 0 ∧ ∀ g : (Fin d → ℤ) →₀ ℕ, g ≤ f → g ≠ 0 → g ≠ f → (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) g ≠ 0

/-- Lengths of the minimal zero-sum sequences over `⟦-m, m⟧^d` whose support has exactly `k` elements. -/
def lengths (d m k : ℕ) : Set ℕ :=
  {L | ∃ f : (Fin d → ℤ) →₀ ℕ, IsMinimalZeroSum f ∧ (↑f.support : Set (Fin d → ℤ)) ⊆ (fun d m => {v : Fin d → ℤ | ∀ i, |v i| ≤ (m : ℕ)}) d m ∧
    f.support.card = k ∧ (f.sum fun _ n => n) = L}






open scoped BigOperators
open Matrix

def augment {R : Type*} [One R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Fin.cases (fun _ => 1) M

@[simp] theorem augment_zero {R : Type*} [One R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) (j : Fin (d + 1)) : augment M 0 j = 1 := by
  rfl

@[simp] theorem augment_succ {R : Type*} [One R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) (i : Fin d) (j : Fin (d + 1)) :
    augment M i.succ j = M i j := by
  rfl

def cofactor {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) (j : Fin (d + 1)) : R :=
  (-1) ^ (j.val) * (M.submatrix id j.succAbove).det

theorem cofactor_eq_adjugate {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) (j : Fin (d + 1)) :
    cofactor M j = (augment M).adjugate j 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add]
  rfl

theorem cofactor_mulVec_eq_zero {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) : M *ᵥ cofactor M = 0 := by
  ext i
  have h := congrArg (fun X => X i.succ 0) (Matrix.mul_adjugate (augment M))
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, augment_succ,
    ← cofactor_eq_adjugate, Matrix.one_apply, Fin.succ_ne_zero] using h

theorem sum_cofactor_eq_det {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) : ∑ j, cofactor M j = (augment M).det := by
  simpa [cofactor, Matrix.submatrix, augment_zero, augment_succ] using
    (Matrix.det_succ_row_zero (augment M)).symm

theorem kernel_cross_identity {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d + 1)) R) (x : Fin (d + 1) → R)
    (hx : M *ᵥ x = 0) (i : Fin (d + 1)) :
    (augment M).det * x i = (∑ j, x j) * cofactor M i := by
  have he : augment M *ᵥ x = Pi.single 0 (∑ j, x j) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mulVec, dotProduct, augment_zero, augment_succ]
    · simpa [Matrix.mulVec, dotProduct, augment_zero, augment_succ] using congrFun hx j
  have h := congrArg (fun y => y i)
    (congrArg (fun A => A *ᵥ x) (Matrix.adjugate_mul (augment M)))
  rw [← Matrix.mulVec_mulVec, he] at h
  simpa [Matrix.mulVec_single, Matrix.smul_mulVec, ← cofactor_eq_adjugate,
    Matrix.col, mul_comm] using h.symm

open scoped BigOperators
open Matrix

private theorem kernel_pair_cross {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hdet : (augment M).det ≠ 0)
    (a x : Fin (d+1) → ℤ) (ha : M *ᵥ a = 0) (hx : M *ᵥ x = 0)
    (i : Fin (d+1)) : (∑ j, a j) * x i = (∑ j, x j) * a i := by
  apply mul_left_cancel₀ hdet
  calc
    (augment M).det * ((∑ j, a j) * x i) =
        (∑ j, a j) * ((augment M).det * x i) := by ring
    _ = (∑ j, a j) * ((∑ j, x j) * cofactor M i) := by
      rw [kernel_cross_identity M x hx i]
    _ = (∑ j, x j) * ((augment M).det * a i) := by
      rw [kernel_cross_identity M a ha i]
      ring
    _ = (augment M).det * ((∑ j, x j) * a i) := by ring

private theorem primitive_kernel_span {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hdet : (augment M).det ≠ 0)
    (a : Fin (d+1) → ℤ) (ha : M *ᵥ a = 0)
    (hsum : ∑ j, a j ≠ 0) (hgcd : Finset.univ.gcd a = 1)
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x = 0) :
    ∃ z : ℤ, ∀ i, x i = z * a i := by
  obtain ⟨b, hb⟩ := Finset.gcd_eq_sum_mul Finset.univ a
  rw [hgcd] at hb
  let z : ℤ := ∑ j, b j * x j
  have hz : (∑ j, a j) * z = ∑ j, x j := by
    calc
      (∑ j, a j) * z = ∑ i, b i * ((∑ j, a j) * x i) := by
        simp only [z, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, b i * ((∑ j, x j) * a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [kernel_pair_cross M hdet a x ha hx i]
      _ = (∑ j, x j) * (∑ i, a i * b i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ j, x j := by rw [← hb, mul_one]
  refine ⟨z, fun i => ?_⟩
  apply mul_left_cancel₀ hsum
  rw [kernel_pair_cross M hdet a x ha hx i, ← hz]
  ring

private theorem primitive_kernel_nonneg_span {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hdet : (augment M).det ≠ 0)
    (a : Fin (d+1) → ℤ) (ha : M *ᵥ a = 0)
    (hapos : ∀ i, 0 < a i) (hgcd : Finset.univ.gcd a = 1)
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x = 0) (hxpos : ∀ i, 0 ≤ x i) :
    ∃ z : ℕ, ∀ i, x i = z * a i := by
  have hsum : ∑ j, a j ≠ 0 := ne_of_gt (Finset.sum_pos (fun j _ => hapos j)
    Finset.univ_nonempty)
  obtain ⟨z, hz⟩ := primitive_kernel_span M hdet a ha hsum hgcd x hx
  have hzpos : 0 ≤ z := by
    have hp := hapos 0
    have hq := hxpos 0
    rw [hz 0] at hq
    exact nonneg_of_mul_nonneg_left hq hp
  refine ⟨z.toNat, fun i => ?_⟩
  simpa [Int.toNat_of_nonneg hzpos] using hz i


private theorem kernel_det_ne_zero_of_positive {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x = 0) (hpos : ∀ i, 0 < x i)
    (hcof : ∃ i, cofactor M i ≠ 0) : (augment M).det ≠ 0 := by
  obtain ⟨i, hi⟩ := hcof
  have hs : ∑ j, x j ≠ 0 := ne_of_gt (Finset.sum_pos (fun j _ => hpos j)
    Finset.univ_nonempty)
  intro hz
  have h := kernel_cross_identity M x hx i
  rw [hz, zero_mul] at h
  exact (mul_ne_zero hs hi) h.symm

private theorem minimal_nonneg_kernel_gcd_one {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x = 0) (hpos : ∀ i, 0 < x i)
    (hmin : ∀ y : Fin (d+1) → ℤ, (∀ i, 0 ≤ y i) → y ≤ x →
      y ≠ 0 → M *ᵥ y = 0 → y = x) : Finset.univ.gcd x = 1 := by
  obtain ⟨a, ha, hag⟩ := Finset.univ.extract_gcd x Finset.univ_nonempty
  have he (i) : x i = Finset.univ.gcd x * a i := ha i (Finset.mem_univ i)
  have hg : 0 < Finset.univ.gcd x := by
    have hn : Finset.univ.gcd x ≠ 0 := by
      intro hz
      have h := he 0
      rw [hz, zero_mul] at h
      exact (ne_of_gt (hpos 0)) h
    exact lt_of_le_of_ne Finset.Int.finsetGcd_nonneg (Ne.symm hn)
  have hap (i) : 0 ≤ a i := by
    have h := (hpos i).le
    rw [he i] at h
    exact nonneg_of_mul_nonneg_right h hg
  have hal : a ≤ x := by
    intro i
    rw [he i]
    have h1 : 1 ≤ Finset.univ.gcd x := hg
    nlinarith [hap i]
  have han : a ≠ 0 := by
    intro hz
    have h := he 0
    rw [hz, Pi.zero_apply, mul_zero] at h
    exact (ne_of_gt (hpos 0)) h
  have hak : M *ᵥ a = 0 := by
    ext i
    have h := congrFun hx i
    change ∑ j, M i j * x j = 0 at h
    simp_rw [he] at h
    have heq : (∑ j, M i j * (Finset.univ.gcd x * a j)) =
        Finset.univ.gcd x * (∑ j, M i j * a j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hg)
  have hae : a = x := hmin a hap hal han hak
  simpa [hae] using hag

private theorem cofactor_length_identity {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x = 0) (hpos : ∀ i, 0 < x i)
    (hcof : ∃ i, cofactor M i ≠ 0)
    (hmin : ∀ y : Fin (d+1) → ℤ, (∀ i, 0 ≤ y i) → y ≤ x →
      y ≠ 0 → M *ᵥ y = 0 → y = x) :
    |(augment M).det| = (∑ j, x j) * Finset.univ.gcd (cofactor M) := by
  have hdet := kernel_det_ne_zero_of_positive M x hx hpos hcof
  have hsum : 0 < ∑ j, x j := Finset.sum_pos (fun j _ => hpos j) Finset.univ_nonempty
  have hgcd := minimal_nonneg_kernel_gcd_one M x hx hpos hmin
  obtain ⟨z, hz⟩ := primitive_kernel_span M hdet x hx (ne_of_gt hsum) hgcd
    (cofactor M) (cofactor_mulVec_eq_zero M)
  have he : cofactor M = fun i => z * x i := funext hz
  have hg : Finset.univ.gcd (cofactor M) = |z| := by
    rw [he, Finset.gcd_mul_left, hgcd, mul_one]
    exact (Int.abs_eq_normalize z).symm
  rw [hg, ← sum_cofactor_eq_det, he, ← Finset.mul_sum, abs_mul,
    abs_of_pos hsum]
  ring

open scoped BigOperators
open Matrix

def fromWeights {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ)) (x : Fin k → ℕ) :
    (Fin d → ℤ) →₀ ℕ :=
  Finsupp.embDomain v (Finsupp.equivFunOnFinite.symm x)

theorem fromWeights_apply {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) (i : Fin k) : fromWeights v x (v i) = x i := by
  exact Finsupp.embDomain_apply_self v _ i

theorem fromWeights_support_subset {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) : (↑(fromWeights v x).support : Set (Fin d → ℤ)) ⊆ Set.range v := by
  classical
  intro w hw
  change w ∈ (Finsupp.embDomain v _).support at hw
  rw [Finsupp.support_embDomain] at hw
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hw
  exact ⟨j,rfl⟩

theorem fromWeights_restrict {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (f : (Fin d → ℤ) →₀ ℕ)
    (hf : (↑f.support : Set (Fin d → ℤ)) ⊆ Set.range v) :
    fromWeights v (fun i => f (v i)) = f := by
  classical
  ext w
  by_cases hw : w ∈ Set.range v
  · obtain ⟨j,rfl⟩ := hw
    exact fromWeights_apply v _ j
  · rw [show f w = 0 from Finsupp.notMem_support_iff.mp (fun h => hw (hf h))]
    exact Finsupp.embDomain_of_notMem_range v _ w hw

private theorem total_fromWeights {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) :
    (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) (fromWeights v x) = fun i => ∑ j, (x j : ℤ) * v j i := by
  dsimp only
  unfold fromWeights
  rw [Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  ext i
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem length_fromWeights {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) : (Finsupp.degree (R := ℕ)) (fromWeights v x) = ∑ j, x j := by
  change (fromWeights v x).sum (fun _ n => n) = _
  unfold fromWeights
  rw [Finsupp.sum_embDomain]
  exact Finsupp.equivFunOnFinite_symm_sum x

private theorem fromWeights_mono {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    {x y : Fin k → ℕ} (hxy : x ≤ y) : fromWeights v x ≤ fromWeights v y := by
  exact Finsupp.embDomain_mono v hxy




theorem fromWeights_minimal_of_primitive {d : ℕ}
    (v : Fin (d+1) ↪ (Fin d → ℤ))
    (hdet : (augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det ≠ 0)
    (x : Fin (d+1) → ℤ) (hx : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ x = 0)
    (hpos : ∀ i, 0 < x i) (hgcd : Finset.univ.gcd x = 1) :
    IsMinimalZeroSum (fromWeights v (fun i => (x i).toNat)) := by
  classical
  have hecast (i) : ((x i).toNat : ℤ) = x i := Int.toNat_of_nonneg (hpos i).le
  have htotal : (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) (fromWeights v (fun i => (x i).toNat)) = (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ x := by
    ext i
    rw [total_fromWeights]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose, Matrix.of_apply, hecast]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  refine ⟨?_, htotal.trans hx, ?_⟩
  · intro hz
    have hz' := DFunLike.congr_fun hz (v 0)
    rw [fromWeights_apply] at hz'
    have h := hecast 0
    simp only [Finsupp.zero_apply] at hz'
    rw [hz', Int.natCast_zero] at h
    exact (ne_of_gt (hpos 0)) h.symm
  · intro g hgf hgn hgne hgz
    have hgs : (↑g.support : Set (Fin d → ℤ)) ⊆ Set.range v := by
      intro w hw
      exact fromWeights_support_subset v _ ((Finsupp.support_mono hgf) hw)
    have hgr := fromWeights_restrict v g hgs
    let y : Fin (d+1) → ℤ := fun j => g (v j)
    have hy : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ y = 0 := by
      rw [← hgr, total_fromWeights] at hgz
      ext i
      have h := congrFun hgz i
      simpa [Matrix.transpose, Matrix.mulVec, dotProduct, y, mul_comm] using h
    obtain ⟨z,hz⟩ := primitive_kernel_nonneg_span ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) hdet x hx hpos hgcd y hy
      (fun i => Int.natCast_nonneg _)
    have hzle : z ≤ 1 := by
      have hle := hgf (v 0)
      rw [fromWeights_apply] at hle
      have hle' : (g (v 0) : ℤ) ≤ x 0 := by
        rw [← hecast 0]
        exact_mod_cast hle
      have h := hz 0
      change (g (v 0) : ℤ) = (z : ℤ) * x 0 at h
      have hzi : (z : ℤ) ≤ 1 := by nlinarith [hpos 0]
      exact_mod_cast hzi
    have hzne : z ≠ 0 := by
      intro hz0
      apply hgn
      ext w
      by_cases hw : w ∈ Set.range v
      · obtain ⟨j,rfl⟩ := hw
        have h := hz j
        simp only [hz0, Nat.cast_zero, zero_mul, y] at h
        exact_mod_cast h
      · exact Finsupp.notMem_support_iff.mp (fun h => hw (hgs h))
    have hz1 : z = 1 := by omega
    apply hgne
    rw [← hgr]
    apply congrArg (fromWeights v)
    funext i
    apply Int.ofNat_inj.mp
    rw [hecast]
    simpa [y, hz1] using hz i


theorem total_fromWeights_eq_mulVec {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) : (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) (fromWeights v x) = (Matrix.of (v : Fin k → Fin d → ℤ)).transpose *ᵥ (fun j => (x j : ℤ)) := by
  rw [total_fromWeights]
  ext i
  simp [Matrix.transpose, Matrix.mulVec, dotProduct, mul_comm]

theorem fromWeights_minimal_to_vector {d k : ℕ} (v : Fin k ↪ (Fin d → ℤ))
    (x : Fin k → ℕ) (hmin : IsMinimalZeroSum (fromWeights v x))
    (y : Fin k → ℕ) (hy : y ≤ x) (hyker : (Matrix.of (v : Fin k → Fin d → ℤ)).transpose *ᵥ (fun j => (y j : ℤ)) = 0) :
    y = 0 ∨ y = x := by
  classical
  by_cases hy0 : y=0
  · exact Or.inl hy0
  by_cases hyx : y=x
  · exact Or.inr hyx
  exfalso
  have hgn : fromWeights v y ≠ 0 := by
    intro h
    apply hy0
    funext i
    simpa only [fromWeights_apply, Finsupp.zero_apply, Pi.zero_apply] using DFunLike.congr_fun h (v i)
  have hgne : fromWeights v y ≠ fromWeights v x := by
    intro h
    apply hyx
    funext i
    simpa only [fromWeights_apply] using DFunLike.congr_fun h (v i)
  exact hmin.2.2 _ (fromWeights_mono v hy) hgn hgne
    ((total_fromWeights_eq_mulVec v y).trans hyker)

theorem sequence_cofactor_length {d : ℕ} (v : Fin (d+1) ↪ (Fin d → ℤ))
    (x : Fin (d+1) → ℕ) (hpos : ∀ i, 0 < x i)
    (hmin : IsMinimalZeroSum (fromWeights v x))
    (hdet : (augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det ≠ 0) :
    |(augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det| =
      ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ) * Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)) := by
  classical
  have hx : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ (fun i => (x i : ℤ)) = 0 := by
    rw [← total_fromWeights_eq_mulVec]
    exact hmin.2.1
  have hcof : ∃ i, cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) i ≠ 0 := by
    by_contra hn
    have hz (i) : cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) i = 0 := by
      by_contra hi
      exact hn ⟨i,hi⟩
    apply hdet
    rw [← sum_cofactor_eq_det]
    simp only [hz, Finset.sum_const_zero]
  have hminimal : ∀ y : Fin (d+1) → ℤ, (∀ i, 0 ≤ y i) → y ≤ (fun i => (x i : ℤ)) →
      y ≠ 0 → (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ y=0 → y=(fun i => (x i : ℤ)) := by
    intro y hyp hyl hyn hyk
    let yn : Fin (d+1) → ℕ := fun i => (y i).toNat
    have hycast : (fun i => (yn i : ℤ))=y := funext (fun i => Int.toNat_of_nonneg (hyp i))
    have hynle : yn ≤ x := by
      intro i
      exact_mod_cast (show (yn i : ℤ) ≤ (x i : ℤ) by rw [congrFun hycast i]; exact hyl i)
    have hync : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ (fun i => (yn i : ℤ))=0 := by rw [hycast]; exact hyk
    rcases fromWeights_minimal_to_vector v x hmin yn hynle hync with hy0 | hyx
    · apply False.elim
      apply hyn
      rw [← hycast, hy0]
      rfl
    · rw [← hycast, hyx]
  have h := cofactor_length_identity ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) (fun i => (x i : ℤ)) hx
    (fun i => by exact_mod_cast hpos i) hcof hminimal
  rw [length_fromWeights]
  simpa only [Nat.cast_sum] using h

open scoped BigOperators
open Matrix

theorem sequence_cofactor_multiplicities {d : ℕ}
    (v : Fin (d+1) ↪ (Fin d → ℤ)) (x : Fin (d+1) → ℕ)
    (hp : ∀ i,0<x i) (hmin : IsMinimalZeroSum (fromWeights v x))
    (hdet : (augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det≠0) :
    (∀ i,(x i : ℤ)=|cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) i|/
      Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose))) ∧
    ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ)=|(augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det|/
      Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)) := by
  classical
  have hid := sequence_cofactor_length v x hp hmin hdet
  have hL : (0 : ℤ)<(Finsupp.degree (R := ℕ)) (fromWeights v x) := by
    rw [length_fromWeights]
    exact_mod_cast (Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty)
  have hgd : Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose))≠0 := by
    intro hz
    rw [hz,mul_zero] at hid
    exact hdet (abs_eq_zero.mp hid)
  have hx : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ (fun j => (x j : ℤ))=0 := by
    rw [← total_fromWeights_eq_mulVec]
    exact hmin.2.1
  have hlen : (∑ j,(x j : ℤ))=((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ) := by
    rw [length_fromWeights,Nat.cast_sum]
  constructor
  · intro i
    have hc := kernel_cross_identity ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) (fun j => (x j : ℤ)) hx i
    have hca := congrArg abs hc
    simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at hca
    rw [hlen,abs_of_pos hL,hid] at hca
    have he : |cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) i|=
        (x i : ℤ)*Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)) := by
      apply (mul_left_cancel₀ (ne_of_gt hL))
      calc
        ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ)*|cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) i| =
            ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ)*Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose))*(x i : ℤ) := hca.symm
        _ = ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ)*((x i : ℤ)*Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose))) := by ring
    rw [he,mul_comm (x i : ℤ),Int.mul_ediv_cancel_left _ hgd]
  · rw [hid,mul_comm ((Finsupp.degree (R := ℕ)) (fromWeights v x) : ℤ),Int.mul_ediv_cancel_left _ hgd]

open scoped BigOperators
open Matrix

theorem positive_kernel_orientation {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) ℤ) (hdet : (augment A).det≠0)
    (x : Fin (d+1) → ℤ) (hp : ∀ j,0<x j) (hx : A *ᵥ x=0) :
    ∃ s : ℤ,(s=1 ∨ s= -1) ∧ ∀ j,0<s*cofactor A j := by
  have hS : 0<∑ j,x j := Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · refine ⟨-1,Or.inr rfl,fun j => ?_⟩
    have he := kernel_cross_identity A x hx j
    have hh : (∑ j,x j)*cofactor A j<0 := by rw [← he]; exact mul_neg_of_neg_of_pos hneg (hp j)
    have hc : cofactor A j<0 := neg_of_mul_neg_right hh hS.le
    simpa using neg_pos.mpr hc
  · refine ⟨1,Or.inl rfl,fun j => ?_⟩
    have he := kernel_cross_identity A x hx j
    have hh : 0<(∑ j,x j)*cofactor A j := by rw [← he]; exact mul_pos hpos (hp j)
    simpa using pos_of_mul_pos_right hh hS.le

theorem augmented_det_ne_zero_of_oriented_cofactors {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) ℤ) (s : ℤ)
    (hp : ∀ j,0<s*cofactor A j) : (augment A).det≠0 := by
  have hs : 0<s*(augment A).det := by
    rw [← sum_cofactor_eq_det,Finset.mul_sum]
    exact Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
  intro hz
  rw [hz,mul_zero] at hs
  exact lt_irrefl _ hs

open scoped BigOperators
open Matrix

private theorem det_topRow {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R) (a : Fin (d+1) → R) :
    ((augment M).updateRow 0 a).det = ∑ j, a j * cofactor M j := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.updateRow_self]
  have he : ((augment M).updateRow 0 a).submatrix Fin.succ j.succAbove =
      M.submatrix id j.succAbove := by
    ext i k
    simp only [Matrix.submatrix_apply, Matrix.updateRow_ne (Fin.succ_ne_zero i), augment_succ, id_eq]
  rw [he]
  simp only [cofactor]
  ring

private theorem topRow_mul {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R)
    (W : Matrix (Fin (d+1)) (Fin (d+1)) R) (a : Fin (d+1) → R) :
    (augment (M * W)).updateRow 0 (a ᵥ* W) = (augment M).updateRow 0 a * W := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Matrix.updateRow_self, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · simp only [Matrix.updateRow_ne (Fin.succ_ne_zero i), augment_succ, Matrix.mul_apply]

private theorem cofactor_mul_right_cross {R : Type*} [CommRing R] {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) R)
    (W : Matrix (Fin (d+1)) (Fin (d+1)) R) :
    W *ᵥ cofactor (M * W) = W.det • cofactor M := by
  ext i
  have he := congrArg Matrix.det (topRow_mul M W (Pi.single i 1))
  rw [Matrix.det_mul, det_topRow, det_topRow] at he
  simpa [Matrix.vecMul, Matrix.row, Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_ite_eq, smul_eq_mul, mul_comm] using he

private theorem cofactor_mul_left {R : Type*} [CommRing R] {d : ℕ}
    (U : Matrix (Fin d) (Fin d) R) (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    cofactor (U * M) j = U.det * cofactor M j := by
  have he : (U * M).submatrix id j.succAbove = U * M.submatrix id j.succAbove := by
    ext i k
    rfl
  rw [cofactor, he, Matrix.det_mul, cofactor]
  ring

private theorem normalized_gcd_eq_one_of_dvd_one {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : s.gcd f ∣ 1) : s.gcd f = 1 := by
  have he := normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr h)
  simpa only [Finset.normalize_gcd] using he

theorem cofactor_gcd_one_mul_right {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (W : Matrix (Fin (d+1)) (Fin (d+1)) ℤ)
    (hW : IsUnit W.det) (hM : Finset.univ.gcd (cofactor M) = 1) :
    Finset.univ.gcd (cofactor (M * W)) = 1 := by
  apply normalized_gcd_eq_one_of_dvd_one
  rw [← hM, Finset.dvd_gcd_iff]
  intro i hi
  apply hW.dvd_mul_left.mp
  have he := congrFun (cofactor_mul_right_cross M W) i
  change (W *ᵥ cofactor (M * W)) i = W.det * cofactor M i at he
  rw [← he]
  change Finset.univ.gcd (cofactor (M * W)) ∣ ∑ j, W i j * cofactor (M * W) j
  exact Finset.dvd_sum (fun j hj => dvd_mul_of_dvd_right (Finset.gcd_dvd hj) _)

theorem cofactor_gcd_one_mul_left {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℤ) (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hU : IsUnit U.det) (hM : Finset.univ.gcd (cofactor M) = 1) :
    Finset.univ.gcd (cofactor (U * M)) = 1 := by
  have he : cofactor (U * M) = fun j => U.det * cofactor M j := funext (cofactor_mul_left U M)
  rw [he, Finset.gcd_mul_left, hM, mul_one]
  exact normalize_eq_one.mpr hU

end D5.S3.Arith.Lattices.CofactorKernel
