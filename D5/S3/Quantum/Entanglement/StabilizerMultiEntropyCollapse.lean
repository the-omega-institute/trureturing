/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The n = 3 genuine four-party multi-entropy collapse for pure qubit stabilizer states. -/

/-
Per-declaration judgement:
  shift: proof_shape: bind-only; escape_witness: none.
    consumer: Z, Z_local_unitary_phase, Z_one, Z_smul, graph_replica_form, shiftEquiv, shift_delta.
    admission_basis: open-problem-resolution (#13575; Proved).
  Z: proof_shape: bind-only; escape_witness: none.
    consumer: S, Z_local_scalar, Z_local_unitary_phase, Z_one, Z_smul, claim, entropy_formula,
      entropy_partition, graph_count, graph_replica_form, graph_scalar_norm, result,
      stabilizer_replica_count, stabilizer_replica_positive.
    admission_basis: open-problem-resolution (#13575; Proved).
  replicaOp: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase, replicaOp_permutation, replica_expand, replica_unitary.
    admission_basis: open-problem-resolution (#13575; Proved).
  replica_expand: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase.
    admission_basis: open-problem-resolution (#13575; Proved).
  replica_unitary: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase.
    admission_basis: open-problem-resolution (#13575; Proved).
  shiftEquiv: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase.
    admission_basis: open-problem-resolution (#13575; Proved).
  replicaPermutation: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase, replicaOp_permutation.
    admission_basis: open-problem-resolution (#13575; Proved).
  replicaOp_permutation: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_unitary_phase.
    admission_basis: open-problem-resolution (#13575; Proved).
  Z_local_unitary_phase: proof_shape: bind-only; escape_witness: none.
    consumer: Z_local_scalar.
    admission_basis: open-problem-resolution (#13575; Proved).
  delta: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_formula, entropy_partition, graph_count, graph_replica_form, rank_partition,
      result, shift_delta, stabilizer_replica_count, stabilizer_replica_positive.
    admission_basis: open-problem-resolution (#13575; Proved).
  shift_delta: proof_shape: bind-only; escape_witness: none.
    consumer: graph_replica_form.
    admission_basis: open-problem-resolution (#13575; Proved).
  bilinear_sum: proof_shape: bind-only; escape_witness: none.
    consumer: quadratic_sum.
    admission_basis: open-problem-resolution (#13575; Proved).
  Z_smul: proof_shape: bind-only; escape_witness: none.
    consumer: graph_scalar_norm, stabilizer_replica_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  graph_replica_form: proof_shape: bind-only; escape_witness: none.
    consumer: graph_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  quadratic_sum: proof_shape: bind-only; escape_witness: none.
    consumer: graph_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  Z_one: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_formula, graph_scalar_norm.
    admission_basis: open-problem-resolution (#13575; Proved).
  graph_norm: proof_shape: bind-only; escape_witness: none.
    consumer: graph_scalar_norm.
    admission_basis: open-problem-resolution (#13575; Proved).
  Z_local_scalar: proof_shape: bind-only; escape_witness: none.
    consumer: graph_scalar_norm, stabilizer_replica_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  graph_scalar_norm: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_replica_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  graph_count: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_replica_count.
    admission_basis: open-problem-resolution (#13575; Proved).
  representatives_exist: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_replica_positive.
    admission_basis: open-problem-resolution (#13575; Proved).
  stabilizer_replica_count: proof_shape: bind-only; escape_witness: none.
    consumer: result, stabilizer_replica_positive.
    admission_basis: open-problem-resolution (#13575; Proved).
  stabilizer_replica_positive: proof_shape: bind-only; escape_witness: none.
    consumer: result.
    admission_basis: open-problem-resolution (#13575; Proved).
  S: proof_shape: bind-only; escape_witness: none.
    consumer: GM4, I3, entropy_formula, entropy_partition, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  I3: proof_shape: bind-only; escape_witness: none.
    consumer: GM4, claim, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  GM4: proof_shape: bind-only; escape_witness: none.
    consumer: claim, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  claim: proof_shape: bind-only; escape_witness: none.
    consumer: result.
    admission_basis: open-problem-resolution (#13575; Proved).
  cutPattern: proof_shape: bind-only; escape_witness: none.
    consumer: cutPattern_apply, entropy_partition, partitionSum, partition_count, rank_partition.
    admission_basis: open-problem-resolution (#13575; Proved).
  cutPattern_apply: proof_shape: bind-only; escape_witness: none.
    consumer: rank_partition.
    admission_basis: open-problem-resolution (#13575; Proved).
  colourValue: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_partition, partitionSum, partition_count, rank_partition.
    admission_basis: open-problem-resolution (#13575; Proved).
  modes1: proof_shape: bind-only; escape_witness: none.
    consumer: partition_count, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  modes2: proof_shape: bind-only; escape_witness: none.
    consumer: partition_count, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  modes3: proof_shape: bind-only; escape_witness: none.
    consumer: partition_count, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  partitionSum: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_partition, partition_count, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  partition_count: proof_shape: content (after helper expansion);
    escape_witness: arbitrary-label merger_sum_transport through ternary partition classification.
    consumer: result.
    admission_basis: open-problem-resolution (#13575; Proved).
  partitionRank: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_partition, rank_partition, result.
    admission_basis: open-problem-resolution (#13575; Proved).
  rank_partition: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_partition.
    admission_basis: open-problem-resolution (#13575; Proved).
  entropy_formula: proof_shape: bind-only; escape_witness: none.
    consumer: entropy_partition.
    admission_basis: open-problem-resolution (#13575; Proved).
  entropy_partition: proof_shape: bind-only; escape_witness: none.
    consumer: result.
    admission_basis: open-problem-resolution (#13575; Proved).
  result: proof_shape: content (after helper expansion);
    escape_witness: structural partition_count on the live entropy-partition path.
    consumer: none (terminal settlement).
    admission_basis: open-problem-resolution (#13575; Proved).
Structural helper judgement (all are consumed on the existing result path):
  partition: proof_shape: bind-only; consumer: partition_eq_iff, representative_injOn.
  partition_eq_iff: proof_shape: bind-only; consumer: representative_injOn, pulled_partition_mem_image.
  representative_injOn: proof_shape: content (after helper expansion); consumer: representative_sum, pulled_representative_injOn.
  representative_sum: proof_shape: content (after helper expansion); consumer: full_sum_upperSum.
  four_party_partition_ne_bot: proof_shape: bind-only; consumer: partitionSupport_ne_bot.
  nonzero_partition_ne_top: proof_shape: bind-only; consumer: partitionSupport_ne_top.
  factor_through_merger: proof_shape: bind-only; consumer: compatible_partition_has_representative.
  compatible_partition_has_representative: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  pullPartition: proof_shape: bind-only; consumer: pulled_representative_injOn, pulled_partition_mem_image.
  pulled_representative_injOn: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  pulled_partition_mem_image: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  merger_sum_transport: proof_shape: content (after helper expansion); consumer: merger_sum_upperSum.
  relation: proof_shape: bind-only; consumer: Valid, FourPartition.
  Valid: proof_shape: bind-only; consumer: FourPartition.
  FourPartition: proof_shape: bind-only; consumer: discrete, indiscrete.
  discrete: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  indiscrete: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  edgeCount: proof_shape: bind-only; consumer: coefficient, coefficient_cancel.
  coefficient: proof_shape: bind-only; consumer: catalogue_coefficient, coefficient_cancel.
  toSetoid: proof_shape: bind-only; consumer: to_from, from_to.
  code: proof_shape: bind-only; consumer: relation_code, fromSetoid.
  relation_code: proof_shape: bind-only; consumer: fromSetoid, to_from.
  fromSetoid: proof_shape: bind-only; consumer: to_from, from_to.
  to_from: proof_shape: bind-only; consumer: fromSetoid_le_iff.
  from_to: proof_shape: bind-only; consumer: encodePartition_surjective.
  toSetoid_le_iff: proof_shape: bind-only; consumer: fromSetoid_le_iff.
  fromSetoid_le_iff: proof_shape: bind-only; consumer: encodePartition_le_iff.
  catalogue: proof_shape: bind-only; consumer: catalogue_bijective, pairPartition.
  catalogue_bijective: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  pairPartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  triplePartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  doublePartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  catalogue_coefficient: proof_shape: bind-only; consumer: weighted_sum_expansion.
  coefficient_cancel: proof_shape: bind-only; consumer: weighted_upper_sum_cancel.
  weighted_sum_expansion: proof_shape: bind-only; consumer: four_party_counting_identity.
  upperSum: proof_shape: bind-only; consumer: weighted_upper_sum_cancel, four_party_counting_identity.
  weighted_upper_sum_cancel: proof_shape: bind-only; consumer: four_party_counting_identity.
  four_party_counting_identity: proof_shape: bind-only; consumer: structural_partition_count.
  anchorEquiv: proof_shape: bind-only; consumer: colourValue2, colourValue3.
  colourValue2: proof_shape: bind-only; consumer: structural_partition_count.
  colourValue3: proof_shape: bind-only; consumer: structural_partition_count.
  colourValue4: proof_shape: bind-only; consumer: partitionSum_full_upperSum.
  mergeMap: proof_shape: bind-only; consumer: mergeMap_surjective, encoded_merger_kernel.
  mergeMap_surjective: proof_shape: bind-only; consumer: merger_sum_upperSum.
  pairMergers: proof_shape: bind-only; consumer: pairMergers_surjective, pairMergers_partition.
  singletonCuts: proof_shape: bind-only; consumer: singletonCuts_surjective, singletonCuts_partition.
  balancedCuts: proof_shape: bind-only; consumer: balancedCuts_surjective, balancedCuts_partition.
  pairMergers_surjective: proof_shape: bind-only; consumer: structural_partition_count.
  singletonCuts_surjective: proof_shape: bind-only; consumer: structural_partition_count.
  balancedCuts_surjective: proof_shape: bind-only; consumer: structural_partition_count.
  encodePartition: proof_shape: bind-only; consumer: encodePartition_le_iff, encodePartition_injective.
  encodePartition_le_iff: proof_shape: bind-only; consumer: encodePartition_injective, encodePartition_bot.
  encodePartition_injective: proof_shape: bind-only; consumer: partitionSupport_ne_bot, partitionSupport_ne_top.
  encodePartition_surjective: proof_shape: bind-only; consumer: encodePartition_bot, encodePartition_top.
  encodePartition_bot: proof_shape: bind-only; consumer: partitionSupport_ne_bot, full_sum_upperSum.
  encodePartition_top: proof_shape: bind-only; consumer: partitionSupport_ne_top.
  partitionSupport: proof_shape: bind-only; consumer: partitionSupport_ne_bot, partitionSupport_ne_top.
  partitionSupport_ne_bot: proof_shape: bind-only; consumer: structural_partition_count.
  partitionSupport_ne_top: proof_shape: bind-only; consumer: structural_partition_count.
  encoded_upperSum: proof_shape: bind-only; consumer: merger_sum_upperSum, full_sum_upperSum.
  encoded_merger_kernel: proof_shape: bind-only; consumer: merger_sum_upperSum.
  merger_sum_upperSum: proof_shape: content (after helper expansion); consumer: partitionSum_as_upperSum.
  full_sum_upperSum: proof_shape: content (after helper expansion); consumer: partitionSum_full_upperSum.
  separation: proof_shape: bind-only; consumer: separation_encoded, partitionSum_as_upperSum.
  separation_encoded: proof_shape: bind-only; consumer: partitionSum_as_upperSum, partitionSum_full_upperSum.
  pairMergers_partition: proof_shape: bind-only; consumer: structural_partition_count.
  singletonCuts_partition: proof_shape: bind-only; consumer: structural_partition_count.
  balancedCuts_partition: proof_shape: bind-only; consumer: structural_partition_count.
  partitionSumR: proof_shape: bind-only; consumer: partitionSum_as_upperSum, partitionSum_full_upperSum.
  partitionSum_as_upperSum: proof_shape: content (after helper expansion); consumer: structural_partition_count.
  partitionSum_full_upperSum: proof_shape: content (after helper expansion); consumer: structural_partition_count.
  structural_partition_count: proof_shape: content (after helper expansion); consumer: partition_count.
  The content entries use the same-delivery arbitrary-index ternary partition
  classification on their live path; the remaining entries only organize,
  encode, or normalize that transport and the finite four-party coefficients.
  The local decidability, order and interval instances supply the catalogue
  and interval-sum proofs; they introduce no independent mathematical claim.
Utility: none. The delivered inference is a structural transport for arbitrary
index types, representative families, surjective mergers, and real weights.
The private catalogue_bijective, catalogue_coefficient and coefficient_cancel
lemmas are finite normalization auxiliaries: their actual consumers are,
respectively, coefficient_cancel/weighted_sum_expansion, weighted_sum_expansion,
and weighted_upper_sum_cancel, all on the live partition_count proof path.
They do not assert a general Mobius formula or constitute a delivered independent
finite-instance certificate, checker, or numerical reduction.
Same-delivery structural dependency (not an already frozen premise):
  D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.result.
Direct frozen dependencies:
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.F₂
    statement_id: sha256:e975fc48104d0cb1a40271fdfb5ec7fcfe2730a1c600ee81758d5e89253bd60f
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign.eq_1
    statement_id: sha256:47b1c4360f7294d639daaa81a4dc00aa903f52ef7b53aeca8f2a321008db2233
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_sum
    statement_id: sha256:cca15d93bbe8896cad48b7dfd75c8053ab080db717fab32f9ace58b5aaeec0b9
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign_add
    statement_id: sha256:9299cfc42d5d0ba183be190abb0eaa8f7ca19b25a002ecd815057449aad3e7ad
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign
    statement_id: sha256:815b3b55d18bbe94631f98e608ed75835a5ed6590c5cb4a958805cade90cb93d
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.normalExponent
    statement_id: sha256:582b0f2439e696a8856cf0d2c7099efbee950ed3b8702546f84c5b45cc7598f4
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.StabilizedBy
    statement_id: sha256:84981833e6a3c38263d5476f28eb063fbdd1f76f4349d22a4bb67f3cb128d344
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.pauliSet
    statement_id: sha256:856f9c10bdadcb60566b2de31e839e712c75cb4be32af461b413c9fdc95a1014
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.tensorOp
    statement_id: sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
-/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm

import D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Decide

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse

open Matrix
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient


/-- Translation in the coordinate assigned to `c`; the last party acts as the identity. -/
def shift (n q : ℕ) (c : Fin q) (r : Fin (q - 1) → ZMod n) :
    Fin (q - 1) → ZMod n :=
  fun i => if (i : ℕ) = (c : ℕ) then r i + 1 else r i

/-- The replica contraction on `(ℤ/n)^(q-1)`, with the last party unshifted. -/
def Z (n q : ℕ) [NeZero n] {N : ℕ} (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) : ℂ :=
  ∑ x : (Fin (q - 1) → ZMod n) → Fin N → Fin 2,
    ∏ r : Fin (q - 1) → ZMod n,
      star (ψ (x r)) * ψ (fun u => x (shift n q (col u) r) u)

private def replicaOp {R : Type*} [Fintype R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (R → Fin N → Fin 2) (R → Fin N → Fin 2) ℂ :=
  fun x y => ∏ r, ∏ u, U u (x r u) (y r u)

private lemma replica_expand {R : Type*} [Fintype R] [DecidableEq R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : (Fin N → Fin 2) → ℂ) (x : R → Fin N → Fin 2) :
    (∏ r, (tensorOp U *ᵥ ψ) (x r)) =
      (replicaOp (R := R) U *ᵥ fun y => ∏ r, ψ (y r)) x := by
  classical
  simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply]
  conv_rhs =>
    arg 2
    intro y
    rw [replicaOp.eq_1]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.prod_mul_distrib

private lemma replica_unitary {R : Type*} [Fintype R] [DecidableEq R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star (replicaOp (R := R) U) * replicaOp U = 1 := by
  classical
  have hcol (u : Fin N) (b c : Fin 2) :
      (∑ a, star (U u a b) * U u a c) = if b = c then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M b c)
        (Matrix.mem_unitaryGroup_iff'.mp (hU u))
  ext y t
  change (∑ x : R → Fin N → Fin 2,
    star (∏ r, ∏ u, U u (x r u) (y r u)) *
      (∏ r, ∏ u, U u (x r u) (t r u))) = if y = t then 1 else 0
  simp_rw [star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun r (v : Fin N → Fin 2) =>
    ∏ u, star (U u (v u) (y r u)) * U u (v u) (t r u))]
  have hrow (r : R) :
      (∑ v : Fin N → Fin 2, ∏ u, star (U u (v u) (y r u)) * U u (v u) (t r u)) =
        ∏ u, if y r u = t r u then (1 : ℂ) else 0 := by
    rw [← Fintype.prod_sum (fun u (a : Fin 2) =>
      star (U u a (y r u)) * U u a (t r u))]
    simp_rw [hcol]
  simp_rw [hrow]
  by_cases h : y = t
  · subst t; simp
  · rw [if_neg h]
    obtain ⟨r, u, hu⟩ : ∃ r u, y r u ≠ t r u := by
      by_contra hn
      apply h
      exact funext fun r => funext fun u => not_not.mp (fun hh => hn ⟨r, u, hh⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ r)
      (Finset.prod_eq_zero (Finset.mem_univ u) (by simp [hu]))

private def shiftEquiv (n q : ℕ) (c : Fin q) :
    Equiv.Perm (Fin (q - 1) → ZMod n) where
  toFun := shift n q c
  invFun r i := if (i : ℕ) = (c : ℕ) then r i - 1 else r i
  left_inv r := by
    funext i
    dsimp [shift]
    split <;> simp_all
  right_inv r := by
    funext i
    dsimp [shift]
    split <;> simp_all

private def replicaPermutation {R : Type*} {N : ℕ}
    (σ : Fin N → Equiv.Perm R) : Equiv.Perm (R → Fin N → Fin 2) where
  toFun x r u := x (σ u r) u
  invFun x r u := x ((σ u).symm r) u
  left_inv x := by funext r u; simp
  right_inv x := by funext r u; simp

private lemma replicaOp_permutation {R : Type*} [Fintype R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (σ : Fin N → Equiv.Perm R)
    (x y : R → Fin N → Fin 2) :
    replicaOp U (replicaPermutation σ x) (replicaPermutation σ y) = replicaOp U x y := by
  classical
  change (∏ r, ∏ u, U u (x (σ u r) u) (y (σ u r) u)) =
    ∏ r, ∏ u, U u (x r u) (y r u)
  rw [Finset.prod_comm]
  conv_rhs => rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro u _
  exact Equiv.prod_comp (σ u) (fun r => U u (x r u) (y r u))

/-- Applying the same local unitaries to all replicas preserves the contraction. -/
private theorem Z_local_unitary_phase : ∀ (n q : ℕ) [NeZero n] {N : ℕ}
    (col : Fin N → Fin q) (ψ : (Fin N → Fin 2) → ℂ)
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ),
    (∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) → ‖z‖ = 1 →
    Z n q col (z • (tensorOp U *ᵥ ψ)) = Z n q col ψ := by
  classical
  intro n q _ N col ψ U z hU hz
  have hz' : star z * z = 1 := by
    simpa only [Complex.star_def, hz, one_pow, Complex.ofReal_one] using Complex.conj_mul' z
  have phase (φ : (Fin N → Fin 2) → ℂ) : Z n q col (z • φ) = Z n q col φ := by
    unfold Z
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro r _
    simp only [Pi.smul_apply, smul_eq_mul, star_mul]
    calc
      star (φ (x r)) * star z * (z * φ (fun u => x (shift n q (col u) r) u)) =
          (star z * z) * (star (φ (x r)) * φ (fun u => x (shift n q (col u) r) u)) := by
        ring
      _ = star (φ (x r)) * φ (fun u => x (shift n q (col u) r) u) := by rw [hz', one_mul]
  rw [phase]
  let R := Fin (q - 1) → ZMod n
  let σ : Fin N → Equiv.Perm R := fun u => shiftEquiv n q (col u)
  let P := replicaPermutation σ
  let A := replicaOp (R := R) U
  let v : (R → Fin N → Fin 2) → ℂ := fun x => ∏ r, ψ (x r)
  have hexpand : (fun x : R → Fin N → Fin 2 => ∏ r, (tensorOp U *ᵥ ψ) (x r)) =
      A *ᵥ v := by
    funext x
    exact replica_expand U ψ x
  have hcomm : (A *ᵥ v) ∘ P = A *ᵥ (v ∘ P) := by
    funext x
    change (∑ y, replicaOp U (P x) y * v y) =
      ∑ y, replicaOp U x y * v (P y)
    symm
    apply Fintype.sum_equiv P
    intro y
    rw [replicaOp_permutation]
  have hZ (φ : (Fin N → Fin 2) → ℂ) :
      Z n q col φ = star (fun x : R → Fin N → Fin 2 => ∏ r, φ (x r)) ⬝ᵥ
        ((fun x : R → Fin N → Fin 2 => ∏ r, φ (x r)) ∘ P) := by
    simp only [Z, dotProduct, Pi.star_apply, Function.comp_apply, star_prod,
      Finset.prod_mul_distrib]
    rfl
  calc
    Z n q col (tensorOp U *ᵥ ψ) = star (A *ᵥ v) ⬝ᵥ ((A *ᵥ v) ∘ P) := by
      rw [hZ, hexpand]
    _ = star (A *ᵥ v) ⬝ᵥ (A *ᵥ (v ∘ P)) := by rw [hcomm]
    _ = star v ⬝ᵥ (v ∘ P) := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.star_eq_conjTranspose, replica_unitary U hU, Matrix.vecMul_one]
    _ = Z n q col ψ := (hZ ψ).symm

/-- The replica translation assigned to a colour, with the last colour unshifted. -/
private def delta {N q : ℕ} (col : Fin N → Fin q) (u : Fin N) : (Fin (q - 1) → ZMod 3) :=
  fun i => if (i : ℕ) = (col u : ℕ) then 1 else 0

private lemma shift_delta {N q : ℕ} (col : Fin N → Fin q) (u : Fin N)
    (r : (Fin (q - 1) → ZMod 3)) : shift 3 q (col u) r = r + delta col u := by
  ext i
  simp only [shift.eq_1, delta.eq_1, Pi.add_apply]
  split <;> simp

/-- The binary bilinear character sum is controlled by the matrix rank. -/
private theorem bilinear_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2)) :
    (∑ y : Fin N → ZMod 2, ∑ z : Fin N → ZMod 2, complexSign (y ⬝ᵥ (A *ᵥ z))) =
      (2 : ℂ) ^ (2 * N - A.rank) := by
  classical
  have orth (v : Fin N → ZMod 2) :
      (∑ y : Fin N → ZMod 2, complexSign (y ⬝ᵥ v)) = if v = 0 then (2 : ℂ) ^ N else 0 := by
    let χ : AddChar (Fin N → ZMod 2) ℂ :=
      { toFun := fun y => complexSign (y ⬝ᵥ v)
        map_zero_eq_one' := by simp [complexSign, F₂]
        map_add_eq_mul' := fun y z => by rw [add_dotProduct, complexSign_add] }
    by_cases hv : v = 0
    · rw [if_pos hv]
      have hχ : χ = 1 := by ext y; simp [χ, hv, complexSign, F₂]
      simpa [χ, Fintype.card_fun, ZMod.card] using AddChar.sum_eq_card_of_eq_one hχ
    · rw [if_neg hv]
      apply AddChar.sum_eq_zero_of_ne_one (ψ := χ)
      intro hχ
      apply hv
      ext i
      change v i = 0
      have h := congrArg (fun f : AddChar (Fin N → ZMod 2) ℂ => f (Pi.single i 1)) hχ
      have hi : complexSign (v i) = 1 := by simpa [χ] using h
      by_contra hn
      norm_num [complexSign, F₂, hn] at hi
  rw [Finset.sum_comm]
  simp_rw [orth]
  let K := LinearMap.ker A.mulVecLin
  have hcard : Fintype.card K = 2 ^ (N - A.rank) := by
    rw [Module.card_eq_pow_finrank (K := (ZMod 2)), ZMod.card]
    congr 1
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    have h' : A.rank + Module.finrank (ZMod 2) K = N := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, rank] using h
    omega
  have hsum : (∑ z : Fin N → ZMod 2, if A *ᵥ z = 0 then (2 : ℂ) ^ N else 0) =
      (Fintype.card K : ℂ) * (2 : ℂ) ^ N := by
    simp [Finset.sum_ite, Fintype.card_subtype, K]
  rw [hsum, hcard, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  congr 1
  have hr : A.rank ≤ N := by simpa using A.rank_le_card_width
  omega

/-- Scalar multiplication contributes one squared norm per replica. -/
private theorem Z_smul {N : ℕ} (n q : ℕ) [NeZero n] (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (c : ℂ) :
    Z n q col (c • ψ) = (star c * c) ^ (n ^ (q - 1)) * Z n q col ψ := by
  classical
  simp only [Z.eq_1]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  have h (x : (Fin (q - 1) → ZMod n) → Fin N → Fin 2)
      (r : Fin (q - 1) → ZMod n) :
      star (ψ (x r)) * star c * (c * ψ (fun u => x (shift n q (col u) r) u)) =
        (star c * c) * (star (ψ (x r)) * ψ (fun u => x (shift n q (col u) r) u)) := by
    ring
  simp_rw [h, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, ← Finset.mul_sum, mul_pow]

/-- Expanding graph amplitudes gives the binary ternary-translation quadratic form. -/
private theorem graph_replica_form {N q : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) :
    Z 3 q col (graphAmp A) =
      ∑ x : (Fin (q - 1) → ZMod 3) → Fin N → ZMod 2, complexSign (F A (delta col) x) := by
  classical
  have hg (v : Fin N → ZMod 2) :
      graphAmp A v = complexSign (∑ u, ∑ w, if u < w then A u w * v u * v w else 0) := by
    simp only [graphAmp, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.normalExponent,
      Finset.sum_filter]
    exact (complex_sign_val _).symm
  have hs (t : ZMod 2) : star (complexSign t) = complexSign t := by
    rw [complexSign]
    split <;> norm_num
  change (∑ x : (Fin (q - 1) → ZMod 3) → Fin N → ZMod 2,
    ∏ r : (Fin (q - 1) → ZMod 3), star (graphAmp A (x r)) *
      graphAmp A (fun u => x (shift 3 q (col u) r) u)) = _
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [hg, hs, ← complexSign_add, shift_delta]
  rw [← sign_sum]
  congr 1
  simp only [F.eq_1, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split <;> ring

/-- The normal form factors the quadratic character sum into independent bilinear blocks. -/
private theorem quadratic_sum {N d : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (hA : ∀ u v, A u v = A v u) (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3))
    (h0 : (0 : (Fin d → ZMod 3)) ∉ P) (hP : ∀ t : (Fin d → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P)) :
    (∑ x : (Fin d → ZMod 3) → Fin N → ZMod 2, complexSign (F A δ x)) =
      (2 : ℂ) ^ N * ∏ t : {t : (Fin d → ZMod 3) // t ∈ P}, (2 : ℂ) ^ (2 * N - (C A δ t.val).rank) :=
        by
  classical
  obtain ⟨E, hE⟩ := ternary_translation_quadratic_normal_form A hA δ P h0 hP
  let T := {t : (Fin d → ZMod 3) // t ∈ P}
  have hblock (x : T → (Fin N → ZMod 2) × (Fin N → ZMod 2)) :
      complexSign (∑ t : T, ∑ u, ∑ v, (x t).1 u * C A δ t.val u v * (x t).2 v) =
        ∏ t : T, complexSign ((x t).1 ⬝ᵥ (C A δ t.val *ᵥ (x t).2)) := by
    rw [sign_sum]
    apply Finset.prod_congr rfl
    intro t _
    congr 1
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  calc
    (∑ x, complexSign (F A δ x)) =
        ∑ w : (Fin N → ZMod 2) × (T → (Fin N → ZMod 2) × (Fin N → ZMod 2)),
          complexSign (∑ t : T, ∑ u, ∑ v, (w.2 t).1 u * C A δ t.val u v * (w.2 t).2 v) := by
      apply Fintype.sum_equiv E.toEquiv
      intro x
      rw [hE]
      rfl
    _ = (2 : ℂ) ^ N * ∑ x : T → (Fin N → ZMod 2) × (Fin N → ZMod 2),
        ∏ t : T, complexSign ((x t).1 ⬝ᵥ (C A δ t.val *ᵥ (x t).2)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [hblock]
      simp [ZMod.card]
    _ = (2 : ℂ) ^ N * ∏ t : T,
        ∑ x : (Fin N → ZMod 2) × (Fin N → ZMod 2), complexSign (x.1 ⬝ᵥ (C A δ t.val *ᵥ x.2)) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      simp_rw [Fintype.sum_prod_type, bilinear_sum]
      rfl

/-- At replica index one the contraction is exactly the squared norm. -/
private theorem Z_one {N : ℕ} (q : ℕ) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) :
    Z 1 q col ψ = ((∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
  classical
  let R := Fin (q - 1) → ZMod 1
  have ht (r : R) (u : Fin N) : shift 1 q (col u) r = r := Subsingleton.elim _ _
  change (∑ x : R → Fin N → Fin 2,
    ∏ r : R, star (ψ (x r)) * ψ (fun u => x (shift 1 q (col u) r) u)) = _
  simp_rw [ht]
  simp only [Fintype.prod_unique]
  rw [Complex.ofReal_sum]
  apply Fintype.sum_equiv (Equiv.funUnique R (Fin N → Fin 2))
  intro x
  change star (ψ (x default)) * ψ (x default) = (↑(‖ψ (x default)‖ ^ 2) : ℂ)
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.conj_mul' (ψ (x default))

/-- Unnormalized graph amplitudes have squared norm `2^N`. -/
private theorem graph_norm {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2)) :
    (∑ x : Fin N → Fin 2, ‖graphAmp A x‖ ^ 2) = (2 : ℝ) ^ N := by
  classical
  simp [graphAmp.eq_1, norm_pow]

/-- Product unitaries preserve replica contractions even with an arbitrary scalar. -/
private theorem Z_local_scalar {N : ℕ} (n q : ℕ) [NeZero n] (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (c : ℂ) :
    Z n q col (c • (tensorOp U *ᵥ ψ)) = Z n q col (c • ψ) := by
  have h := Z_local_unitary_phase n q col (c • ψ) U 1 hU (by simp)
  simpa only [one_smul, Matrix.mulVec_smul] using h

/-- A normalized local-unitary graph amplitude has the reciprocal graph normalization. -/
private theorem graph_scalar_norm {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (c : ℂ)
    (hn : (∑ x : Fin N → Fin 2, ‖(c • (tensorOp U *ᵥ graphAmp A)) x‖ ^ 2) = 1) :
    star c * c = ((2 : ℂ) ^ N)⁻¹ := by
  have h := Z_local_scalar 1 1 (fun _ => 0) (graphAmp A) U hU c
  rw [Z_one, hn, Complex.ofReal_one, Z_smul, Z_one, graph_norm] at h
  simp only [one_pow, pow_one, Complex.ofReal_pow, Complex.ofReal_ofNat] at h
  have hz : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_right_cancel₀ hz
  rw [h.symm, inv_mul_cancel₀ hz]

/-- The replica form and the block count give the positive graph contraction. -/
private theorem graph_count {N q : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (hA : ∀ u v, A u v = A v u) (col : Fin N → Fin q)
    (P : Finset ((Fin (q - 1) → ZMod 3))) (h0 : (0 : (Fin (q - 1) → ZMod 3)) ∉ P)
    (hP : ∀ t : (Fin (q - 1) → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P)) :
    (((2 : ℂ) ^ N)⁻¹) ^ (3 ^ (q - 1)) * Z 3 q col (graphAmp A) =
      ((2 : ℂ) ^ (∑ t : {t : (Fin (q - 1) → ZMod 3) // t ∈ P}, (C A (delta col) t.val).rank))⁻¹ :=
        by
  classical
  let T := {t : (Fin (q - 1) → ZMod 3) // t ∈ P}
  obtain ⟨E, _⟩ := ternary_translation_quadratic_normal_form A hA (delta col) P h0 hP
  have hdim := E.finrank_eq
  have hdim' : N * 3 ^ (q - 1) = N + Fintype.card T * (N + N) := by
    simpa [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card,
      ZMod.card, T, Nat.mul_comm] using hdim
  have hr (t : T) : (C A (delta col) t.val).rank ≤ N := by
    simpa using (C A (delta col) t.val).rank_le_card_width
  have hsum : N + (∑ t : T, (2 * N - (C A (delta col) t.val).rank)) +
      (∑ t : T, (C A (delta col) t.val).rank) = N * 3 ^ (q - 1) := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    have hterm (t : T) : 2 * N - (C A (delta col) t.val).rank +
        (C A (delta col) t.val).rank = 2 * N :=
      Nat.sub_add_cancel ((hr t).trans (by omega))
    simp_rw [hterm]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hdim']
    ring
  rw [graph_replica_form, quadratic_sum A hA (delta col) P h0 hP]
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, inv_pow, ← pow_mul]
  apply mul_right_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))
  rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)),
    mul_assoc, ← pow_add, hsum]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

/-- Negation pairs admit representatives at every ternary replica dimension. -/
private theorem representatives_exist (d : ℕ) :
    ∃ P : Finset (Fin d → ZMod 3), (0 : (Fin d → ZMod 3)) ∉ P ∧
      ∀ t : (Fin d → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P) := by
  classical
  let e := Fintype.equivFin ((Fin d → ZMod 3))
  let P := Finset.univ.filter (fun t : (Fin d → ZMod 3) => e t < e (-t))
  refine ⟨P, by simp [P], ?_⟩
  intro t ht
  have hn : e t ≠ e (-t) := by
    intro h
    apply ht
    have he := e.injective h
    ext i
    change t i = 0
    have hi : t i = -(t i) := congrFun he i
    exact (show ∀ a : ZMod 3, a = -a → a = 0 from by decide) (t i) hi
  simp only [P, Finset.mem_filter,
    Finset.mem_univ,
    true_and, neg_neg]
  exact ⟨fun h => not_lt.mpr h.le, fun h => lt_of_le_of_ne (not_lt.mp h) hn⟩

/-- A single graph matrix counts every replica contraction of a normalized stabilizer state. -/
private theorem stabilizer_replica_count {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hψ : D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.StabilizedBy
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.pauliSet ψ)
    (hn : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1) :
    ∃ A : Matrix (Fin N) (Fin N) (ZMod 2), A.IsSymm ∧
      ∀ (q : ℕ) (col : Fin N → Fin q) (P : Finset ((Fin (q - 1) → ZMod 3))),
        (0 : (Fin (q - 1) → ZMod 3)) ∉ P →
        (∀ t : (Fin (q - 1) → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P)) →
        Z 3 q col ψ =
          ((2 : ℂ) ^ (∑ t : {t : (Fin (q - 1) → ZMod 3) // t ∈ P}, (C A (delta col) t.val).rank))⁻¹
            := by
  classical
  obtain ⟨U, A, c, hU, hA, _, he⟩ := stabilizer_graph_normal_form ψ hψ
  subst ψ
  have hc := graph_scalar_norm A U hU c hn
  refine ⟨A, hA, ?_⟩
  intro q col P h0 hP
  rw [Z_local_scalar 3 q col (graphAmp A) U hU c, Z_smul, hc]
  exact graph_count A (fun u v => (hA.apply u v).symm) col P h0 hP

/-- Every ternary replica contraction of a normalized qubit stabilizer state is positive real. -/
private theorem stabilizer_replica_positive {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hψ : D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.StabilizedBy
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.pauliSet ψ)
    (hn : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1)
    (q : ℕ) (col : Fin N → Fin q) : 0 < (Z 3 q col ψ).re ∧ (Z 3 q col ψ).im = 0 := by
  classical
  obtain ⟨A, _, hA⟩ := stabilizer_replica_count ψ hψ hn
  obtain ⟨P, h0, hP⟩ := representatives_exist (q - 1)
  rw [hA q col P h0 hP, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by positivity, rfl⟩

/-- The normalized replica multi-entropy, using the real part of the complex quotient. -/
def S (n q : ℕ) [NeZero n] {N : ℕ} (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  1 / (1 - (n : ℝ)) * (1 / (n : ℝ) ^ (q - 2)) *
    Real.log ((Z n q col ψ / (Z 1 q col ψ) ^ (n ^ (q - 1))).re)

/-- The Rényi tripartite information: four singleton cuts minus three pair cuts. -/
def I3 (n : ℕ) [NeZero n] {N : ℕ} (party : Fin N → Fin 4)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  S n 2 ((![(0 : Fin 2), 0, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- ABC:D
    S n 2 ((![(0 : Fin 2), 0, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ABD:C
    S n 2 ((![(0 : Fin 2), 1, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ACD:B
    S n 2 ((![(1 : Fin 2), 0, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ - -- BCD:A
    (S n 2 ((![(0 : Fin 2), 0, 1, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- AB:CD
      S n 2 ((![(0 : Fin 2), 1, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- AC:BD
      S n 2 ((![(0 : Fin 2), 1, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ) -- AD:BC

/-- The genuine four-party multi-entropy with convention parameter `a`. -/
def GM4 (n : ℕ) [NeZero n] (a : ℝ) {N : ℕ} (party : Fin N → Fin 4)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  S n 4 party ψ - 1 / 3 *
    (S n 3 ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- AB:C:D
      S n 3 ((![(0 : Fin 3), 1, 0, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- AC:B:D
      S n 3 ((![(0 : Fin 3), 1, 2, 0] : Fin 4 → Fin 3) ∘ party) ψ + -- AD:B:C
      S n 3 ((![(1 : Fin 3), 0, 0, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- BC:A:D
      S n 3 ((![(1 : Fin 3), 0, 2, 0] : Fin 4 → Fin 3) ∘ party) ψ + -- BD:A:C
      S n 3 ((![(1 : Fin 3), 2, 0, 0] : Fin 4 → Fin 3) ∘ party) ψ) + -- CD:A:B
    1 / 3 *
      (S n 2 ((![(0 : Fin 2), 0, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- ABC:D
        S n 2 ((![(0 : Fin 2), 0, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ABD:C
        S n 2 ((![(0 : Fin 2), 1, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ACD:B
        S n 2 ((![(1 : Fin 2), 0, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ) - -- BCD:A
    a * I3 n party ψ

/-- Positivity of all n = 3 replica contractions and the four-party collapse. -/
def claim : Prop :=
  ∀ (N : ℕ) (party : Fin N → Fin 4) (ψ : (Fin N → Fin 2) → ℂ),
    StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      (∀ (q : ℕ) (col : Fin N → Fin q),
        0 < (Z 3 q col ψ).re ∧ (Z 3 q col ψ).im = 0) ∧
      ∀ a : ℝ, GM4 3 a party ψ = -(a - 1 / 9) * I3 3 party ψ


/-- The separation matrix of a ternary colouring of four labelled parties. -/
private def cutPattern (v : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) Bool :=
  ![![decide (v 0 ≠ v 0), decide (v 0 ≠ v 1), decide (v 0 ≠ v 2), decide (v 0 ≠ v 3)],
    ![decide (v 1 ≠ v 0), decide (v 1 ≠ v 1), decide (v 1 ≠ v 2), decide (v 1 ≠ v 3)],
    ![decide (v 2 ≠ v 0), decide (v 2 ≠ v 1), decide (v 2 ≠ v 2), decide (v 2 ≠ v 3)],
    ![decide (v 3 ≠ v 0), decide (v 3 ≠ v 1), decide (v 3 ≠ v 2), decide (v 3 ≠ v 3)]]

private lemma cutPattern_apply (v : Fin 4 → ZMod 3) (i j : Fin 4) :
    cutPattern v i j = decide (v i ≠ v j) := by
  rw [cutPattern.eq_1]
  fin_cases i <;> fin_cases j <;> rfl

private def colourValue {q : ℕ} (t : Fin (q - 1) → ZMod 3) (c : Fin q) : ZMod 3 :=
  ∑ i : Fin (q - 1), t i * (if (i : ℕ) = (c : ℕ) then 1 else 0)

private def modes1 : Finset (Fin 1 → ZMod 3) :=
  {![1]}

private def modes2 : Finset (Fin 2 → ZMod 3) :=
  {![0, 1], ![1, 0], ![1, 1], ![1, 2]}

private def modes3 : Finset (Fin 3 → ZMod 3) :=
  {![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2],
    ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2]}

private def partitionSum (q : ℕ) (P : Finset (Fin (q - 1) → ZMod 3))
    (m : Fin 4 → Fin q) (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) : ℝ :=
  ∑ t ∈ P, f (cutPattern (colourValue t ∘ m))




open Classical
open scoped BigOperators
open D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit

private def partition {α : Type*} (u : α → ZMod 3) : Setoid (Option α) :=
  Setoid.ker (anchored u)

private theorem partition_eq_iff {α : Type*} (u v : α → ZMod 3) :
    partition u = partition v ↔ SamePartition (anchored u) (anchored v) := by
  constructor
  · intro h i j
    exact Iff.of_eq (congrArg (fun r : Setoid (Option α) => r i j) h)
  · intro h
    exact Setoid.ext h

-- This is the load-bearing use of the new affine/anchored theorem: the mode
-- image is a genuine partition set, with no multiplicities hidden by `image`.
private theorem representative_injOn {α : Type*}
    (P : Finset (α → ZMod 3)) (h0 : (0 : α → ZMod 3) ∉ P)
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P)) :
    Set.InjOn partition (P : Set (α → ZMod 3)) := by
  intro u hu v hv huv
  have hu0 : u ≠ 0 := by
    intro h
    exact h0 (h ▸ hu)
  obtain ⟨w, _, hw⟩ := D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit.result (P : Set (α → ZMod 3)) hP u hu0
  have hu' : u ∈ P ∧ SamePartition (anchored u) (anchored u) :=
    ⟨hu, fun _ _ => Iff.rfl⟩
  have hv' : v ∈ P ∧ SamePartition (anchored u) (anchored v) :=
    ⟨hv, (partition_eq_iff u v).mp huv⟩
  exact (hw u hu').trans (hw v hv').symm

private theorem representative_sum {α A : Type*} [AddCommMonoid A]
    (P : Finset (α → ZMod 3)) (h0 : (0 : α → ZMod 3) ∉ P)
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : Setoid (Option α) → A) :
    (∑ u ∈ P, f (partition u)) = ∑ Q ∈ P.image partition, f Q := by
  classical
  exact (Finset.sum_image (representative_injOn P h0 hP)).symm

-- No finite setoid enumeration is needed for this obstruction. It directly
-- reuses Mathlib's finite pigeonhole theorem, via `ker_eq_bot_iff`.
private theorem four_party_partition_ne_bot (u : Fin 3 → ZMod 3) :
    partition u ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (anchored u) := Setoid.ker_eq_bot_iff.mp h
  have hcard := Fintype.card_le_of_injective (anchored u) hinj
  norm_num [Fintype.card_option] at hcard

private theorem nonzero_partition_ne_top {α : Type*} (u : α → ZMod 3) (hu : u ≠ 0) :
    partition u ≠ ⊤ := by
  intro h
  apply hu
  funext a
  have ha : anchored u (some a) = anchored u none := by
    change partition u (some a) none
    rw [h]
    trivial
  simpa [anchored] using ha

-- A merger's fibers are contained in the coloring partition exactly when that
-- coloring factors through the merger. The function is chosen on actual fibers;
-- surjectivity ensures every target label is represented.
private theorem factor_through_merger {α β : Type*}
    (m : Option α → Option β) (hm : Function.Surjective m)
    (u : α → ZMod 3) (hcompat : Setoid.ker m ≤ partition u) :
    ∃ g : Option β → ZMod 3, anchored u = g ∘ m := by
  classical
  let g : Option β → ZMod 3 := fun b => anchored u (Function.surjInv hm b)
  refine ⟨g, ?_⟩
  funext a
  apply hcompat
  exact (Function.rightInverse_surjInv hm (m a)).symm

-- Merger factorization followed by representative selection. This is the
-- surjectivity half of the merger-to-compatible-partitions sum transport.
private theorem compatible_partition_has_representative {α β : Type*}
    (P : Set (β → ZMod 3))
    (hP : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ P ↔ -v ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (u : α → ZMod 3) (hu : u ≠ 0)
    (hcompat : Setoid.ker m ≤ partition u) :
    ∃ v : β → ZMod 3,
      v ∈ P ∧ partition u = Setoid.ker (anchored v ∘ m) := by
  classical
  obtain ⟨g, hg⟩ := factor_through_merger m hm u hcompat
  let v : β → ZMod 3 := fun b => g (some b) - g none
  have hv : anchored v = fun b => g b - g none := by
    funext b
    cases b <;> simp [anchored, v]
  have hv0 : v ≠ 0 := by
    intro h
    have hgconst (b : Option β) : g b = g none := by
      apply sub_eq_zero.mp
      have hb : anchored v b = 0 := by rw [h]; cases b <;> rfl
      simpa only [hv] using hb
    apply hu
    funext a
    calc
      u a = g (m (some a)) := congrFun hg (some a)
      _ = g none := hgconst _
      _ = g (m none) := (hgconst _).symm
      _ = 0 := (congrFun hg none).symm
  obtain ⟨w, ⟨hw, hpart⟩, _⟩ := result P hP v hv0
  refine ⟨w, hw, Setoid.ext (fun i j => ?_)⟩
  change anchored u i = anchored u j ↔ anchored w (m i) = anchored w (m j)
  calc
    anchored u i = anchored u j ↔ g (m i) = g (m j) := by rw [hg]; rfl
    _ ↔ anchored v (m i) = anchored v (m j) := by rw [hv]; exact sub_left_inj.symm
    _ ↔ anchored w (m i) = anchored w (m j) := hpart (m i) (m j)

private def pullPartition {α β : Type*} (m : Option α → Option β)
    (v : β → ZMod 3) : Setoid (Option α) :=
  Setoid.ker (anchored v ∘ m)

private theorem pulled_representative_injOn {α β : Type*}
    (P : Finset (β → ZMod 3)) (h0 : (0 : β → ZMod 3) ∉ P)
    (hP : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ P ↔ -v ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m) :
    Set.InjOn (pullPartition m) (P : Set (β → ZMod 3)) := by
  intro v hv w hw h
  apply representative_injOn P h0 hP hv hw
  apply Setoid.ext
  intro i j
  obtain ⟨a, rfl⟩ := hm i
  obtain ⟨b, rfl⟩ := hm j
  exact Iff.of_eq (congrArg (fun Q : Setoid (Option α) => Q a b) h)

private theorem pulled_partition_mem_image {α β : Type*}
    (P : Finset (α → ZMod 3))
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (v : β → ZMod 3) (hv : v ≠ 0) :
    pullPartition m v ∈ P.image partition := by
  classical
  let u : α → ZMod 3 := fun a => anchored v (m (some a)) - anchored v (m none)
  have hu : anchored u = fun a => anchored v (m a) - anchored v (m none) := by
    funext a
    cases a <;> simp [anchored, u]
  have hu0 : u ≠ 0 := by
    intro h
    have hconstant (b : Option β) : anchored v b = anchored v (m none) := by
      obtain ⟨a, rfl⟩ := hm b
      apply sub_eq_zero.mp
      have ha : anchored u a = 0 := by rw [h]; cases a <;> rfl
      simpa only [hu] using ha
    apply hv
    funext b
    calc
      v b = anchored v (some b) := rfl
      _ = anchored v (m none) := hconstant _
      _ = anchored v none := (hconstant _).symm
      _ = 0 := rfl
  obtain ⟨w, ⟨hw, hpart⟩, _⟩ := result (P : Set (α → ZMod 3)) hP u hu0
  apply Finset.mem_image.mpr
  refine ⟨w, hw, ?_⟩
  calc
    partition w = partition u := ((partition_eq_iff u w).mpr hpart).symm
    _ = pullPartition m v := by
      apply Setoid.ext
      intro i j
      change anchored u i = anchored u j ↔ anchored v (m i) = anchored v (m j)
      rw [hu]
      exact sub_left_inj

-- The full finite transport: each merger sum counts each compatible coloring
-- partition once. Both directions consume representative selection, not a
-- 13-entry numerical enumeration.
private theorem merger_sum_transport {α β A : Type*} [AddCommMonoid A]
    (Pα : Finset (α → ZMod 3)) (h0α : (0 : α → ZMod 3) ∉ Pα)
    (hPα : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ Pα ↔ -u ∉ Pα))
    (Pβ : Finset (β → ZMod 3)) (h0β : (0 : β → ZMod 3) ∉ Pβ)
    (hPβ : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ Pβ ↔ -v ∉ Pβ))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (f : Setoid (Option α) → A) :
    (∑ v ∈ Pβ, f (pullPartition m v)) =
      ∑ Q ∈ (Pα.image partition).filter (fun Q => Setoid.ker m ≤ Q), f Q := by
  classical
  refine Finset.sum_bij (fun v _ => pullPartition m v) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro v hv
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply pulled_partition_mem_image Pα hPα m hm v
      intro h
      exact h0β (h ▸ hv)
    · intro i j hij
      change anchored v (m i) = anchored v (m j)
      exact congrArg (anchored v) hij
  · intro v hv w hw h
    exact pulled_representative_injOn Pβ h0β hPβ m hm hv hw h
  · intro Q hQ
    obtain ⟨hQ, hcompat⟩ := Finset.mem_filter.mp hQ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hQ
    have hu0 : u ≠ 0 := by
      intro h
      exact h0α (h ▸ hu)
    obtain ⟨v, hv, heq⟩ := compatible_partition_has_representative
      (Pβ : Set (β → ZMod 3)) hPβ m hm u hu0 hcompat
    exact ⟨v, hv, heq.symm⟩

private def relation (c : Fin 6 → Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, c 0, c 1, c 2], ![c 0, true, c 3, c 4],
    ![c 1, c 3, true, c 5], ![c 2, c 4, c 5, true]]

private def Valid (c : Fin 6 → Bool) : Prop :=
  ∀ i j k : Fin 4,
    relation c i j = true → relation c j k = true → relation c i k = true

private abbrev FourPartition := {c : Fin 6 → Bool // Valid c}

private instance : DecidablePred Valid := fun c =>
  inferInstanceAs (Decidable (∀ i j k : Fin 4,
    relation c i j = true → relation c j k = true → relation c i k = true))

private instance : PartialOrder FourPartition where
  le c d := ∀ k : Fin 6, c.val k = true → d.val k = true
  le_refl _ _ h := h
  le_trans _ _ _ hcd hde k h := hde k (hcd k h)
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext k
    have hc := hcd k
    have hd := hdc k
    cases hck : c.val k <;> cases hdk : d.val k <;> simp_all

private instance : DecidableLE FourPartition := fun c d =>
  inferInstanceAs (Decidable (∀ k : Fin 6, c.val k = true → d.val k = true))

private instance : DecidableLT FourPartition := by
  intro c d
  by_cases hcd : c ≤ d
  · by_cases hdc : d ≤ c
    · exact isFalse (fun h => h.2 hdc)
    · exact isTrue ⟨hcd, hdc⟩
  · exact isFalse (fun h => hcd h.1)

private def discrete : FourPartition := ⟨fun _ => false, by decide⟩

private def indiscrete : FourPartition := ⟨fun _ => true, by decide⟩

private instance : BoundedOrder FourPartition where
  bot := discrete
  top := indiscrete
  bot_le c k h := by cases h
  le_top c k h := rfl

private instance : LocallyFiniteOrder FourPartition := Fintype.toLocallyFiniteOrder

private def edgeCount (c : FourPartition) : ℕ :=
  ∑ k : Fin 6, if c.val k then 1 else 0

private def coefficient (c : FourPartition) : ℤ :=
  match edgeCount c with
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => 2
  | _ => -6

private def toSetoid (c : FourPartition) : Setoid (Fin 4) where
  r i j := relation c.val i j = true
  iseqv.refl i := by fin_cases i <;> rfl
  iseqv.symm := by
    intro i j h
    fin_cases i <;> fin_cases j <;> exact h
  iseqv.trans := fun {i j k} hij hjk => c.property i j k hij hjk

private noncomputable def code (Q : Setoid (Fin 4)) : Fin 6 → Bool := by
  classical
  exact ![decide (Q 0 1), decide (Q 0 2), decide (Q 0 3),
    decide (Q 1 2), decide (Q 1 3), decide (Q 2 3)]

private theorem relation_code (Q : Setoid (Fin 4)) (i j : Fin 4) :
    relation (code Q) i j = true ↔ Q i j := by
  classical
  fin_cases i <;> fin_cases j <;>
    simp [relation, code, Q.refl'] <;>
    constructor <;> intro h <;> exact Q.symm' h

private noncomputable def fromSetoid (Q : Setoid (Fin 4)) : FourPartition :=
  ⟨code Q, fun i j k hij hjk =>
    (relation_code Q i k).mpr
      (Q.trans' ((relation_code Q i j).mp hij) ((relation_code Q j k).mp hjk))⟩

private theorem to_from (Q : Setoid (Fin 4)) : toSetoid (fromSetoid Q) = Q := by
  apply Setoid.ext
  exact relation_code Q

private theorem from_to (c : FourPartition) : fromSetoid (toSetoid c) = c := by
  apply Subtype.ext
  funext k
  have hdecide : ∀ b : Bool, decide (b = true) = b := by
    intro b
    cases b <;> rfl
  fin_cases k
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 0 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 1 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 2 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 3 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 4 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 5 <;> unfold toSetoid <;> simp [relation, h]

private theorem toSetoid_le_iff (c d : FourPartition) :
    toSetoid c ≤ toSetoid d ↔ c ≤ d := by
  constructor
  · intro h k
    fin_cases k
    · exact @h 0 1
    · exact @h 0 2
    · exact @h 0 3
    · exact @h 1 2
    · exact @h 1 3
    · exact @h 2 3
  · intro h i j
    fin_cases i <;> fin_cases j <;>
      first | exact id | exact h 0 | exact h 1 | exact h 2 |
        exact h 3 | exact h 4 | exact h 5

private theorem fromSetoid_le_iff (Q R : Setoid (Fin 4)) :
    fromSetoid Q ≤ fromSetoid R ↔ Q ≤ R := by
  rw [← toSetoid_le_iff, to_from, to_from]

private def catalogue : Fin 15 → FourPartition :=
  ![discrete,
    ⟨![true, false, false, false, false, false], by decide⟩,
    ⟨![false, true, false, false, false, false], by decide⟩,
    ⟨![false, false, true, false, false, false], by decide⟩,
    ⟨![false, false, false, true, false, false], by decide⟩,
    ⟨![false, false, false, false, true, false], by decide⟩,
    ⟨![false, false, false, false, false, true], by decide⟩,
    ⟨![true, true, false, true, false, false], by decide⟩,
    ⟨![true, false, true, false, true, false], by decide⟩,
    ⟨![false, true, true, false, false, true], by decide⟩,
    ⟨![false, false, false, true, true, true], by decide⟩,
    ⟨![true, false, false, false, false, true], by decide⟩,
    ⟨![false, true, false, false, true, false], by decide⟩,
    ⟨![false, false, true, true, false, false], by decide⟩,
    indiscrete]

set_option maxHeartbeats 1000000 in
-- Kernel reduction checks the complete finite partition catalogue.
private theorem catalogue_bijective : Function.Bijective catalogue := by decide

private def pairPartition (k : Fin 6) : FourPartition := catalogue ⟨k.val + 1, by omega⟩
private def triplePartition (k : Fin 4) : FourPartition := catalogue ⟨k.val + 7, by omega⟩
private def doublePartition (k : Fin 3) : FourPartition := catalogue ⟨k.val + 11, by omega⟩

private theorem catalogue_coefficient : ∀ k : Fin 15,
    coefficient (catalogue k) =
      (![1, -1, -1, -1, -1, -1, -1, 2, 2, 2, 2, 1, 1, 1, -6] : Fin 15 → ℤ) k := by
  decide

-- The finite audit covers all fifteen equivalence relations.  We keep the
-- cancellation kernel-auditable by rewriting the finite sum through the
-- explicit catalogue and reducing the fifteen cases with `norm_num`.
set_option maxHeartbeats 4000000 in
-- Kernel reduction normalizes each of the fifteen interval sums.
set_option maxRecDepth 100000 in
private theorem coefficient_cancel (Q : FourPartition) (hQ : Q ≠ ⊥) :
    (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, coefficient p) = 0 := by
  have hIcc : Finset.univ.filter (fun p : FourPartition => p ≤ Q) =
      Finset.Icc (⊥ : FourPartition) Q := by
    ext p
    simp
  have hfilter :
      (∑ p : FourPartition, if p ≤ Q then coefficient p else 0) =
        ∑ j : Fin 15, if catalogue j ≤ Q then coefficient (catalogue j) else 0 := by
    exact (catalogue_bijective.sum_comp
      (fun p => if p ≤ Q then coefficient p else 0)).symm
  rw [← hIcc, Finset.sum_filter]
  rw [hfilter]
  obtain ⟨k, rfl⟩ := catalogue_bijective.surjective Q
  fin_cases k
  all_goals try exact (hQ rfl).elim
  all_goals
    norm_num [catalogue, coefficient, edgeCount, Fin.sum_univ_succ,
      discrete, indiscrete] at hQ ⊢ <;> decide

-- This expansion is over all fifteen *partitions*. The mode representative
-- theorem and merger_sum_transport are what justify replacing these upper
-- partition sums with the Fourier mode sums in the existing entropy theorem.
private theorem weighted_sum_expansion (G : FourPartition → ℝ) :
    (∑ p : FourPartition, (coefficient p : ℝ) * G p) =
      G ⊥ - (∑ k : Fin 6, G (pairPartition k)) +
        2 * (∑ k : Fin 4, G (triplePartition k)) +
        (∑ k : Fin 3, G (doublePartition k)) - 6 * G ⊤ := by
  calc
    _ = ∑ k : Fin 15, (coefficient (catalogue k) : ℝ) * G (catalogue k) :=
      (catalogue_bijective.sum_comp (fun p => (coefficient p : ℝ) * G p)).symm
    _ = _ := by
      simp only [catalogue_coefficient]
      have hbot : (⊥ : FourPartition) = discrete := rfl
      have htop : (⊤ : FourPartition) = indiscrete := rfl
      rw [hbot, htop]
      norm_num [Fin.sum_univ_succ, pairPartition, triplePartition, doublePartition, catalogue]
      ring_nf

private def upperSum (Ω : Finset FourPartition) (f : FourPartition → ℝ)
    (p : FourPartition) : ℝ :=
  ∑ Q ∈ Ω, if p ≤ Q then f Q else 0

-- The integer audit supplies the real cancellation by casting its finite sum;
-- no unproved identification of integer and real Möbius functions is used.
private theorem weighted_upper_sum_cancel (Ω : Finset FourPartition)
    (hΩ : ∀ Q ∈ Ω, Q ≠ ⊥) (f : FourPartition → ℝ) :
    (∑ p : FourPartition, (coefficient p : ℝ) * upperSum Ω f p) = 0 := by
  unfold upperSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro Q hQ
  have hcast : (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ)) = 0 := by
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ℝ)) (coefficient_cancel Q (hΩ Q hQ))
  have hIcc : Finset.univ.filter (fun p : FourPartition => p ≤ Q) =
      Finset.Icc ⊥ Q := by
    ext p
    simp
  calc
    (∑ p : FourPartition, (coefficient p : ℝ) * (if p ≤ Q then f Q else 0)) =
        ∑ p : FourPartition, if p ≤ Q then (coefficient p : ℝ) * f Q else 0 := by
      simp_rw [mul_ite, mul_zero]
    _ = ∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ) * f Q := by
      rw [← Finset.sum_filter, hIcc]
    _ = (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ)) * f Q := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hcast, zero_mul]

-- This is the source question's coefficient identity for an arbitrary weight
-- on a family of nontrivial, non-discrete four-point coloring partitions.
-- The remaining exact merger bindings replace each upperSum by partitionSum.
private theorem four_party_counting_identity (Ω : Finset FourPartition)
    (hΩbot : ∀ Q ∈ Ω, Q ≠ ⊥) (hΩtop : ∀ Q ∈ Ω, Q ≠ ⊤)
    (f : FourPartition → ℝ) :
    upperSum Ω f ⊥ - (∑ k : Fin 6, upperSum Ω f (pairPartition k)) +
      2 * (∑ k : Fin 4, upperSum Ω f (triplePartition k)) +
      (∑ k : Fin 3, upperSum Ω f (doublePartition k)) = 0 := by
  have htop : upperSum Ω f ⊤ = 0 := by
    unfold upperSum
    apply Finset.sum_eq_zero
    intro Q hQ
    apply if_neg
    intro h
    exact hΩtop Q hQ (top_le_iff.mp h)
  have h := weighted_sum_expansion (upperSum Ω f)
  rw [weighted_upper_sum_cancel Ω hΩbot f, htop, mul_zero, sub_zero] at h
  exact h.symm

open D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
open scoped BigOperators

private def anchorEquiv (r : ℕ) : Fin (r + 1) ≃ Option (Fin r) :=
  finSuccEquiv' (Fin.last r)

private theorem colourValue2 : ∀ (t : Fin 1 → ZMod 3) (c : Fin 2),
    colourValue t c = anchored t (anchorEquiv 1 c) := by decide

private theorem colourValue3 : ∀ (t : Fin 2 → ZMod 3) (c : Fin 3),
    colourValue t c = anchored t (anchorEquiv 2 c) := by decide

private theorem colourValue4 : ∀ (t : Fin 3 → ZMod 3) (c : Fin 4),
    colourValue t c = anchored t (anchorEquiv 3 c) := by decide

private def mergeMap {r : ℕ} (m : Fin 4 → Fin (r + 1)) :
    Option (Fin 3) → Option (Fin r) :=
  anchorEquiv r ∘ m ∘ (anchorEquiv 3).symm

private theorem mergeMap_surjective {r : ℕ} (m : Fin 4 → Fin (r + 1))
    (hm : Function.Surjective m) : Function.Surjective (mergeMap m) :=
  (anchorEquiv r).surjective.comp (hm.comp (anchorEquiv 3).symm.surjective)

private def pairMergers : Fin 6 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 1, 0, 2], ![0, 1, 2, 0],
    ![1, 0, 0, 2], ![1, 0, 2, 0], ![1, 2, 0, 0]]

private def singletonCuts : Fin 4 → Fin 4 → Fin 2 :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]

private def balancedCuts : Fin 3 → Fin 4 → Fin 2 :=
  ![![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]]

private theorem pairMergers_surjective :
    ∀ k : Fin 6, Function.Surjective (pairMergers k) := by decide

private theorem singletonCuts_surjective :
    ∀ k : Fin 4, Function.Surjective (singletonCuts k) := by decide

private theorem balancedCuts_surjective :
    ∀ k : Fin 3, Function.Surjective (balancedCuts k) := by decide

private noncomputable def encodePartition (Q : Setoid (Option (Fin 3))) : FourPartition :=
  fromSetoid (Setoid.comap (anchorEquiv 3) Q)

private theorem encodePartition_le_iff (Q R : Setoid (Option (Fin 3))) :
    encodePartition Q ≤ encodePartition R ↔ Q ≤ R := by
  rw [encodePartition, encodePartition, fromSetoid_le_iff]
  constructor
  · intro h i j hij
    obtain ⟨a, rfl⟩ := (anchorEquiv 3).surjective i
    obtain ⟨b, rfl⟩ := (anchorEquiv 3).surjective j
    exact h hij
  · exact fun h => Setoid.comap_monotone _ h

private theorem encodePartition_injective : Function.Injective encodePartition := by
  intro Q R h
  exact le_antisymm ((encodePartition_le_iff Q R).mp h.le)
    ((encodePartition_le_iff R Q).mp h.ge)

private theorem encodePartition_surjective : Function.Surjective encodePartition := by
  intro c
  refine ⟨Setoid.comap (anchorEquiv 3).symm (toSetoid c), ?_⟩
  unfold encodePartition
  have h : Setoid.comap (anchorEquiv 3)
      (Setoid.comap (anchorEquiv 3).symm (toSetoid c)) = toSetoid c := by
    apply Setoid.ext
    intro i j
    simp only [Setoid.comap_rel, Equiv.symm_apply_apply]
  rw [h, from_to]

private theorem encodePartition_bot : encodePartition ⊥ = ⊥ := by
  apply le_antisymm
  · obtain ⟨Q, hQ⟩ := encodePartition_surjective ⊥
    rw [← hQ]
    exact (encodePartition_le_iff _ _).mpr bot_le
  · exact bot_le

private theorem encodePartition_top : encodePartition ⊤ = ⊤ := by
  apply le_antisymm
  · exact le_top
  · obtain ⟨Q, hQ⟩ := encodePartition_surjective ⊤
    rw [← hQ]
    exact (encodePartition_le_iff _ _).mpr le_top

private noncomputable def partitionSupport (P : Finset (Fin 3 → ZMod 3)) :
    Finset FourPartition := (P.image partition).image encodePartition

private theorem partitionSupport_ne_bot (P : Finset (Fin 3 → ZMod 3)) :
    ∀ Q ∈ partitionSupport P, Q ≠ ⊥ := by
  intro Q hQ
  unfold partitionSupport at hQ
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hR
  intro h
  apply four_party_partition_ne_bot u
  apply encodePartition_injective
  exact h.trans encodePartition_bot.symm

private theorem partitionSupport_ne_top (P : Finset (Fin 3 → ZMod 3))
    (h0 : (0 : Fin 3 → ZMod 3) ∉ P) :
    ∀ Q ∈ partitionSupport P, Q ≠ ⊤ := by
  intro Q hQ
  unfold partitionSupport at hQ
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hR
  have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
  intro h
  apply nonzero_partition_ne_top u hu0
  apply encodePartition_injective
  exact h.trans encodePartition_top.symm

private theorem encoded_upperSum (P : Finset (Fin 3 → ZMod 3))
    (f : FourPartition → ℝ) (K : Setoid (Option (Fin 3))) :
    upperSum (partitionSupport P) f (encodePartition K) =
      ∑ Q ∈ (P.image partition).filter (fun Q => K ≤ Q), f (encodePartition Q) := by
  classical
  unfold upperSum partitionSupport
  rw [Finset.sum_image (fun _ _ _ _ h => encodePartition_injective h)]
  simp only [encodePartition_le_iff, Finset.sum_filter]

-- The merger's source anchor need not map to the target anchor. Its kernel is
-- carried correctly because conjugation uses equivalences on both label sets.
private theorem encoded_merger_kernel {r : ℕ} (m : Fin 4 → Fin (r + 1)) :
    encodePartition (Setoid.ker (mergeMap m)) = fromSetoid (Setoid.ker m) := by
  unfold encodePartition
  congr 1
  apply Setoid.ext
  intro i j
  change mergeMap m (anchorEquiv 3 i) = mergeMap m (anchorEquiv 3 j) ↔ m i = m j
  simp only [mergeMap, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]

private theorem merger_sum_upperSum {r : ℕ}
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (R : Finset (Fin r → ZMod 3)) (h0R : (0 : Fin r → ZMod 3) ∉ R)
    (hR : ∀ u : Fin r → ZMod 3, u ≠ 0 → (u ∈ R ↔ -u ∉ R))
    (m : Fin 4 → Fin (r + 1)) (hm : Function.Surjective m)
    (f : FourPartition → ℝ) :
    (∑ t ∈ R, f (encodePartition (pullPartition (mergeMap m) t))) =
      upperSum (partitionSupport P) f (fromSetoid (Setoid.ker m)) := by
  rw [← encoded_merger_kernel m, encoded_upperSum]
  exact merger_sum_transport P h0 hP R h0R hR (mergeMap m)
    (mergeMap_surjective m hm) (fun Q => f (encodePartition Q))

private theorem full_sum_upperSum
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : FourPartition → ℝ) :
    (∑ t ∈ P, f (encodePartition (partition t))) =
      upperSum (partitionSupport P) f ⊥ := by
  rw [← encodePartition_bot, encoded_upperSum]
  simpa using representative_sum P h0 hP (fun Q => f (encodePartition Q))

private def separation (c : FourPartition) : Matrix (Fin 4) (Fin 4) Bool :=
  fun i j => !(relation c.val i j)

private theorem separation_encoded (v : Option (Fin 3) → ZMod 3)
    (i j : Fin 4) :
    separation (encodePartition (Setoid.ker v)) i j =
      decide (v (anchorEquiv 3 i) ≠ v (anchorEquiv 3 j)) := by
  classical
  have h := relation_code (Setoid.comap (anchorEquiv 3) (Setoid.ker v)) i j
  change (!(relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j)) = _
  by_cases he : v (anchorEquiv 3 i) = v (anchorEquiv 3 j)
  · have ht := h.mpr he
    simp [ht, he]
  · have ht : relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j = false := by
      cases hr : relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j
      · rfl
      · exact False.elim (he (h.mp hr))
    simp [ht, he]

private theorem pairMergers_partition (k : Fin 6) :
    fromSetoid (Setoid.ker (pairMergers k)) = pairPartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, pairMergers, pairPartition, catalogue]

private theorem singletonCuts_partition (k : Fin 4) :
    fromSetoid (Setoid.ker (singletonCuts k)) = triplePartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, singletonCuts, triplePartition, catalogue]

private theorem balancedCuts_partition (k : Fin 3) :
    fromSetoid (Setoid.ker (balancedCuts k)) = doublePartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, balancedCuts, doublePartition, catalogue]

-- The source uses `q - 1` in its public arity.  This r-indexed spelling keeps
-- the dependent finite type normalized while proving the transport bridge.
private def partitionSumR (r : ℕ) (P : Finset (Fin r → ZMod 3))
    (m : Fin 4 → Fin (r + 1)) (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) : ℝ :=
  ∑ t ∈ P, f (cutPattern (colourValue (q := r + 1) t ∘ m))

private theorem partitionSum_as_upperSum {r : ℕ}
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (R : Finset (Fin r → ZMod 3)) (h0R : (0 : Fin r → ZMod 3) ∉ R)
    (hR : ∀ u : Fin r → ZMod 3, u ≠ 0 → (u ∈ R ↔ -u ∉ R))
    (hcolour : ∀ (t : Fin r → ZMod 3) (c : Fin (r + 1)),
      colourValue (q := r + 1) t c = anchored t (anchorEquiv r c))
    (m : Fin 4 → Fin (r + 1)) (hm : Function.Surjective m)
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR r R m f =
      upperSum (partitionSupport P) (fun c => f (separation c))
        (fromSetoid (Setoid.ker m)) := by
  unfold partitionSumR
  calc
    _ = ∑ t ∈ R, f (separation (encodePartition (pullPartition (mergeMap m) t))) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      funext i j
      rw [cutPattern_apply]
      change decide (colourValue (q := r + 1) t (m i) ≠ colourValue (q := r + 1) t (m j)) =
        separation (encodePartition (Setoid.ker (anchored t ∘ mergeMap m))) i j
      rw [separation_encoded]
      simp only [Function.comp_apply, mergeMap, Equiv.symm_apply_apply, hcolour]
    _ = _ := merger_sum_upperSum P h0 hP R h0R hR m hm (fun c => f (separation c))

private theorem partitionSum_full_upperSum
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR 3 P id f =
      upperSum (partitionSupport P) (fun c => f (separation c)) ⊥ := by
  unfold partitionSumR
  calc
    _ = ∑ t ∈ P, f (separation (encodePartition (partition t))) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      funext i j
      rw [cutPattern_apply]
      change decide (colourValue (q := 4) t i ≠ colourValue (q := 4) t j) =
        separation (encodePartition (Setoid.ker (anchored t))) i j
      rw [separation_encoded, colourValue4, colourValue4]
    _ = _ := full_sum_upperSum P h0 hP (fun c => f (separation c))

-- The same generic representative family drives the full and all merger sums.
-- The function f is arbitrary; only the fifteen-element partition poset is
-- finitely audited, while arbitrary weighted mode sums are transported by the
-- structural classification theorem.
private theorem structural_partition_count
    (P3 : Finset (Fin 3 → ZMod 3)) (h03 : (0 : Fin 3 → ZMod 3) ∉ P3)
    (hP3 : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P3 ↔ -u ∉ P3))
    (P2 : Finset (Fin 2 → ZMod 3)) (h02 : (0 : Fin 2 → ZMod 3) ∉ P2)
    (hP2 : ∀ u : Fin 2 → ZMod 3, u ≠ 0 → (u ∈ P2 ↔ -u ∉ P2))
    (P1 : Finset (Fin 1 → ZMod 3)) (h01 : (0 : Fin 1 → ZMod 3) ∉ P1)
    (hP1 : ∀ u : Fin 1 → ZMod 3, u ≠ 0 → (u ∈ P1 ↔ -u ∉ P1))
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR 3 P3 id f -
      (∑ k : Fin 6, partitionSumR 2 P2 (pairMergers k) f) +
      2 * (∑ k : Fin 4, partitionSumR 1 P1 (singletonCuts k) f) +
      (∑ k : Fin 3, partitionSumR 1 P1 (balancedCuts k) f) = 0 := by
  have hp (k : Fin 6) : partitionSumR 2 P2 (pairMergers k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (pairPartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P2 h02 hP2 colourValue3
      (pairMergers k) (pairMergers_surjective k) f, pairMergers_partition]
  have ht (k : Fin 4) : partitionSumR 1 P1 (singletonCuts k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (triplePartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P1 h01 hP1 colourValue2
      (singletonCuts k) (singletonCuts_surjective k) f, singletonCuts_partition]
  have hd (k : Fin 3) : partitionSumR 1 P1 (balancedCuts k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (doublePartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P1 h01 hP1 colourValue2
      (balancedCuts k) (balancedCuts_surjective k) f, balancedCuts_partition]
  rw [partitionSum_full_upperSum P3 h03 hP3 f]
  simp_rw [hp, ht, hd]
  exact four_party_counting_identity (partitionSupport P3)
    (partitionSupport_ne_bot P3) (partitionSupport_ne_top P3 h03)
    (fun c => f (separation c))


set_option maxHeartbeats 2000000 in
-- Check the three concrete representative families and normalize merger sums.
private theorem partition_count (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSum 4 modes3 id f -
      (partitionSum 3 modes2 (![0, 0, 1, 2] : Fin 4 → Fin 3) f +
        partitionSum 3 modes2 (![0, 1, 0, 2] : Fin 4 → Fin 3) f +
        partitionSum 3 modes2 (![0, 1, 2, 0] : Fin 4 → Fin 3) f +
        partitionSum 3 modes2 (![1, 0, 0, 2] : Fin 4 → Fin 3) f +
        partitionSum 3 modes2 (![1, 0, 2, 0] : Fin 4 → Fin 3) f +
        partitionSum 3 modes2 (![1, 2, 0, 0] : Fin 4 → Fin 3) f) + 2 *
      (partitionSum 2 modes1 (![0, 0, 0, 1] : Fin 4 → Fin 2) f +
        partitionSum 2 modes1 (![0, 0, 1, 0] : Fin 4 → Fin 2) f +
        partitionSum 2 modes1 (![0, 1, 0, 0] : Fin 4 → Fin 2) f +
        partitionSum 2 modes1 (![1, 0, 0, 0] : Fin 4 → Fin 2) f) +
      (partitionSum 2 modes1 (![0, 0, 1, 1] : Fin 4 → Fin 2) f +
        partitionSum 2 modes1 (![0, 1, 0, 1] : Fin 4 → Fin 2) f +
        partitionSum 2 modes1 (![0, 1, 1, 0] : Fin 4 → Fin 2) f) = 0 := by
  classical
  have h03 : (0 : Fin 3 → ZMod 3) ∉ modes3 := by decide
  have hP3 : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ modes3 ↔ -u ∉ modes3) := by decide
  have h02 : (0 : Fin 2 → ZMod 3) ∉ modes2 := by decide
  have hP2 : ∀ u : Fin 2 → ZMod 3, u ≠ 0 → (u ∈ modes2 ↔ -u ∉ modes2) := by decide
  have h01 : (0 : Fin 1 → ZMod 3) ∉ modes1 := by decide
  have hP1 : ∀ u : Fin 1 → ZMod 3, u ≠ 0 → (u ∈ modes1 ↔ -u ∉ modes1) := by decide
  have h := structural_partition_count modes3 h03 hP3 modes2 h02 hP2 modes1 h01 hP1 f
  simpa [partitionSumR, partitionSum, Fin.sum_univ_succ,
    pairMergers, singletonCuts, balancedCuts, add_assoc] using h

private def partitionRank {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (party : Fin N → Fin 4) (p : Matrix (Fin 4) (Fin 4) Bool) : ℝ :=
  (Matrix.rank (fun u v => if p (party u) (party v) then A u v else 0) : ℝ)

private lemma rank_partition {N q : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (party : Fin N → Fin 4) (m : Fin 4 → Fin q) (t : Fin (q - 1) → ZMod 3) :
    ((C A (delta (m ∘ party)) t).rank : ℝ) =
      partitionRank A party (cutPattern (colourValue t ∘ m)) := by
  unfold partitionRank
  congr 2
  ext u v
  simp [C, delta, cutPattern_apply, colourValue, Function.comp_def, ite_not]

private theorem entropy_formula {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hn : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1) (q : ℕ) (col : Fin N → Fin q)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (P : Finset (Fin (q - 1) → ZMod 3))
    (hc : Z 3 q col ψ =
      ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
        (C A (delta col) t.val).rank))⁻¹) :
    S 3 q col ψ = Real.log 2 / (2 * (3 : ℝ) ^ (q - 2)) *
      ∑ t ∈ P, ((C A (delta col) t).rank : ℝ) := by
  classical
  rw [S, Z_one, hn, Complex.ofReal_one, one_pow, div_one, hc]
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.ofReal_re, Real.log_inv, Real.log_pow]
  simp only [Nat.cast_sum]
  rw [Finset.sum_coe_sort (s := P) (f := fun t => ((C A (delta col) t).rank : ℝ))]
  norm_num
  ring

private theorem entropy_partition {N q : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hn : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (party : Fin N → Fin 4)
    (m : Fin 4 → Fin q) (P : Finset (Fin (q - 1) → ZMod 3))
    (hc : Z 3 q (m ∘ party) ψ =
      ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
        (C A (delta (m ∘ party)) t.val).rank))⁻¹) :
    S 3 q (m ∘ party) ψ = Real.log 2 / (2 * (3 : ℝ) ^ (q - 2)) *
      partitionSum q P m (partitionRank A party) := by
  rw [entropy_formula ψ hn q (m ∘ party) A P hc]
  simp_rw [rank_partition]
  rfl

theorem result : claim := by
  classical
  intro N party ψ hψ hn
  constructor
  · exact fun q col => stabilizer_replica_positive ψ hψ hn q col
  · obtain ⟨A, _, hc⟩ := stabilizer_replica_count ψ hψ hn
    let f := partitionRank A party
    have e2 (m : Fin 4 → Fin 2) :
        S 3 2 (m ∘ party) ψ = Real.log 2 / 2 * partitionSum 2 modes1 m f := by
      have h0 : (0 : Fin 1 → ZMod 3) ∉ modes1 := by decide
      have hP : ∀ t : Fin 1 → ZMod 3, t ≠ 0 → (t ∈ modes1 ↔ -t ∉ modes1) := by decide
      simpa only [show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one] using
        entropy_partition ψ hn A party m modes1 (hc 2 (m ∘ party) modes1 h0 hP)
    have e3 (m : Fin 4 → Fin 3) :
        S 3 3 (m ∘ party) ψ = Real.log 2 / 6 * partitionSum 3 modes2 m f := by
      have h0 : (0 : Fin 2 → ZMod 3) ∉ modes2 := by decide
      have hP : ∀ t : Fin 2 → ZMod 3, t ≠ 0 → (t ∈ modes2 ↔ -t ∉ modes2) := by decide
      convert entropy_partition ψ hn A party m modes2 (hc 3 (m ∘ party) modes2 h0 hP)
        using 1
      norm_num [f]
    have e4 : S 3 4 party ψ = Real.log 2 / 18 * partitionSum 4 modes3 id f := by
      have h0 : (0 : Fin 3 → ZMod 3) ∉ modes3 := by decide
      have hP : ∀ t : Fin 3 → ZMod 3, t ≠ 0 → (t ∈ modes3 ↔ -t ∉ modes3) := by decide
      convert entropy_partition ψ hn A party id modes3 (hc 4 party modes3 h0 hP)
        using 1 <;> norm_num [f]
    intro a
    rw [GM4.eq_1]
    repeat rw [I3.eq_1]
    rw [e4]
    simp_rw [e3, e2]
    linear_combination (Real.log 2 / 18) * partition_count f

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
