/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive partial-transpose floor for finite permutation symmetrizers. -/

/-
admission_basis: escape-witness
escape_witness: symmetrizer_partialTranspose_floor
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19210
Direct frozen dependencies: none.
proof_shape: IsSymmetricVector: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric, LouvetSymmetricAbsolutelyPPT.IsSymmetricOperator, LouvetSymmetricAbsolutelyPPT.IsSymmetricUnitary, LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant, LouvetSymmetricAbsolutelyPPT.occupationEval_injective, LouvetSymmetricAbsolutelyPPT.symmetric_conjugate, LouvetSymmetricAbsolutelyPPT.result, SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric, LouvetSymmetricAbsolutelyPPT.operator_mulVec_symmetric; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P, SymmetricAbsolutePPTPermutationFloor.Q_mulVec, SymmetricAbsolutePPTPermutationFloor.Q_mul, SymmetricAbsolutePPTPermutationFloor.Q_one, SymmetricAbsolutePPTPermutationFloor.Q_star, SymmetricAbsolutePPTPermutationFloor.Q_apply, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_psd, SymmetricAbsolutePPTPermutationFloor.Q_mul_P, SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.P_idempotent, SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric, SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric, SymmetricAbsolutePPTPermutationFloor.Local.R, SymmetricAbsolutePPTPermutationFloor.Local.localP, SymmetricAbsolutePPTPermutationFloor.R_eq_Q, SymmetricAbsolutePPTPermutationFloor.P_eq_avg_R, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Q_mul_P, SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.P_idempotent, SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric, SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric, SymmetricAbsolutePPTPermutationFloor.PiS_mul_P, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, LouvetSymmetricAbsolutelyPPT.occupationEval, LouvetSymmetricAbsolutelyPPT.occupationEval_injective, LouvetSymmetricAbsolutelyPPT.P_rank_le, LouvetSymmetricAbsolutelyPPT.P_mul_operator, LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank, LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum, SymmetricAbsolutePPTPermutationFloor.P_eq_avg_R; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_mulVec: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric, SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric; escape_witness: none; Direct frozen dependencies: none.
proof_shape: wordPerm_mul: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Q_mul; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_mul: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Q_mul_P, SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.P_idempotent; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_one: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Q_mul_P, SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.P_idempotent, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_star: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.Local.R_star; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_apply: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram, SymmetricAbsolutePPTPermutationFloor.Local.R_apply; escape_witness: none; Direct frozen dependencies: none.
proof_shape: cross_equation: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram; escape_witness: none; Direct frozen dependencies: none.
proof_shape: crossGram: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.cross_gram_entry, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_psd; escape_witness: none; Direct frozen dependencies: none.
proof_shape: cross_gram_entry: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram; escape_witness: none; Direct frozen dependencies: none.
proof_shape: cross_partialTranspose_gram: content; consumer: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_psd; escape_witness: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram; Direct frozen dependencies: none.
proof_shape: cross_partialTranspose_psd: content; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram; Direct frozen dependencies: none.
proof_shape: Average.expect_formula: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Average.avg_idempotent, SymmetricAbsolutePPTPermutationFloor.Average.avg_hermitian, SymmetricAbsolutePPTPermutationFloor.Average.subgroup_avg_left, SymmetricAbsolutePPTPermutationFloor.Average.avg_section, SymmetricAbsolutePPTPermutationFloor.Q_mul_P, SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.P_idempotent, SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose, SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor, SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.avg_left: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Average.subgroup_avg_left, SymmetricAbsolutePPTPermutationFloor.Q_mul_P; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.avg_idempotent: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_idempotent, SymmetricAbsolutePPTPermutationFloor.PiS_idempotent; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.avg_hermitian: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_hermitian, SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose, SymmetricAbsolutePPTPermutationFloor.PiS_hermitian; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.subgroup_avg_left: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.PiS_mul_P; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.sectionEquiv: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Average.sum_section, SymmetricAbsolutePPTPermutationFloor.Average.avg_section; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.sum_section: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Average.avg_section; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Average.avg_section: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_coset_expansion; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Q_mul_P: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_hermitian: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_idempotent: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_mulVec_symmetric: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.occupationEval_injective, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_mulVec_of_symmetric: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.P_mul_operator, LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.swapFn: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.swapFn_involutive, SymmetricAbsolutePPTPermutationFloor.Swaps.swapPerm, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_membership, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_cross, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_self; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.swapFn_apply: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.swapFn_involutive, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_membership, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_cross, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_self; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.swapFn_involutive: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.swapPerm, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_involutive; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.swapPerm: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.difference_card: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_involutive, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_membership, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_cross; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.differences_disjoint: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_involutive; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_membership, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_cross, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_self, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_image, SymmetricAbsolutePPTPermutationFloor.Cosets.rep, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_identity, SymmetricAbsolutePPTPermutationFloor.Cosets.partEquiv, SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_involutive; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange_involutive: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_image, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_involutive; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange_membership: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_image; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange_cross: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep_cross; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange_self: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep_identity; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Swaps.exchange_image: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep_section, SymmetricAbsolutePPTPermutationFloor.Cosets.partEquiv; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.part_mk: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep_section; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.part_card: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_section, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_involutive, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_cross, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_identity, SymmetricAbsolutePPTPermutationFloor.Cosets.partEquiv; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.rep: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.rep_section, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_cross, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_identity, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, SymmetricAbsolutePPTPermutationFloor.Cosets.rep_involutive; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.rep_section: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_coset_expansion; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.rep_involutive: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.rep_cross: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.rep_identity: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.partEquiv: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.card_cosets; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.card_parts: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Cosets.card_cosets; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Cosets.card_cosets: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_coset_expansion; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Tensor.pt_kronecker_sandwich: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Tensor.pt_tensor_projector; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Tensor.pt_tensor_projector: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.R: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose, SymmetricAbsolutePPTPermutationFloor.Local.R_local_tensor, SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor, SymmetricAbsolutePPTPermutationFloor.R_eq_Q, SymmetricAbsolutePPTPermutationFloor.P_eq_avg_R, SymmetricAbsolutePPTPermutationFloor.PiS_hermitian, SymmetricAbsolutePPTPermutationFloor.PiS_idempotent, SymmetricAbsolutePPTPermutationFloor.PiS_mul_P, SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion, SymmetricAbsolutePPTPermutationFloor.Local.R_apply, SymmetricAbsolutePPTPermutationFloor.Local.R_star; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.R_apply: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose, SymmetricAbsolutePPTPermutationFloor.Local.R_local_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.R_star: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose, SymmetricAbsolutePPTPermutationFloor.PiS_hermitian; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.avg_transpose: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.mem_H_iff: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.transport; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.color: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.fiber0, SymmetricAbsolutePPTPermutationFloor.Local.fiber1, SymmetricAbsolutePPTPermutationFloor.Local.transport, SymmetricAbsolutePPTPermutationFloor.Local.localEquiv, SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.fiber0: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.split; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.fiber1: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.split; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.split: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.localEquiv, SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.transport: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.localEquiv; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.localEquiv: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.split_comp: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.R_local_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.R_local_tensor: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.localP: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor, SymmetricAbsolutePPTPermutationFloor.PiS_hermitian, SymmetricAbsolutePPTPermutationFloor.PiS_idempotent, SymmetricAbsolutePPTPermutationFloor.PiS_psd, SymmetricAbsolutePPTPermutationFloor.PiS_mul_P, SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Local.localP_tensor: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: R_eq_Q: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_coset_expansion; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_eq_avg_R: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.PiS_mul_P, SymmetricAbsolutePPTPermutationFloor.P_coset_expansion; escape_witness: none; Direct frozen dependencies: none.
proof_shape: PiS_hermitian: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.PiS_psd, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: PiS_idempotent: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.PiS_psd, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: PiS_psd: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: PiS_mul_P: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pt_split: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: partialTranspose_PiS_sandwich: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_coset_expansion: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets; escape_witness: none; Direct frozen dependencies: none.
proof_shape: partialTranspose_smulC: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets; escape_witness: none; Direct frozen dependencies: none.
proof_shape: partialTranspose_one: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_partialTranspose_cosets: bind-only; consumer: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; escape_witness: none; Direct frozen dependencies: none.
proof_shape: symmetrizer_partialTranspose_floor: content; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; Direct frozen dependencies: none.
-/

import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fin.Tuple.Basic
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound

open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
/-- A vector of the symmetric subspace `Sym^N(ℂ^d)`: invariant under every permutation of the
`N` sites. -/
def IsSymmetricVector {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] (v : (I → L) → ℂ) : Prop :=
  ∀ σ : Equiv.Perm I, ∀ x, v (x ∘ σ) = v x

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open Matrix
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
noncomputable def Q (σ : Equiv.Perm I) : Matrix (I → L) (I → L) ℂ :=
  Equiv.Perm.permMatrix ℂ (Equiv.arrowCongr σ.symm (Equiv.refl L))
noncomputable def P (I L : Type*) [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] : Matrix (I → L) (I → L) ℂ :=
  Finset.expect Finset.univ (fun σ : Equiv.Perm I => Q (L := L) σ)
private lemma Q_mulVec (σ : Equiv.Perm I) (v : (I → L) → ℂ) :
    Q σ *ᵥ v = fun x => v (x ∘ σ) := by
  rw [Q, Matrix.permMatrix_mulVec]
  rfl
omit [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] in
private lemma wordPerm_mul (σ τ : Equiv.Perm I) :
    ((Equiv.arrowCongr (σ * τ).symm (Equiv.refl L))) = (Equiv.arrowCongr τ.symm (Equiv.refl L)) * (Equiv.arrowCongr σ.symm (Equiv.refl L)) := by
  exact Equiv.arrowCongr_trans σ.symm (Equiv.refl L) τ.symm (Equiv.refl L)
private lemma Q_mul (σ τ : Equiv.Perm I) :
    Q (L := L) (σ * τ) = Q σ * Q τ := by
  rw [Q, wordPerm_mul, Matrix.permMatrix_mul]
  rfl
omit [DecidableEq I] [Fintype L] in
private lemma Q_one : Q (L := L) (1 : Equiv.Perm I) = 1 := by
  have h : (Equiv.arrowCongr (1 : Equiv.Perm I).symm (Equiv.refl L)) = 1 :=
    Equiv.arrowCongr_refl
  simp [Q, h]
omit [DecidableEq I] [Fintype L] in
private lemma Q_star (σ : Equiv.Perm I) : (Q (L := L) σ)ᴴ = Q σ⁻¹ := by
  have h : ((Equiv.arrowCongr σ.symm (Equiv.refl L)))⁻¹ = (Equiv.arrowCongr (σ⁻¹).symm (Equiv.refl L)) := by
    exact Equiv.arrowCongr_symm σ.symm (Equiv.refl L)
  simp [Q, h]
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open Matrix
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
attribute [local instance] Classical.propDecidable
omit [DecidableEq I] [Fintype L] in
private lemma Q_apply (σ : Equiv.Perm I) (x y : I → L) :
    Q σ x y = if y = x ∘ σ then 1 else 0 := by
  simp [Q, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.arrowCongr, eq_comm]
omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma cross_equation (S : Finset I) (σ : Equiv.Perm I)
    (hi : Function.Involutive σ)
    (hc : ∀ i, σ i ≠ i → (σ i ∈ S ↔ i ∉ S))
    (x y : I → L) :
    S.piecewise x y = (S.piecewise y x) ∘ σ ↔
      Set.EqOn (x ∘ σ) x {i | σ i ≠ i} ∧ Set.EqOn (y ∘ σ) y {i | σ i ≠ i} ∧ (fun i : {i // σ i = i} => x i.val) = (fun i : {i // σ i = i} => y i.val) := by
  constructor
  · intro h
    have ha (i : I) (hmove : σ i ≠ i) : x (σ i) = x i ∧ y (σ i) = y i := by
      have h1 := congrFun h i
      have h2 := congrFun h (σ i)
      have hs := hc i hmove
      by_cases hsi : i ∈ S
      · have hss : σ i ∉ S := (not_congr hs.symm).mp (fun a => a hsi)
        simpa [Finset.piecewise, hsi, hss, hi i, Function.comp_apply] using
          And.intro h1.symm h2
      · have hss : σ i ∈ S := hs.mpr hsi
        simpa [Finset.piecewise, hsi, hss, hi i, Function.comp_apply] using
          And.intro h2 h1.symm
    refine ⟨fun i hm => (ha i hm).1, fun i hm => (ha i hm).2, ?_⟩
    funext i
    have h1 := congrFun h i.1
    by_cases hsi : i.1 ∈ S
    · simpa [Finset.piecewise, hsi, i.2] using h1
    · simpa [Finset.piecewise, hsi, i.2] using h1.symm
  · rintro ⟨hx, hy, hf⟩
    funext i
    by_cases hfix : σ i = i
    · have he := congrFun hf ⟨i,hfix⟩
      by_cases hsi : i ∈ S <;>
        simp_all [Finset.piecewise, Function.comp_apply]
    · have hs := hc i hfix
      have hx' := hx hfix
      have hy' := hy hfix
      by_cases hsi : i ∈ S
      · have hss : σ i ∉ S := (not_congr hs.symm).mp (fun a => a hsi)
        simpa [Finset.piecewise, Function.comp_apply, hsi, hss] using hx'.symm
      · have hss : σ i ∈ S := hs.mpr hsi
        simpa [Finset.piecewise, Function.comp_apply, hsi, hss] using hy'.symm
private noncomputable def crossGram (σ : Equiv.Perm I) :
    Matrix (I → L) ({i // σ i = i} → L) ℂ :=
  {x | Set.EqOn (x ∘ σ) x {i | σ i ≠ i}}.indicator
    (fun x => Pi.single (fun i : {i // σ i = i} => x i.val) (1 : ℂ))
private lemma cross_gram_entry (σ : Equiv.Perm I) (x y : I → L) :
    (crossGram (L := L) σ * (crossGram (L := L) σ)ᴴ) x y =
      if Set.EqOn (x ∘ σ) x {i | σ i ≠ i} ∧ Set.EqOn (y ∘ σ) y {i | σ i ≠ i} ∧ (fun i : {i // σ i = i} => x i.val) = (fun i : {i // σ i = i} => y i.val) then 1 else 0 := by
  classical
  by_cases hx : Set.EqOn (x ∘ σ) x {i | σ i ≠ i} <;> by_cases hy : Set.EqOn (y ∘ σ) y {i | σ i ≠ i} <;>
    simp [crossGram, Set.indicator, Pi.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hx, hy] <;> simp [eq_comm]
private lemma cross_partialTranspose_gram (S : Finset I) (σ : Equiv.Perm I)
    (hi : Function.Involutive σ)
    (hc : ∀ i, σ i ≠ i → (σ i ∈ S ↔ i ∉ S)) :
    partialTransposeOn S (Q (L := L) σ) = crossGram (L := L) σ * (crossGram (L := L) σ)ᴴ := by
  ext x y
  rw [cross_gram_entry]
  simp only [partialTransposeOn, Q_apply]
  simp only [cross_equation S σ hi hc x y]
private lemma cross_partialTranspose_psd (S : Finset I) (σ : Equiv.Perm I)
    (hi : Function.Involutive σ)
    (hc : ∀ i, σ i ≠ i → (σ i ∈ S ↔ i ∉ S)) :
    (partialTransposeOn S (Q (L := L) σ)).PosSemidef := by
  rw [cross_partialTranspose_gram S σ hi hc]
  exact Matrix.posSemidef_self_mul_conjTranspose _
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

open scoped BigOperators Matrix ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average
open Matrix QuotientGroup
open scoped Pointwise
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
omit [Group G] [Fintype I] [DecidableEq I] in
private lemma expect_formula (R : G → Matrix I I ℂ) :
    Finset.expect Finset.univ R = (Fintype.card G : ℂ)⁻¹ • ∑ g, R g := by
  simpa only [← NNRat.cast_smul_eq_nnqsmul ℂ, NNRat.cast_inv, NNRat.cast_natCast]
    using (Finset.expect_univ (f := R))
private lemma avg_left (R : G →* Matrix I I ℂ) (g : G) : R g * Finset.expect Finset.univ R = Finset.expect Finset.univ R := by
  rw [Finset.mul_expect]
  exact Fintype.expect_equiv (Equiv.mulLeft g) _ _ (fun h => (R.map_mul g h).symm)
private lemma avg_idempotent (R : G →* Matrix I I ℂ) : Finset.expect Finset.univ R * Finset.expect Finset.univ R = Finset.expect Finset.univ R := by
  classical
  let E : Matrix I I ℂ ≃ₐ[ℂ] Module.End ℂ (I → ℂ) := Matrix.toLinAlgEquiv'
  let ρ : Representation ℂ G (I → ℂ) := E.toRingEquiv.toMonoidHom.comp R
  letI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have hnorm : ρ.averageMap = E (Finset.expect Finset.univ R) := by
    rw [show Finset.expect Finset.univ R =
        (Fintype.card G : ℂ)⁻¹ • ∑ g, R g by
      simpa only [← NNRat.cast_smul_eq_nnqsmul ℂ,
        NNRat.cast_inv, NNRat.cast_natCast] using (Finset.expect_univ (f := R))]
    simp only [Representation.averageMap, GroupAlgebra.average,
      map_smul, map_sum, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one, invOf_eq_inv]
    all_goals rfl
  apply E.injective
  rw [map_mul]
  have hid := (Representation.isProj_averageMap ρ).isIdempotentElem.eq
  rw [hnorm] at hid
  exact hid
private lemma avg_hermitian (R : G →* Matrix I I ℂ) (hR : ∀ g, (R g)ᴴ = R g⁻¹) :
    (Finset.expect Finset.univ R).IsHermitian := by
  change (Finset.expect Finset.univ R)ᴴ = Finset.expect Finset.univ R
  simp only [expect_formula, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    hR, star_inv₀, star_natCast]
  congr 1
  exact Equiv.sum_comp (Equiv.inv G) (fun g => R g)
private lemma subgroup_avg_left (R : G →* Matrix I I ℂ) (H : Subgroup G) [Fintype H] :
    Finset.expect Finset.univ (R.comp H.subtype) * Finset.expect Finset.univ R = Finset.expect Finset.univ R := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  conv_lhs => lhs; rw [expect_formula]
  rw [Matrix.smul_mul, Matrix.sum_mul]
  simp only [MonoidHom.comp_apply, avg_left, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
private noncomputable def sectionEquiv (H : Subgroup G) (r : G ⧸ H → G)
    (hr : ∀ q, (r q : G ⧸ H) = q) : (G ⧸ H) × H ≃ G :=
  ((Equiv.prodCongr (Equiv.refl (G ⧸ H))
      (((QuotientGroup.quotientBot (G := H)).toEquiv.symm).trans
        (Subgroup.quotientEquivOfEq (Subgroup.bot_subgroupOf H).symm))).trans
      (Subgroup.quotientEquivProdOfLE' (bot_le : (⊥ : Subgroup G) ≤ H) r hr).symm).trans
    (QuotientGroup.quotientBot (G := G)).toEquiv
private lemma sum_section (R : G →* Matrix I I ℂ) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)] (r : G ⧸ H → G)
    (hr : ∀ q, (r q : G ⧸ H) = q) :
    ∑ g, R g = ∑ q : G ⧸ H, R (r q) * ∑ h : H, R h := by
  rw [← Equiv.sum_comp (sectionEquiv H r hr) (fun g => R g), Fintype.sum_prod_type]
  change (∑ x, ∑ y : H, R (r x * y)) = _
  simp only [R.map_mul, Matrix.mul_sum]
private lemma avg_section (R : G →* Matrix I I ℂ) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)] (r : G ⧸ H → G)
    (hr : ∀ q, (r q : G ⧸ H) = q) :
    Finset.expect Finset.univ R = (Fintype.card (G ⧸ H) : ℂ)⁻¹ • ∑ q : G ⧸ H, R (r q) * Finset.expect Finset.univ (R.comp H.subtype) := by
  have hc : Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
  simp only [expect_formula]
  rw [sum_section R H r hr]
  simp only [Matrix.mul_smul, MonoidHom.comp_apply, ← Finset.smul_sum, smul_smul,
    hc, Nat.cast_mul, mul_inv]
  rfl
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open Matrix
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
private lemma Q_mul_P (σ : Equiv.Perm I) : Q σ * P I L = P I L := by
  simpa only [Average.expect_formula, P, MonoidHom.coe_mk, OneHom.coe_mk] using Average.avg_left ({ toFun := Q, map_one' := Q_one, map_mul' := Q_mul } : Equiv.Perm I →* Matrix (I → L) (I → L) ℂ) σ
lemma P_hermitian (I L : Type*) [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] : (P I L).IsHermitian := by
  simpa only [Average.expect_formula, P, MonoidHom.coe_mk, OneHom.coe_mk] using Average.avg_hermitian ({ toFun := Q, map_one' := Q_one, map_mul' := Q_mul } : Equiv.Perm I →* Matrix (I → L) (I → L) ℂ) Q_star
lemma P_idempotent (I L : Type*) [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] : P I L * P I L = P I L := by
  simpa only [Average.expect_formula, P, MonoidHom.coe_mk, OneHom.coe_mk] using Average.avg_idempotent ({ toFun := Q, map_one' := Q_one, map_mul' := Q_mul } : Equiv.Perm I →* Matrix (I → L) (I → L) ℂ)
lemma P_mulVec_symmetric (v : (I → L) → ℂ) : IsSymmetricVector (P I L *ᵥ v) := by
  intro σ x
  have h := congrArg (fun A => (A *ᵥ v) x) (Q_mul_P (L := L) σ)
  simpa only [← Matrix.mulVec_mulVec, Q_mulVec] using h
lemma P_mulVec_of_symmetric (v : (I → L) → ℂ) (hv : IsSymmetricVector v) :
    P I L *ᵥ v = v := by
  have hc : (Fintype.card (Equiv.Perm I) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hq (σ : Equiv.Perm I) : Q σ *ᵥ v = v := by
    ext x
    simpa only [Q_mulVec] using hv σ x
  simp only [P, Average.expect_formula, Matrix.smul_mulVec, Matrix.sum_mulVec, hq,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps
variable {I : Type*} [DecidableEq I]
private noncomputable def swapFn (A B : Finset I) (f : A ≃ B) : I → I :=
  Function.extend (Subtype.val : A → I) (fun a => (f a).val)
    (Function.extend (Subtype.val : B → I) (fun b => (f.symm b).val) id)
private lemma swapFn_apply (A B : Finset I) (f : A ≃ B) (i : I) :
    swapFn A B f i =
      if h : i ∈ A then (f ⟨i,h⟩ : I) else if h : i ∈ B then (f.symm ⟨i,h⟩ : I) else i := by
  classical
  unfold swapFn
  by_cases ha : i ∈ A
  · rw [dite_eq_left ha]
    exact Subtype.val_injective.extend_apply _ _ ⟨i,ha⟩
  · rw [dite_eq_right ha, Function.extend_apply' _ _ i (by simpa using ha)]
    by_cases hb : i ∈ B
    · rw [dite_eq_left hb]
      exact Subtype.val_injective.extend_apply _ _ ⟨i,hb⟩
    · rw [dite_eq_right hb, Function.extend_apply' _ _ i (by simpa using hb)]
      rfl
private lemma swapFn_involutive (A B : Finset I) (hAB : Disjoint A B) (f : A ≃ B) :
    Function.Involutive (swapFn A B f) := by
  intro i
  by_cases ha : i ∈ A
  · have hb : i ∉ B := hAB.notMem_of_mem_left_finset ha
    have hfB : (f ⟨i,ha⟩).val ∈ B := Finset.coe_mem (f ⟨i,ha⟩)
    have hfA : (f ⟨i,ha⟩).val ∉ A := hAB.symm.notMem_of_mem_left_finset hfB
    simp [swapFn_apply, ha, hb, hfA, hfB]
  · by_cases hb : i ∈ B
    · have hfA : (f.symm ⟨i,hb⟩).val ∈ A := Finset.coe_mem (f.symm ⟨i,hb⟩)
      have hfB : (f.symm ⟨i,hb⟩).val ∉ B := hAB.notMem_of_mem_left_finset hfA
      simp [swapFn_apply, ha, hb, hfA, hfB]
    · simp [swapFn_apply, ha, hb]
private noncomputable def swapPerm (A B : Finset I) (hAB : Disjoint A B) (f : A ≃ B) : Equiv.Perm I :=
  Function.Involutive.toPerm (swapFn A B f) (swapFn_involutive A B hAB f)
private lemma difference_card (S T : Finset I) (h : S.card = T.card) :
    (S \ T).card = (T \ S).card := Finset.card_sdiff_comm h
private lemma differences_disjoint (S T : Finset I) : Disjoint (S \ T) (T \ S) :=
  disjoint_sdiff_sdiff
private noncomputable def exchange (S T : Finset I) (h : S.card = T.card) : Equiv.Perm I :=
  swapPerm (S \ T) (T \ S) (differences_disjoint S T) ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I)))
private lemma exchange_involutive (S T : Finset I) (h : S.card = T.card) :
    Function.Involutive (exchange S T h) := swapFn_involutive _ _ (differences_disjoint S T) _
private lemma exchange_membership (S T : Finset I) (h : S.card = T.card) (i : I) :
    exchange S T h i ∈ T ↔ i ∈ S := by
  change swapFn (S \ T) (T \ S) ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I))) i ∈ T ↔ i ∈ S
  by_cases ha : i ∈ S \ T
  · have hf := ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I)) ⟨i,ha⟩).property
    simp only [Finset.mem_sdiff] at ha hf
    simp only [exchange, swapPerm, Equiv.coe_fn_mk, swapFn_apply, dif_pos (show i ∈ S \ T from Finset.mem_sdiff.mpr ha)]
    exact iff_of_true hf.1 ha.1
  · by_cases hb : i ∈ T \ S
    · have hf := (((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I))).symm ⟨i,hb⟩).property
      have hiS := (Finset.mem_sdiff.mp hb).2
      have hfT := (Finset.mem_sdiff.mp hf).2
      simp only [exchange, swapPerm, Equiv.coe_fn_mk, swapFn_apply, dif_neg ha, dif_pos hb]
      exact iff_of_false hfT hiS
    · have hi : i ∈ T ↔ i ∈ S := by
        simp only [Finset.mem_sdiff] at ha hb
        tauto
      simpa only [exchange, swapPerm, Equiv.coe_fn_mk, swapFn_apply, dif_neg ha, dif_neg hb] using hi
private lemma exchange_cross (S T : Finset I) (h : S.card = T.card) (i : I)
    (hm : exchange S T h i ≠ i) :
    exchange S T h i ∈ S ↔ i ∉ S := by
  change swapFn (S \ T) (T \ S) ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I))) i ∈ S ↔ i ∉ S
  change swapFn (S \ T) (T \ S) ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I))) i ≠ i at hm
  by_cases ha : i ∈ S \ T
  · have hiS := (Finset.mem_sdiff.mp ha).1
    have hf := ((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I)) ⟨i,ha⟩).property
    have hfS := (Finset.mem_sdiff.mp hf).2
    simp only [exchange, swapPerm, Equiv.coe_fn_mk, swapFn_apply, dif_pos ha]
    tauto
  · by_cases hb : i ∈ T \ S
    · have hiS := (Finset.mem_sdiff.mp hb).2
      have hf := (((Fintype.equivOfCardEq (by simpa using difference_card S T h) : (S \ T : Finset I) ≃ (T \ S : Finset I))).symm ⟨i,hb⟩).property
      have hfS := (Finset.mem_sdiff.mp hf).1
      simp only [exchange, swapPerm, Equiv.coe_fn_mk, swapFn_apply, dif_neg ha, dif_pos hb]
      tauto
    · exact (hm (by simp [exchange, swapPerm, swapFn_apply, ha, hb])).elim
private lemma exchange_self (S : Finset I) : exchange S S rfl = 1 := by
  ext i
  change swapFn (S \ S) (S \ S) ((Fintype.equivOfCardEq (Fintype.card_congr' rfl) : (S \ S : Finset I) ≃ (S \ S : Finset I))) i = i
  simp [swapFn_apply]
private lemma exchange_image (S T : Finset I) (h : S.card = T.card) :
    S.image (exchange S T h) = T := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact (exchange_membership S T h j).mpr hj
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨exchange S T h i, ?_, exchange_involutive S T h i⟩
    apply (exchange_membership S T h (exchange S T h i)).mp
    simpa only [exchange_involutive S T h i] using hi
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets
open scoped Pointwise
open Equiv QuotientGroup
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [Fintype I] in
private lemma part_mk (S : Finset I) (g : Perm I) : MulAction.ofQuotientStabilizer (Perm I) S (g : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) = S.image g := rfl
omit [Fintype I] in
private lemma part_card (S : Finset I) (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) : (MulAction.ofQuotientStabilizer (Perm I) S q).card = S.card := by
  induction q using Quotient.inductionOn' with
  | h g => simp [part_mk, Finset.card_image_iff.mpr g.injective.injOn]
private noncomputable def rep (S : Finset I) (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) : Perm I :=
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange S (MulAction.ofQuotientStabilizer (Perm I) S q) (part_card S q).symm
private lemma rep_section (S : Finset I) (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) : (rep S q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) = q := by
  apply MulAction.injective_ofQuotientStabilizer (Perm I) S
  change MulAction.ofQuotientStabilizer (Perm I) S (rep S q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) = MulAction.ofQuotientStabilizer (Perm I) S q
  rw [part_mk]
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_image _ _ _
private lemma rep_involutive (S : Finset I) (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) : Function.Involutive (rep S q) :=
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_involutive _ _ _
private lemma rep_cross (S : Finset I) (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) (i : I) (h : rep S q i ≠ i) :
    rep S q i ∈ S ↔ i ∉ S := D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_cross _ _ _ _ h
private lemma rep_identity (S : Finset I) : rep S (1 : Perm I) = 1 := by
  have he : MulAction.ofQuotientStabilizer (Perm I) S (1 : Perm I) = S := by simp [part_mk]
  simp only [rep, he]
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_self S
private noncomputable def partEquiv (S : Finset I) : (Perm I ⧸ MulAction.stabilizer (Perm I) S) ≃ {T : Finset I // T.card = S.card} :=
  (MulAction.orbitEquivQuotientStabilizer (Perm I) S).symm.trans
    (Equiv.subtypeEquivRight (fun T => by
      constructor
      · rintro ⟨g, rfl⟩
        exact part_card S (g : Perm I ⧸ MulAction.stabilizer (Perm I) S)
      · intro hT
        exact ⟨D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange S T hT.symm,
          D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Swaps.exchange_image S T hT.symm⟩))
omit [DecidableEq I] in
private lemma card_parts (S : Finset I) :
    Fintype.card {T : Finset I // T.card = S.card} = (Fintype.card I).choose S.card := by
  exact Fintype.card_finset_len S.card
private lemma card_cosets (S : Finset I) : Fintype.card ((Perm I ⧸ MulAction.stabilizer (Perm I) S)) = (Fintype.card I).choose S.card := by
  rw [Fintype.card_congr (partEquiv S), card_parts]
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets

open scoped BigOperators Matrix ComplexOrder Kronecker
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Tensor
open Matrix
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
omit [DecidableEq α] [DecidableEq β] in
private lemma pt_kronecker_sandwich (A C : Matrix α α ℂ) (B D : Matrix β β ℂ)
    (Y : Matrix (α × β) (α × β) ℂ) :
    ((Matrix.of (fun (x y : α × β) => (((A ⊗ₖ B) * Y * (C ⊗ₖ D))) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) = (Cᵀ ⊗ₖ B) * ((Matrix.of (fun (x y : α × β) => (Y) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) * (Aᵀ ⊗ₖ D) := by
  ext x y
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  simp only [← Fintype.sum_prod_type' ]
  rw [← Equiv.sum_comp (((Equiv.prodProdProdComm α β α β).trans
    ((Equiv.prodComm α α).prodCongr (Equiv.refl (β × β)))).trans
    (Equiv.prodProdProdComm α α β β))]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [Equiv.prodProdProdComm, Equiv.prodCongr, Equiv.prodComm]
  ring
private lemma pt_tensor_projector (A : Matrix α α ℂ) (B : Matrix β β ℂ)
    (hA : Aᵀ = A) (Y : Matrix (α × β) (α × β) ℂ) :
    ((Matrix.of (fun (x y : α × β) => (((A ⊗ₖ B) * Y * (A ⊗ₖ B))) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) = (A ⊗ₖ B) * ((Matrix.of (fun (x y : α × β) => (Y) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) * (A ⊗ₖ B) := by
  rw [pt_kronecker_sandwich, hA]
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Tensor

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local
open Matrix Equiv MulAction
open scoped BigOperators Kronecker Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {L : Type*} [Fintype L] [DecidableEq L]
private noncomputable def R (I : Type*) [Fintype I] [DecidableEq I] (L : Type*) [Fintype L] [DecidableEq L] :
    Perm I →* Matrix (I → L) (I → L) ℂ :=
  letI : MulAction (Perm I) (I → L) := arrowAction
  ((Matrix.permMatrixHom (n := I → L) (R := ℂ)).comp
    (MulAction.toPermHom (Perm I) (I → L))).copy Q (by funext g; rfl)
private lemma R_apply (g : Perm I) (x y : I → L) :
    R I L g x y = if y = x ∘ g then 1 else 0 := by
  exact Q_apply g x y
private lemma R_star (g : Perm I) : (R I L g)ᴴ = R I L g⁻¹ := by
  exact Q_star g
private lemma avg_transpose (I : Type*) [Fintype I] [DecidableEq I] (L : Type*) [Fintype L] [DecidableEq L] :
    (Finset.expect Finset.univ (R I L))ᵀ = Finset.expect Finset.univ (R I L) := by
  have he := D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.avg_hermitian (R I L) R_star
  change (Finset.expect Finset.univ (R I L))ᴴ = _ at he
  have hr (x y : I → L) : star (Finset.expect Finset.univ (R I L) x y) = Finset.expect Finset.univ (R I L) x y := by
    simp [D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.expect_formula, Matrix.smul_apply, Matrix.sum_apply, R_apply, apply_ite star]
  ext x y
  exact (hr y x).symm.trans (congrArg (fun M => M x y) he)

omit [Fintype I] in
private lemma mem_H_iff (S : Finset I) (g : Perm I) :
    g ∈ (MulAction.stabilizer (Perm I) S) ↔ ∀ i, g i ∈ S ↔ i ∈ S :=
  MulAction.mem_stabilizer_finset
private noncomputable def color (S : Finset I) : I → Fin 2 :=
  (S : Set I).mulIndicator (fun _ => (0 : Fin 2))
private noncomputable def fiber0 (S : Finset I) : {i // color S i = 0} ≃ S :=
  Equiv.subtypeEquivRight (fun i => by simp [color])
private noncomputable def fiber1 (S : Finset I) : {i // color S i = 1} ≃ {i // i ∉ S} :=
  Equiv.subtypeEquivRight (fun i => by simp [color])
private noncomputable def split (S : Finset I) :
    (Perm S × Perm {i // i ∉ S}) ≃ (∀ b : Fin 2, Perm {i // color S i = b}) :=
  ((fiber0 S).permCongr.symm.prodCongr (fiber1 S).permCongr.symm).trans
    (piFinTwoEquiv (fun b : Fin 2 => Perm {i // color S i = b})).symm
private noncomputable def transport (S : Finset I) :
    stabilizer (Perm I)ᵈᵐᵃ (color S) ≃ stabilizer (Perm I) S :=
  Equiv.subtypeEquiv DomMulAct.mk.symm (fun g => by
    rw [DomMulAct.mem_stabilizer_iff, mem_H_iff]
    change color S ∘ (DomMulAct.mk.symm g : Perm I) = color S ↔
      ∀ i, (DomMulAct.mk.symm g : Perm I) i ∈ S ↔ i ∈ S
    simp only [funext_iff, Function.comp_apply]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ S <;> by_cases hg : (DomMulAct.mk.symm g : Perm I) i ∈ S <;>
      simp [color, hi, hg])
private noncomputable def localEquiv (S : Finset I) :
    (Perm S × Perm {i // i ∉ S}) ≃ stabilizer (Perm I) S :=
  (((split S).trans (DomMulAct.stabilizerMulEquiv (color S)).toEquiv.symm).trans
    (MulOpposite.opEquiv : stabilizer (Perm I)ᵈᵐᵃ (color S) ≃
      (stabilizer (Perm I)ᵈᵐᵃ (color S))ᵐᵒᵖ).symm).trans (transport S)
omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma split_comp (S : Finset I) (a : Perm S) (b : Perm {i // i ∉ S}) (x : I → L) :
    (Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)) (x ∘ a.subtypeCongr b) = (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)) x).1 ∘ a,((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)) x).2 ∘ b) := by
  apply Prod.ext <;> funext i
  · change x ((a.subtypeCongr b) i) = x (a i)
    rw [Perm.subtypeCongr.left_apply a b i.2]
  · change x ((a.subtypeCongr b) i) = x (b i)
    rw [Perm.subtypeCongr.right_apply a b i.2]
private lemma R_local_tensor (S : Finset I) (a : Perm S) (b : Perm {i // i ∉ S}) :
    (R I L (a.subtypeCongr b)).submatrix ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm =
      R S L a ⊗ₖ R {i // i ∉ S} L b := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, R_apply]
  have he : ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm y = ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm x ∘ a.subtypeCongr b ↔
      y.1 = x.1 ∘ a ∧ y.2 = x.2 ∘ b := by
    rw [← ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).injective.eq_iff, split_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Prod.mk.injEq]
  simp only [he]
  split_ifs <;> simp_all

noncomputable def localP (S : Finset I) : Matrix (I → L) (I → L) ℂ :=
  Finset.expect Finset.univ (fun g : MulAction.stabilizer (Perm I) S => Q (L := L) g.val)
private lemma localP_tensor (S : Finset I) :
    (localP (L := L) S).submatrix ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm =
      Finset.expect Finset.univ (R S L) ⊗ₖ Finset.expect Finset.univ (R {i // i ∉ S} L) := by
  have hc : Fintype.card ((MulAction.stabilizer (Perm I) S)) =
      Fintype.card (Perm S) * Fintype.card (Perm {i // i ∉ S}) := by
    rw [← Fintype.card_prod]
    exact (Fintype.card_congr (localEquiv S)).symm
  change (Finset.expect Finset.univ ((R I L).comp (MulAction.stabilizer (Perm I) S).subtype)).submatrix _ _ = _
  ext x y
  have ht (a : Perm S) (b : Perm {i // i ∉ S}) :
      R I L (a.subtypeCongr b) (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm x) (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm y) =
        R S L a x.1 y.1 * R {i // i ∉ S} L b x.2 y.2 :=
    congrArg (fun M => M x y) (R_local_tensor S a b)
  simp only [localP, D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.expect_formula, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.sum_apply, MonoidHom.comp_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
  rw [← Equiv.sum_comp (localEquiv S)]
  simp only [Fintype.sum_prod_type]
  have hv (a : Perm S) (b : Perm {i // i ∉ S}) :
      ((localEquiv S) (a,b) : Perm I) = a.subtypeCongr b := by
    ext i
    change DomMulAct.stabilizerEquiv_invFun (split S (a,b)) i = (a.subtypeCongr b) i
    by_cases hi : i ∈ S
    · rw [DomMulAct.stabilizerEquiv_invFun_eq _ (show color S i = 0 by simp [color, hi])]
      rw [Perm.subtypeCongr.left_apply a b hi]
      rfl
    · rw [DomMulAct.stabilizerEquiv_invFun_eq _ (show color S i = 1 by simp [color, hi])]
      rw [Perm.subtypeCongr.right_apply a b hi]
      rfl
  simp only [Subgroup.subtype_apply, hv, ht, hc, Nat.cast_mul, mul_inv]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open Matrix Equiv
open scoped BigOperators Kronecker Pointwise
attribute [local instance] Classical.propDecidable
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
private lemma R_eq_Q (g : Perm I) : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R I L g = Q g := by
  exact Matrix.ext fun i => congrFun rfl
private lemma P_eq_avg_R : P I L = Finset.expect Finset.univ (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R I L) := by
  exact Matrix.ext fun i => congrFun rfl
lemma PiS_hermitian (S : Finset I) : (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP (L := L) S).IsHermitian := by
  change (Finset.expect Finset.univ ((D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R I L).comp ((MulAction.stabilizer (Perm I) S)).subtype)).IsHermitian
  apply D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.avg_hermitian
  intro g
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R_star g.val
lemma PiS_idempotent (S : Finset I) : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP (L := L) S * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S = D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
  unfold D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.avg_idempotent ((Local.R I L).comp (MulAction.stabilizer (Perm I) S).subtype)
lemma PiS_psd (S : Finset I) : (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP (L := L) S).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP (L := L) S)
  rwa [PiS_hermitian S, PiS_idempotent S] at h
lemma PiS_mul_P (S : Finset I) : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * P I L = P I L := by
  rw [P_eq_avg_R (I := I) (L := L)]
  unfold D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.subgroup_avg_left (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R I L) ((MulAction.stabilizer (Perm I) S))
omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma pt_split (S : Finset I) (Y : Matrix (I → L) (I → L) ℂ) :
    (partialTransposeOn S Y).submatrix ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm =
      (fun (x y : ({i // i ∈ S} → L) × ({i // i ∉ S} → L)) => ((Y.submatrix ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm)) (y.1, x.2) (x.1, y.2)) := by
  ext x y
  change Y (S.piecewise (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm y) (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm x))
    (S.piecewise (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm x) (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm y)) =
      Y (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm (y.1,x.2)) (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm (x.1,y.2))
  congr 1 <;> funext i <;> by_cases hi : i ∈ S <;>
    simp [Equiv.piEquivPiSubtypeProd, Finset.piecewise, hi]
lemma partialTranspose_PiS_sandwich (S : Finset I)
    (Y : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S) = D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * partialTransposeOn S Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
  let e := ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm
  have hm (A B : Matrix (I → L) (I → L) ℂ) :
      (A*B).submatrix e e = A.submatrix e e * B.submatrix e e :=
    (Matrix.submatrix_mul_equiv A B e e e).symm
  have ht : (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP (L := L) S).submatrix e e =
      Finset.expect Finset.univ (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R S L) ⊗ₖ Finset.expect Finset.univ (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R {i // i ∉ S} L) :=
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP_tensor S
  apply Matrix.submatrix_injective e.surjective e.surjective
  change (partialTransposeOn S (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S)).submatrix e e =
    (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * partialTransposeOn S Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S).submatrix e e
  rw [show (partialTransposeOn S (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S)).submatrix e e =
    (fun (x y : ({i // i ∈ S} → L) × ({i // i ∉ S} → L)) => (((D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * Y * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S).submatrix e e)) (y.1, x.2) (x.1, y.2)) from pt_split S _]
  rw [hm,hm,hm,hm,ht]
  rw [show (partialTransposeOn S Y).submatrix e e = (fun (x y : ({i // i ∈ S} → L) × ({i // i ∉ S} → L)) => ((Y.submatrix e e)) (y.1, x.2) (x.1, y.2)) from pt_split S Y]
  exact D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Tensor.pt_tensor_projector _ _ (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.avg_transpose _ _) _

private lemma P_coset_expansion (S : Finset I) :
    P I L = (((Fintype.card I).choose S.card : ℂ)⁻¹) •
      ∑ q : (Perm I ⧸ MulAction.stabilizer (Perm I) S), Q (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S q) * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
  have h := D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Average.avg_section (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.R I L) ((MulAction.stabilizer (Perm I) S))
    (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S) (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep_section S)
  have hc : Fintype.card (Perm I ⧸ (MulAction.stabilizer (Perm I) S)) = (Fintype.card I).choose S.card :=
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.card_cosets S
  rw [hc] at h
  unfold D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP
  simpa only [P_eq_avg_R (I := I) (L := L), Local.localP, MonoidHom.comp_apply, Subgroup.subtype_apply, R_eq_Q (I := I) (L := L)] using h
omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma partialTranspose_smulC (S : Finset I) (a : ℂ)
    (Y : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (a • Y) = a • partialTransposeOn S Y := rfl
omit [Fintype L] in
private lemma partialTranspose_one (S : Finset I) :
    partialTransposeOn S (1 : Matrix (I → L) (I → L) ℂ) = 1 := by
  ext x y
  simp only [partialTransposeOn, Matrix.one_apply]
  have he : S.piecewise y x = S.piecewise x y ↔ x = y := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      by_cases hs : i ∈ S
      · simpa [Finset.piecewise, hs] using hi.symm
      · simpa [Finset.piecewise, hs] using hi
    · rintro rfl; rfl
  simp only [he]
private lemma P_partialTranspose_cosets (S : Finset I) :
    partialTransposeOn S (P I L) = ((Fintype.card I).choose S.card : ℂ)⁻¹ •
      ∑ q : (Perm I ⧸ MulAction.stabilizer (Perm I) S), D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * partialTransposeOn S (Q (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S q)) * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
  have h : P I L = ((Fintype.card I).choose S.card : ℂ)⁻¹ •
      ∑ q : (Perm I ⧸ MulAction.stabilizer (Perm I) S), D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * Q (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S q) * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
    calc
      P I L = D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * P I L := (PiS_mul_P S).symm
      _ = _ := by rw [P_coset_expansion S, Matrix.mul_smul, Matrix.mul_sum]; simp only [Matrix.mul_assoc]
  rw [h, partialTranspose_smulC, partialTranspose_sum]
  apply congrArg (fun A : Matrix (I → L) (I → L) ℂ => ((Fintype.card I).choose S.card : ℂ)⁻¹ • A)
  apply Finset.sum_congr rfl
  intro q _
  exact partialTranspose_PiS_sandwich S _
lemma symmetrizer_partialTranspose_floor (S : Finset I) :
    (partialTransposeOn S (P I L) - ((Fintype.card I).choose S.card : ℂ)⁻¹ • D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S).PosSemidef := by
  let F (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) := D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * partialTransposeOn S (Q (L := L) (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S q)) * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S
  let q0 : (Perm I ⧸ MulAction.stabilizer (Perm I) S) := (1 : Perm I)
  have hF (q : (Perm I ⧸ MulAction.stabilizer (Perm I) S)) : (F q).PosSemidef := by
    have h := (cross_partialTranspose_psd (L := L) S (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep S q)
      (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep_involutive S q) (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep_cross S q)).conjTranspose_mul_mul_same (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S)
    simpa only [F, (PiS_hermitian (L := L) S).eq] using h
  have h0 : F q0 = D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S := by
    simp only [F, q0, D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Cosets.rep_identity, Q_one, partialTranspose_one,
      Matrix.mul_one, PiS_idempotent]
  have hs := (Matrix.posSemidef_sum (Finset.univ.erase q0) (fun q _ => hF q)).smul
    (show (0 : ℂ) ≤ ((Fintype.card I).choose S.card : ℂ)⁻¹ by positivity)
  rw [P_partialTranspose_cosets]
  change ((((Fintype.card I).choose S.card : ℂ)⁻¹) • ∑ q, F q - _).PosSemidef
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ q0)] at hs
  simpa only [h0, smul_sub] using hs
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
