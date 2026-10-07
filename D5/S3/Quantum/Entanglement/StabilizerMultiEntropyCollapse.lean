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
  partition_count: proof_shape: bind-only; escape_witness: none.
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
  result: proof_shape: bind-only; escape_witness: none.
    consumer: none (terminal settlement).
    admission_basis: open-problem-resolution (#13575; Proved).
Utility: none. The declarations give general mathematical identities and constructions;
fixed field and mode checks occur only inside parameterized proofs. No declaration
is an instance certificate, bounded enumeration result, checker or numeric reduction.
Direct frozen dependencies:
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.F₂
    statement_id: sha256:e975fc48104d0cb1a40271fdfb5ec7fcfe2730a1c600ee81758d5e89253bd60f
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign.eq_1
    statement_id: sha256:47b1c4360f7294d639daaa81a4dc00aa903f52ef7b53aeca8f2a321008db2233
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result._simp_1_2
    statement_id: sha256:b6d398a580b6082cdf28a5f507b45bd399f1ae7037e5a5319384011b96fc19a3
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result._simp_1_4
    statement_id: sha256:2eef85eac594a0afbcfd3444522525aacba24337dc294a1cf3f33407694d1fea
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
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.result._simp_1_2]
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
    D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.result._simp_1_4,
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

set_option maxHeartbeats 2000000 in
-- The 13 modes and six four-mode mergers expand into partition coefficients.
/-- The four-party counting relation holds for every function of the party partition. -/
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
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  simp (disch := decide) only [partitionSum.eq_1, modes1.eq_1, modes2.eq_1, modes3.eq_1,
    Finset.sum_insert, Finset.sum_singleton]
  norm_num [colourValue.eq_1, cutPattern, Fin.sum_univ_succ, Function.comp_def,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    h02, h12, Ne.symm h02, Ne.symm h12]
  ring

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
