/- GID: D5/S3/Quantum/Entanglement/ReplicaPartitionLocalInvariance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ReplicaPartitionLocalInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Replica contractions are invariant under identical local unitaries and a unit phase. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.ReplicaPartitionLocalInvariance

open Matrix D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

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

private def replicaOp {R : Type*} [Fintype R] [DecidableEq R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (R → Fin N → Fin 2) (R → Fin N → Fin 2) ℂ :=
  fun x y => ∏ r, ∏ u, U u (x r u) (y r u)

private lemma replica_expand {R : Type*} [Fintype R] [DecidableEq R] {N : ℕ}
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : (Fin N → Fin 2) → ℂ) (x : R → Fin N → Fin 2) :
    (∏ r, (tensorOp U *ᵥ ψ) (x r)) =
      (replicaOp (R := R) U *ᵥ fun y => ∏ r, ψ (y r)) x := by
  classical
  simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply, replicaOp]
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
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
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

/-- Applying the same local unitaries to all replicas preserves the contraction. -/
theorem Z_local_unitary_phase : ∀ (n q : ℕ) [NeZero n] {N : ℕ}
    (col : Fin N → Fin q) (ψ : (Fin N → Fin 2) → ℂ)
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ),
    (∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) → ‖z‖ = 1 →
    Z n q col (z • (tensorOp U *ᵥ ψ)) = Z n q col ψ := by
  sorry

end D5.S3.Quantum.Entanglement.ReplicaPartitionLocalInvariance
