/- GID: D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.claim; result=D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result; claim=D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.claim
   digest: Refutes Song–Lin, arXiv:2608.10643v1, Conjecture 4.1: on the connected oriented circulant graph G(Z_30, {5, 6, 9, 20}) the continuous-time quantum walk has zero transfer between 0 and the even vertex 2. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the vanishing of the (0, 2) and
  (2, 0) entries of every power of the skew adjacency matrix is produced on its live proof path by
  the degree-seven row recurrence `hrec` (from seven exact row products) and strong induction
  `hzero`, transferred by skew-symmetry `hzero'`, and carried through the exponential series `hexp`
admission_basis: open-problem-resolution (issue #10142)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  (statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb) and
  .hamiltonianGenerator (statement_id
  sha256:4c0ebd78b0aa0a551d6207706ae2d39b87a3d18687dc8dcb29e00bd4e58a735a)
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer

open scoped BigOperators Nat
open Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-!
Song–Lin, *Zero transfer on mixed graphs*, arXiv:2608.10643v1, §4, Conjecture 4.1: for a
(connected) oriented circulant graph `G(ℤ_n, C)` with `n ≡ 2 (mod 4)`, if zero transfer occurs
between a vertex `v` and `0`, then `v` is odd. The Hermitian adjacency matrix has entry `i` on
arcs `a → b` (`b - a ∈ C`), `-i` on reversed arcs and `0` elsewhere; the transition matrix
`U(t) = exp(-i t H)` is the propagator `hamiltonianPropagator H t = exp (t • (-i) • H)` of
`D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow`; zero transfer from `u` to `v` means
`U(t)_{u,v} = 0` for every `t ≥ 0`.
For `n = 30`, `C = {5, 6, 9, 20}` and `v = 2`, every power of `H` has vanishing `(0, 2)` and
`(2, 0)` entries, so zero transfer occurs between `0` and the even vertex `2`.
-/

/-- The Hermitian adjacency matrix of the circulant graph `G(ℤ_n, C)` with arcs `a → b` for
`b - a ∈ C`, when `C ∩ -C = ∅`. -/
def hermAdj (n : ℕ) (C : Finset (ZMod n)) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun a b => if b - a ∈ C then I else if a - b ∈ C then -I else 0

/-- Zero transfer from `u` to `v`: the entry `U(t)_{u,v}` of the transition matrix
`U(t) = exp(-i t H)` vanishes for every time `t ≥ 0`. -/
def ZeroTransfer (n : ℕ) [NeZero n] (C : Finset (ZMod n)) (u v : ZMod n) : Prop :=
  ∀ t : ℝ, 0 ≤ t → hamiltonianPropagator (hermAdj n C) t u v = 0

/-- The connection set lies in `ℤ_n ∖ {0}` and is disjoint from its negation. -/
def Oriented {n : ℕ} (C : Finset (ZMod n)) : Prop :=
  (0 : ZMod n) ∉ C ∧ ∀ c ∈ C, -c ∉ C

/-- The underlying undirected graph of `G(ℤ_n, C)` is connected. -/
def Connected {n : ℕ} (C : Finset (ZMod n)) : Prop :=
  (SimpleGraph.fromRel fun a b : ZMod n => b - a ∈ C).Connected

/-- Conjecture 4.1 of arXiv:2608.10643v1, with zero transfer between `v` and `0` read in both
directions. -/
def claim : Prop :=
  ∀ (n : ℕ) [NeZero n], n % 4 = 2 → ∀ C : Finset (ZMod n), Oriented C → Connected C →
    ∀ v : ZMod n, ZeroTransfer n C v 0 ∧ ZeroTransfer n C 0 v → Odd v.val

/-- On `G(ℤ_30, {5, 6, 9, 20})` the `(0, 2)` entries of the powers of the integer skew adjacency
matrix `S = -i H` vanish: the rows `r_k` of `S^k` at `0` satisfy `r_k(2) = 0` for `k ≤ 6` and
`r_7 = -32 r_5 - 320 r_3 - 960 r_1`, and skew-symmetry transfers this to the `(2, 0)` entries.
The exponential series then has vanishing `(0, 2)` and `(2, 0)` entries at every time. -/
theorem result : ¬ claim := by
  intro h
  set C : Finset (ZMod 30) := {5, 6, 9, 20} with hC
  set S : Matrix (ZMod 30) (ZMod 30) ℤ :=
    Matrix.of fun a b => if b - a ∈ C then 1 else if a - b ∈ C then -1 else 0 with hS
  -- rows of the powers of `S` at vertex `0`
  have hrow : ∀ k : ℕ, (fun j => (S ^ (k + 1)) 0 j) = S.vecMulLinear fun j => (S ^ k) 0 j := by
    intro k
    funext j
    rw [pow_succ, Matrix.mul_apply, Matrix.vecMulLinear_apply]
    rfl
  have r0 : (fun j => (S ^ 0) 0 j) = fun j : ZMod 30 =>
      ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0] : List ℤ).getD j.val 0 := by
    rw [pow_zero]; decide +kernel
  have r1 : (fun j => (S ^ 1) 0 j) = fun j : ZMod 30 =>
      ([0, 0, 0, 0, 0, 1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, -1, 0, 0, 0,
        0] : List ℤ).getD j.val 0 := by
    rw [hrow, r0]; decide +kernel
  have r2 : (fun j => (S ^ 2) 0 j) = fun j : ZMod 30 =>
      ([-8, 0, 0, -2, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, -2, 0,
        0] : List ℤ).getD j.val 0 := by
    rw [hrow, r1]; decide +kernel
  have r3 : (fun j => (S ^ 3) 0 j) = fun j : ZMod 30 =>
      ([0, 0, 0, -4, 0, -12, -12, 0, 0, -12, 12, 0, -4, 0, 0, 0, 0, 0, 4, 0, -12, 12, 0, 0, 12,
        12, 0, 4, 0, 0] : List ℤ).getD j.val 0 := by
    rw [hrow, r2]; decide +kernel
  have r4 : (fun j => (S ^ 4) 0 j) = fun j : ZMod 30 =>
      ([96, 0, 0, 32, 0, -24, 8, 0, 0, -8, -24, 0, -32, 0, 0, 0, 0, 0, -32, 0, -24, -8, 0, 0, 8,
        -24, 0, 32, 0, 0] : List ℤ).getD j.val 0 := by
    rw [hrow, r3]; decide +kernel
  have r5 : (fun j => (S ^ 5) 0 j) = fun j : ZMod 30 =>
      ([0, 0, 0, 80, 0, 144, 160, 0, 0, 160, -144, 0, 80, 0, 0, 0, 0, 0, -80, 0, 144, -160, 0, 0,
        -160, -144, 0, -80, 0, 0] : List ℤ).getD j.val 0 := by
    rw [hrow, r4]; decide +kernel
  have r6 : (fun j => (S ^ 6) 0 j) = fun j : ZMod 30 =>
      ([-1216, 0, 0, -480, 0, 288, -160, 0, 0, 160, 288, 0, 480, 0, 0, 64, 0, 0, 480, 0, 288, 160,
        0, 0, -160, 288, 0, -480, 0, 0] : List ℤ).getD j.val 0 := by
    rw [hrow, r5]; decide +kernel
  have r7 : (fun j => (S ^ 7) 0 j) = fun j : ZMod 30 =>
      ([0, 0, 0, -1280, 0, -1728, -2240, 0, 0, -2240, 1728, 0, -1280, 0, 0, 0, 0, 0, 1280, 0,
        -1728, 2240, 0, 0, 2240, 1728, 0, 1280, 0, 0] : List ℤ).getD j.val 0 := by
    rw [hrow, r6]; decide +kernel
  -- the degree-seven linear recurrence of the rows
  have hrec : ∀ k : ℕ, (fun j => (S ^ (k + 7)) 0 j) =
      (-32 : ℤ) • (fun j => (S ^ (k + 5)) 0 j) - (320 : ℤ) • (fun j => (S ^ (k + 3)) 0 j) -
        (960 : ℤ) • (fun j => (S ^ (k + 1)) 0 j) := by
    intro k
    induction k with
    | zero => rw [r7, r5, r3, r1]; decide +kernel
    | succ k ih =>
      rw [show k + 1 + 7 = (k + 7) + 1 by omega, show k + 1 + 5 = (k + 5) + 1 by omega,
        show k + 1 + 3 = (k + 3) + 1 by omega, hrow (k + 7), hrow (k + 5), hrow (k + 3),
        hrow (k + 1), ih, map_sub, map_sub, map_smul, map_smul, map_smul]
  have hzero : ∀ k : ℕ, (S ^ k) 0 2 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < 7
      · interval_cases k
        · exact (congrFun r0 2).trans rfl
        · exact (congrFun r1 2).trans rfl
        · exact (congrFun r2 2).trans rfl
        · exact (congrFun r3 2).trans rfl
        · exact (congrFun r4 2).trans rfl
        · exact (congrFun r5 2).trans rfl
        · exact (congrFun r6 2).trans rfl
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
        have e := congrFun (hrec m) 2
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
        rw [e, ih (m + 5) (by omega), ih (m + 3) (by omega), ih (m + 1) (by omega)]
        ring
  have hskew : S.transpose = -S := by decide +kernel
  have hzero' : ∀ k : ℕ, (S ^ k) 2 0 = 0 := by
    intro k
    have e : (S ^ k) 2 0 = ((-S) ^ k) 0 2 := by
      rw [← hskew, ← Matrix.transpose_pow, Matrix.transpose_apply]
    rw [e]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_pow, hzero]
    · rw [hk.neg_pow, Matrix.neg_apply, hzero, neg_zero]
  -- the Hermitian adjacency matrix is `i` times the cast of `S`
  have hH : hermAdj 30 C = I • (Int.castRingHom ℂ).mapMatrix S := by
    ext a b
    simp only [hermAdj, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, hS, smul_eq_mul]
    split_ifs <;> simp
  -- entries of the exponential series
  have hexp : ∀ (X : Matrix (ZMod 30) (ZMod 30) ℂ) (a b : ZMod 30),
      (∀ k : ℕ, (X ^ k) a b = 0) → NormedSpace.exp X a b = 0 := by
    intro X a b hX
    rw [NormedSpace.exp_eq_tsum ℂ]
    show (∑' k : ℕ, ((k ! : ℂ)⁻¹) • X ^ k) a b = 0
    by_cases hs : Summable fun k : ℕ => ((k ! : ℂ)⁻¹) • X ^ k
    · have h2 : HasSum (fun k : ℕ => (((k ! : ℂ)⁻¹) • X ^ k) a b)
          ((∑' k : ℕ, ((k ! : ℂ)⁻¹) • X ^ k) a b) :=
        Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum a) b
      have h3 : (fun k : ℕ => (((k ! : ℂ)⁻¹) • X ^ k) a b) = fun _ => 0 := by
        funext k
        rw [Matrix.smul_apply, hX, smul_zero]
      rw [h3] at h2
      exact h2.unique hasSum_zero
    · rw [tsum_eq_zero_of_not_summable hs]
      rfl
  have hpow : ∀ (c : ℂ) (k : ℕ) (a b : ZMod 30), (S ^ k) a b = 0 →
      ((c • hermAdj 30 C) ^ k) a b = 0 := by
    intro c k a b hab
    rw [hH, smul_pow, smul_pow, ← map_pow, Matrix.smul_apply, Matrix.smul_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, hab]
    simp
  have hor : Oriented C := by
    refine ⟨by decide, ?_⟩
    decide
  have hcon : Connected C := by
    have step : ∀ a : ZMod 30,
        (SimpleGraph.fromRel fun a b : ZMod 30 => b - a ∈ C).Reachable a (a + 1) := by
      intro a
      have h1 : (SimpleGraph.fromRel fun a b : ZMod 30 => b - a ∈ C).Adj a (a + 6) := by
        rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ?_⟩
        · intro e
          have : (6 : ZMod 30) = 0 := by linear_combination -e
          exact absurd this (by decide)
        · rw [show a + 6 - a = 6 by ring]; decide
      have h2 : (SimpleGraph.fromRel fun a b : ZMod 30 => b - a ∈ C).Adj (a + 6) (a + 1) := by
        rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inr ?_⟩
        · intro e
          have : (5 : ZMod 30) = 0 := by linear_combination e
          exact absurd this (by decide)
        · rw [show a + 6 - (a + 1) = 5 by ring]; decide
      exact h1.reachable.trans h2.reachable
    have reach : ∀ k : ℕ,
        (SimpleGraph.fromRel fun a b : ZMod 30 => b - a ∈ C).Reachable 0 (k : ZMod 30) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => exact ih.trans (by simpa using step (k : ZMod 30))
    refine ⟨fun u v => ?_⟩
    rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
    exact (reach u.val).symm.trans (reach v.val)
  have hU : ∀ (t : ℝ) (a b : ZMod 30), (∀ k : ℕ, (S ^ k) a b = 0) →
      hamiltonianPropagator (hermAdj 30 C) t a b = 0 := by
    intro t a b hab
    have e : t • hamiltonianGenerator (hermAdj 30 C) = ((t : ℂ) * (-I)) • hermAdj 30 C := by
      rw [hamiltonianGenerator, ← smul_smul, Complex.coe_smul]
    show NormedSpace.exp (t • hamiltonianGenerator (hermAdj 30 C)) a b = 0
    rw [e]
    exact hexp _ a b fun k => hpow _ k a b (hab k)
  have hzt : ZeroTransfer 30 C 2 0 ∧ ZeroTransfer 30 C 0 2 :=
    ⟨fun t _ => hU t 2 0 hzero', fun t _ => hU t 0 2 hzero⟩
  have hodd := h 30 (by norm_num) C hor hcon 2 hzt
  exact absurd hodd (by decide)

#print axioms claim
#print axioms result

end D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
