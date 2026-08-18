/- GID: D5/S3/Quantum/Tomography/RankOneContextCommutator
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/RankOneContextCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete rank-one contexts satisfy the aggregate projection commutator formula. -/

import Mathlib

/- Library-search audit trail (2026-08-18):
   * Repository searches found rank-one density, projection, Frobenius, and generic commutator
     declarations, but no aggregate rank-one context commutator theorem.
   * Pinned-Mathlib source search found the exact support declarations
     `Matrix.trace_conjTranspose`, `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle`,
     `Matrix.trace_sum`, and `Matrix.trace_smul`; they are applied below.
   * Pinned-Mathlib searches for the complete double-sum identity were a miss. -/

open scoped BigOperators

noncomputable section

namespace D5.S3.Quantum.Tomography.RankOneContextCommutator

open Matrix

/-- Algebraic characterization of a normalized rank-one complex projection. -/
def IsNormalizedRankOneProjection {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) : Prop :=
  Pᴴ = P ∧
    P * P = P ∧
    trace P = 1 ∧
    ∀ X : Matrix n n ℂ, P * X * P = trace (P * X) • P

/-- A complete rank-one projective context in dimension `d`. -/
structure RankOneContext (d : Nat) where
  projector : Fin d -> Matrix (Fin d) (Fin d) ℂ
  rankOne : ∀ j, IsNormalizedRankOneProjection (projector j)
  resolvesIdentity : ∑ j, projector j = 1

/-- The squared Hilbert--Schmidt norm, expressed by its trace formula. -/
def hilbertSchmidtSquare {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : ℝ :=
  (trace (Aᴴ * A)).re

/-- The real trace overlap of two context projections. -/
def overlap {d : Nat} (B C : RankOneContext d) (j k : Fin d) : ℝ :=
  (trace (B.projector j * C.projector k)).re

/-- Normalized incompatibility of two complete rank-one contexts. -/
def incompatibility {d : Nat} (B C : RankOneContext d) : ℝ :=
  ((d : ℝ) - ∑ j, ∑ k, overlap B C j k ^ 2) / ((d : ℝ) - 1)

private theorem trace_overlap_is_real {n : Type*} [Fintype n]
    {P Q : Matrix n n ℂ}
    (hP : IsNormalizedRankOneProjection P)
    (hQ : IsNormalizedRankOneProjection Q) :
    (trace (P * Q)).im = 0 := by
  have hstar : star (trace (P * Q)) = trace (P * Q) := by
    calc
      star (trace (P * Q)) = trace ((P * Q)ᴴ) :=
        (trace_conjTranspose (P * Q)).symm
      _ = trace (Q * P) := by rw [conjTranspose_mul, hP.1, hQ.1]
      _ = trace (P * Q) := trace_mul_comm Q P
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

private theorem rank_one_commutator_square {n : Type*} [Fintype n]
    {P Q : Matrix n n ℂ}
    (hP : IsNormalizedRankOneProjection P)
    (hQ : IsNormalizedRankOneProjection Q) :
    hilbertSchmidtSquare (P * Q - Q * P) =
      2 * (trace (P * Q)).re * (1 - (trace (P * Q)).re) := by
  let m : ℂ := trace (P * Q)
  have hmIm : m.im = 0 := trace_overlap_is_real hP hQ
  have hPQP : P * Q * P = m • P := hP.2.2.2 Q
  have hQPQ : Q * P * Q = trace (Q * P) • Q := hQ.2.2.2 P
  have htraceQP : trace (Q * P) = m := trace_mul_comm Q P
  have hPQPQ : trace (P * Q * P * Q) = m ^ 2 := by
    rw [show P * Q * P * Q = (P * Q * P) * Q by noncomm_ring, hPQP,
      smul_mul, trace_smul]
    simp only [smul_eq_mul, m]
    ring
  have hQPQP : trace (Q * P * Q * P) = m ^ 2 := by
    calc
      trace (Q * P * Q * P) = trace (P * Q * P * Q) := by
        simpa only [Matrix.mul_assoc] using trace_mul_comm Q (P * Q * P)
      _ = m ^ 2 := hPQPQ
  have htraceQPQ : trace (Q * P * Q) = m := by
    rw [hQPQ, trace_smul, hQ.2.2.1, htraceQP]
    simp
  have htracePQP : trace (P * Q * P) = m := by
    rw [hPQP, trace_smul, hP.2.2.1]
    simp
  have hstarComm : (P * Q - Q * P)ᴴ = Q * P - P * Q := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hP.1, hQ.1]
  have hproduct :
      (Q * P - P * Q) * (P * Q - Q * P) =
        Q * P * Q + P * Q * P - Q * P * Q * P - P * Q * P * Q := by
    have hQPPQ : Q * P * P * Q = Q * P * Q := by
      rw [Matrix.mul_assoc Q P P, hP.2.1]
    have hPQQP : P * Q * Q * P = P * Q * P := by
      rw [Matrix.mul_assoc P Q Q, hQ.2.1]
    calc
      (Q * P - P * Q) * (P * Q - Q * P) =
          Q * P * P * Q - Q * P * Q * P - P * Q * P * Q + P * Q * Q * P := by
        noncomm_ring
      _ = Q * P * Q + P * Q * P - Q * P * Q * P - P * Q * P * Q := by
        rw [hQPPQ, hPQQP]
        noncomm_ring
  rw [hilbertSchmidtSquare, hstarComm, hproduct]
  simp only [trace_sub, trace_add, htraceQPQ, htracePQP, hQPQP, hPQPQ]
  change (m + m - m ^ 2 - m ^ 2).re = 2 * m.re * (1 - m.re)
  have hmSq : (m ^ 2).re = m.re ^ 2 := by
    rw [pow_two]
    simp only [Complex.mul_re, hmIm, mul_zero, sub_zero]
    ring
  simp only [Complex.add_re, Complex.sub_re, hmSq]
  ring

private theorem overlap_sum {d : Nat} (B C : RankOneContext d) :
    ∑ j, ∑ k, overlap B C j k = d := by
  have hcomplex :
      ∑ j, ∑ k, trace (B.projector j * C.projector k) = (d : ℂ) := by
    calc
      ∑ j, ∑ k, trace (B.projector j * C.projector k) =
          trace (∑ j, ∑ k, B.projector j * C.projector k) := by simp
      _ = trace ((∑ j, B.projector j) * (∑ k, C.projector k)) := by
        congr 1
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = (d : ℂ) := by rw [B.resolvesIdentity, C.resolvesIdentity]; simp
  have hreal := congrArg Complex.re hcomplex
  have hcast : ((d : ℂ)).re = (d : ℝ) := by norm_num
  rw [hcast] at hreal
  simpa only [overlap, Complex.re_sum] using hreal

/-- The sum of squared Hilbert--Schmidt commutators of two complete normalized rank-one
contexts is twice their normalized incompatibility times `d - 1`. -/
theorem aggregated_rank_one_context_commutator {d : Nat} (hd : 2 ≤ d)
    (B C : RankOneContext d) :
    ∑ j, ∑ k,
        hilbertSchmidtSquare (B.projector j * C.projector k -
          C.projector k * B.projector j) =
      2 * ((d : ℝ) - 1) * incompatibility B C := by
  have hoverlap := overlap_sum B C
  have hdcast : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have hdim : (0 : ℝ) < (d : ℝ) - 1 := sub_pos.mpr hdcast
  calc
    ∑ j, ∑ k,
        hilbertSchmidtSquare (B.projector j * C.projector k -
          C.projector k * B.projector j) =
        ∑ j, ∑ k, 2 * overlap B C j k * (1 - overlap B C j k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact rank_one_commutator_square (B.rankOne j) (C.rankOne k)
    _ = 2 * ((d : ℝ) - ∑ j, ∑ k, overlap B C j k ^ 2) := by
      rw [← hoverlap]
      simp_rw [show ∀ x : ℝ, 2 * x * (1 - x) = 2 * x - 2 * x ^ 2 by
        intro x; ring]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = 2 * ((d : ℝ) - 1) * incompatibility B C := by
      rw [incompatibility]
      field_simp [ne_of_gt hdim]

#print axioms aggregated_rank_one_context_commutator

end D5.S3.Quantum.Tomography.RankOneContextCommutator
