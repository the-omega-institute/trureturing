/- GID: D5/S3/QuantumContext/CompleteBasisReconstruction
   generality: G
   mirror-B: D5/B/S3/QuantumContext/CompleteBasisReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete complementary basis probabilities reconstruct a trace-one matrix. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Repository searches for complete mutually unbiased basis reconstruction,
     informationally complete projectors, and the displayed double-sum formula
     found no equivalent theorem. The adjacent probability Pythagoras module
     proves a norm decomposition, not matrix reconstruction.
   * Pinned Mathlib searches found no packaged mutually unbiased basis or state
     reconstruction theorem. Exact algebraic hits `Matrix.mul_sum`,
     `Matrix.sum_mul`, `Matrix.trace_sum`, and `Matrix.trace_smul` are applied
     below to evaluate the proposed reconstruction against every projector.
   * `Matrix.ext_iff_trace_mul_right` gives full trace-pairing extensionality,
     but does not encode completeness of the selected projector family. -/

open scoped BigOperators

namespace D5.S3.QuantumContext.CompleteBasisReconstruction

universe u v

/-- A trace-one matrix is recovered from its probabilities in a complete family
of pairwise complementary projective bases. Completeness is expressed by the
fact that equality of all selected projector traces determines a matrix. -/
theorem complete_basis_reconstruction
    {d : Type u} {L : Type v} [Fintype d] [Nonempty d]
    [DecidableEq d] [Fintype L] [DecidableEq L]
    (rho : Matrix d d ℂ) (projector : L -> d -> Matrix d d ℂ)
    (probability : L -> d -> ℝ)
    (hrho : Matrix.trace rho = 1)
    (hprobability : forall l j,
      (probability l j : ℂ) = Matrix.trace (rho * projector l j))
    (hresolution : forall l, ∑ j, projector l j = 1)
    (hoverlap : forall l k j r,
      Matrix.trace (projector l j * projector k r) =
        if l = k then (if j = r then 1 else 0)
        else (Fintype.card d : ℂ)⁻¹)
    (hcomplete : forall X Y : Matrix d d ℂ,
      (forall l j,
        Matrix.trace (X * projector l j) = Matrix.trace (Y * projector l j)) ->
          X = Y) :
    rho = (Fintype.card d : ℂ)⁻¹ • (1 : Matrix d d ℂ) +
      ∑ l, ∑ j,
        ((probability l j : ℂ) - (Fintype.card d : ℂ)⁻¹) • projector l j := by
  fail_if_success rfl
  let q : ℂ := (Fintype.card d : ℂ)⁻¹
  apply hcomplete
  intro k r
  have hcard : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum_probability (l : L) : ∑ j, (probability l j : ℂ) = 1 := by
    calc
      ∑ j, (probability l j : ℂ) =
          ∑ j, Matrix.trace (rho * projector l j) := by
            exact Finset.sum_congr rfl fun j _ => hprobability l j
      _ = Matrix.trace (rho * ∑ j, projector l j) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = 1 := by rw [hresolution, Matrix.mul_one, hrho]
  have hcentered (l : L) : ∑ j, ((probability l j : ℂ) - q) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_probability]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [q]
    field_simp
    ring
  have htrace_projector : Matrix.trace (projector k r) = 1 := by
    calc
      Matrix.trace (projector k r) =
          Matrix.trace ((1 : Matrix d d ℂ) * projector k r) := by simp
      _ = Matrix.trace ((∑ j, projector k j) * projector k r) := by
        rw [hresolution]
      _ = ∑ j, Matrix.trace (projector k j * projector k r) := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
      _ = 1 := by simp [hoverlap]
  have hcontext (l : L) :
      ∑ j, ((probability l j : ℂ) - q) *
          Matrix.trace (projector l j * projector k r) =
        if l = k then (probability k r : ℂ) - q else 0 := by
    by_cases hl : l = k
    · subst l
      simp [hoverlap]
    · simp only [hoverlap, hl, if_false]
      rw [← Finset.sum_mul, hcentered, zero_mul]
  symm
  calc
    Matrix.trace
        (((Fintype.card d : ℂ)⁻¹ • (1 : Matrix d d ℂ) +
            ∑ l, ∑ j,
              ((probability l j : ℂ) - (Fintype.card d : ℂ)⁻¹) • projector l j) *
          projector k r) =
        q * Matrix.trace (projector k r) +
          ∑ l, ∑ j, ((probability l j : ℂ) - q) *
            Matrix.trace (projector l j * projector k r) := by
              simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
                Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
                Matrix.one_mul, smul_eq_mul, q]
    _ = q + ∑ l,
        (if l = k then (probability k r : ℂ) - q else 0) := by
      rw [htrace_projector, mul_one]
      exact congrArg (q + ·) (Finset.sum_congr rfl fun l _ => hcontext l)
    _ = (probability k r : ℂ) := by simp
    _ = Matrix.trace (rho * projector k r) := hprobability k r

example :
    let rho : Matrix Unit Unit ℂ := 1
    let projector : Unit -> Unit -> Matrix Unit Unit ℂ := fun _ _ => 1
    let probability : Unit -> Unit -> ℝ := fun _ _ => 1
    rho = (Fintype.card Unit : ℂ)⁻¹ • (1 : Matrix Unit Unit ℂ) +
      ∑ l, ∑ j,
        ((probability l j : ℂ) - (Fintype.card Unit : ℂ)⁻¹) • projector l j := by
  dsimp only
  apply complete_basis_reconstruction (rho := (1 : Matrix Unit Unit ℂ))
    (projector := fun _ _ => 1) (probability := fun _ _ => 1)
  · simp
  · simp
  · simp
  · simp
  · intro X Y h
    ext i j
    have hentry := h () ()
    simpa [Matrix.trace, Matrix.mul_apply] using hentry

#print axioms complete_basis_reconstruction

end D5.S3.QuantumContext.CompleteBasisReconstruction
