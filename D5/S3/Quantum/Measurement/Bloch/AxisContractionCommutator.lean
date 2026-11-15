/- GID: D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Bloch/AxisContractionCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parameterized commutator identity for qubit Bloch axis contractions. -/

/- axisOuter_eq_implies_parallel: proof_shape: content; escape_witness: a symmetric
   rank-one outer product forces proportionality of the nonzero vector pair.
   admission_basis: escape-witness.
   axisContraction_commutator: proof_shape: bind-only; escape_witness: none;
   consumer: axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal.
   axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal: proof_shape: content;
   escape_witness: axisOuter_eq_implies_parallel on the live path; admission_basis:
   escape-witness. -/

import D5.S3.Quantum.Measurement.Bloch.QubitBloch

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Measurement.Bloch

/-- The real Bloch contraction associated with an axis and contraction factor. -/
def axisContraction (n : Fin 3 → ℝ) (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (c * if i = j then 1 else 0) + (1 - c) * n i * n j

/-- The Euclidean dot product of two three-coordinate Bloch vectors. -/
def axisDot (n m : Fin 3 → ℝ) : ℝ := ∑ k, n k * m k

/-- The rank-one matrix with entries `n i * m j`. -/
def axisOuter (n m : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => n i * m j

/-- The commutator of two Bloch axis contractions factors through their axis dot product. -/
theorem axisOuter_eq_implies_parallel {n m : Fin 3 → ℝ} (hn : n ≠ 0)
    (h : axisOuter n m = axisOuter m n) :
    ∃ s : ℝ, m = s • n := by
  have hncoord : ∃ i, n i ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    apply hn
    funext i
    simp [hzero i]
  obtain ⟨i, hi⟩ := hncoord
  refine ⟨m i / n i, ?_⟩
  funext j
  have hij := congrFun (congrFun h i) j
  simp [axisOuter] at hij
  simp only [Pi.smul_apply]
  change m j = (m i / n i) * n j
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hi).2
  nlinarith [hij]

/-- The commutator of two Bloch axis contractions factors through their axis dot product. -/
theorem axisContraction_commutator (n m : Fin 3 → ℝ) (c d : ℝ) :
    axisContraction n c * axisContraction m d - axisContraction m d * axisContraction n c =
      ((1 - c) * (1 - d) * axisDot n m) • (axisOuter n m - axisOuter m n) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisContraction, axisDot, axisOuter, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring

/-- Nonparallel, nonorthogonal axes produce a nonzero commutator away from identity factors. -/
theorem axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal
    {n m : Fin 3 → ℝ} {c d : ℝ} (hn : n ≠ 0)
    (hparallel : ¬ ∃ s : ℝ, m = s • n)
    (hdot : axisDot n m ≠ 0) (hc : c ≠ 1) (hd : d ≠ 1) :
    axisContraction n c * axisContraction m d - axisContraction m d * axisContraction n c ≠ 0 := by
  rw [axisContraction_commutator]
  have houter : axisOuter n m - axisOuter m n ≠ 0 := by
    intro hzero
    apply hparallel
    apply axisOuter_eq_implies_parallel hn
    exact sub_eq_zero.mp hzero
  apply smul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact sub_ne_zero.mpr hc.symm
      · exact sub_ne_zero.mpr hd.symm
    · exact hdot
  · exact houter

end D5.S3.Quantum.Measurement.Bloch
