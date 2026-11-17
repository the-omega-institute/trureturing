/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global cardinality obstruction for paired coherent degree-one pure designs. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry

/-! Actual regular coherent degree-one pure designs, in the precise conditional
sense used by Peled et al. The obstruction concerns this paired construction;
it does not refute all interpretations of their broader design hypothesis.
Source: the CC BY 4.0 return note, Haobo Ma (Chrono AI, Singapore) and Wenlin
Zhang (NUS and Chrono AI, Singapore). -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormDesignObstruction

/-- A nonempty family of actual rank-one density projectors, with coherent sum
and one common distinct-pair trace overlap. Existence is not postulated. -/
def PureDesign {n v : ℕ} (P : Fin v → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < v ∧ (∀ j, IsDensity (P j) ∧ P j * P j = P j ∧ (P j).rank = 1) ∧
    (∑ j, P j) = ((v : ℂ) / n) • 1 ∧
    ∃ μ : ℝ, ∀ i j, i ≠ j → (P i * P j).trace = (μ : ℂ)

private lemma trace_self {n v : ℕ} (P : Fin v → Matrix (Fin n) (Fin n) ℂ)
    (hP : PureDesign P) (i : Fin v) : (P i * P i).trace = 1 := by
  rw [(hP.2.1 i).2.1, (hP.2.1 i).1.2]

private lemma trace_pair_sum {n v : ℕ} (P : Fin v → Matrix (Fin n) (Fin n) ℂ)
    (hP : PureDesign P) (i : Fin v) :
    ∑ j, (P j * P i).trace = (v : ℂ) / n := by
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, hP.2.2.1,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, (hP.2.1 i).1.2, smul_eq_mul, mul_one]

/-- A coherent qubit degree-one pure design has at least two and at most four
members. This is a global cardinality theorem, not a bounded search. -/
theorem qubit_design_cardinality {v : ℕ} (P : Fin v → Matrix (Fin 2) (Fin 2) ℂ)
    (hP : PureDesign P) : 2 ≤ v ∧ v ≤ 4 := by
  classical
  obtain ⟨μ, hμ⟩ := hP.2.2.2
  let i0 : Fin v := ⟨0, hP.1⟩
  have hpair (i j : Fin v) :
      (P i * P j).trace = if i = j then 1 else (μ : ℂ) := by
    split_ifs with h
    · subst j; exact trace_self P hP i
    · exact hμ i j h
  have hv : (v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hP.1
  have hμne : (μ : ℂ) ≠ 1 := by
    intro he
    have hs := trace_pair_sum P hP i0
    simp only [hpair, he, ite_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at hs
    have : (v : ℂ) = 0 := by linear_combination 2 * hs
    exact hv this
  have hli : LinearIndependent ℂ P := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hs := congrArg Matrix.trace hc
    simp only [Matrix.trace_sum, Matrix.trace_smul, (hP.2.1 _).1.2,
      smul_eq_mul, mul_one, Matrix.trace_zero] at hs
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M * P i).trace) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      Matrix.zero_mul, Matrix.trace_zero, smul_eq_mul, hpair] at he
    have ht : (∑ j, c j * (if j = i then 1 else (μ : ℂ))) = c i * (1-μ) := by
      calc
        _ = ∑ j, (c j * (μ : ℂ) + if j = i then c j * (1-μ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
        _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_mul, hs]
    rw [ht] at he
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr (Ne.symm hμne))
  have hu := hli.fintype_card_le_finrank
  have hu' : v ≤ 4 := by simpa [Module.finrank_matrix] using hu
  have hv1 : v ≠ 1 := by
    intro he
    have hs := trace_pair_sum P hP i0
    have hsum : ∑ j : Fin v, (P j * P i0).trace = 1 := by
      rw [Finset.sum_eq_single i0]
      · exact trace_self P hP i0
      · intro j _ hj
        have : j = i0 := Fin.ext (by have hjv := j.isLt; dsimp [i0]; omega)
        exact False.elim (hj this)
      · simp
    rw [hsum, he] at hs
    norm_num at hs
  have hvpos := hP.1
  exact ⟨by omega, hu'⟩

private lemma trace_pair_nonneg {n v : ℕ} (P : Fin v → Matrix (Fin n) (Fin n) ℂ)
    (hP : PureDesign P) (i j : Fin v) : 0 ≤ (P i * P j).trace.re := by
  let A : HermitianMat (Fin n) ℂ := ⟨P i, (hP.2.1 i).1.1.isHermitian⟩
  let B : HermitianMat (Fin n) ℂ := ⟨P j, (hP.2.1 j).1.1.isHermitian⟩
  have hA : 0 ≤ A := HermitianMat.zero_le_iff.mpr (hP.2.1 i).1.1
  have hB : 0 ≤ B := HermitianMat.zero_le_iff.mpr (hP.2.1 j).1.1
  exact HermitianMat.inner_ge_zero hA hB

/-- Coherence in dimension n requires at least n actual pure projectors. -/
theorem design_dimension_le_cardinality {n v : ℕ} (hn : 0 < n)
    (P : Fin v → Matrix (Fin n) (Fin n) ℂ) (hP : PureDesign P) : n ≤ v := by
  let i0 : Fin v := ⟨0, hP.1⟩
  have hs : 1 ≤ ∑ j, (P j * P i0).trace.re := by
    rw [← show (P i0 * P i0).trace.re = 1 by rw [trace_self P hP i0]; rfl]
    exact Finset.single_le_sum (fun j _ => trace_pair_nonneg P hP j i0) (Finset.mem_univ _)
  have he := congrArg Complex.re (trace_pair_sum P hP i0)
  simp only [Complex.re_sum] at he
  have hc : 1 ≤ (v : ℝ) / n := by simpa using hs.trans_eq he
  have hl := (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mp hc
  exact_mod_cast (by simpa only [one_mul] using hl : (n : ℝ) ≤ v)

/-- No nonempty common-size pair exists in dimensions 2 and D≥5. This leaves
other design constructions and the broad imprecise general-p question open. -/
theorem no_coherent_pair (D : ℕ) (hD : 5 ≤ D) :
    ¬ ∃ (v : ℕ) (P : Fin v → Matrix (Fin 2) (Fin 2) ℂ)
      (R : Fin v → Matrix (Fin D) (Fin D) ℂ), PureDesign P ∧ PureDesign R := by
  rintro ⟨v, P, R, hP, hR⟩
  have hu := (qubit_design_cardinality P hP).2
  have hl := design_dimension_le_cardinality (by omega : 0 < D) R hR
  omega

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormDesignObstruction
