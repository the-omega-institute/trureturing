/- GID: D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Perfectly distinguishable density matrices number at most the memory dimension. -/

import Mathlib.Analysis.Matrix.Order

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity

open Matrix

private lemma zero_trace_mul_eq_zero {d : Nat}
    (E rho : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) (hRho : rho.PosSemidef)
    (hTrace : (E * rho).trace = 0) : E * rho = 0 := by
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hRho.nonneg
  have hA' : E = A.conjTranspose * A := hA
  have hB' : rho = B.conjTranspose * B := hB
  have hAB : A * B.conjTranspose = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    calc
      ((A * B.conjTranspose).conjTranspose * (A * B.conjTranspose)).trace =
          (B * E * B.conjTranspose).trace := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA']
            simp only [mul_assoc]
      _ = (B.conjTranspose * B * E).trace := Matrix.trace_mul_cycle _ _ _
      _ = (E * rho).trace := by rw [← hB', Matrix.trace_mul_comm]
      _ = 0 := hTrace
  calc
    E * rho = A.conjTranspose * (A * B.conjTranspose) * B := by
      rw [hA', hB']
      simp only [mul_assoc]
    _ = 0 := by rw [hAB, mul_zero, zero_mul]

private lemma zero_trace_support {d : Nat}
    (E rho : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) (hRho : rho.PosSemidef)
    (hTrace : (E * rho).trace = 0) :
    LinearMap.range rho.toEuclideanLin ≤ LinearMap.ker E.toEuclideanLin := by
  rw [LinearMap.range_le_ker_iff]
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, map_zero] using
    congrArg Matrix.toEuclideanLin (zero_trace_mul_eq_zero E rho hE hRho hTrace)

private lemma unit_trace_support {d : Nat}
    (E rho : Matrix (Fin d) (Fin d) ℂ)
    (hE : E ≤ 1) (hRho : rho.PosSemidef)
    (hTrace : rho.trace = 1) (hPairing : (E * rho).trace = 1) :
    LinearMap.range rho.toEuclideanLin ≤ LinearMap.ker (1 - E).toEuclideanLin := by
  apply zero_trace_support (1 - E) rho (Matrix.le_iff.mp hE) hRho
  rw [sub_mul, one_mul, Matrix.trace_sub, hTrace, hPairing, sub_self]

/-- Perfect discrimination by a single POVM bounds the number of density states
by the finite dimension of the memory. -/
theorem finite_memory_history_capacity {N d : Nat}
    (rho E : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hRho : ∀ i, (rho i).PosSemidef ∧ (rho i).trace = 1)
    (hE : ∀ j, (E j).PosSemidef)
    (hSum : ∑ j, E j = 1)
    (hPairing : ∀ i j, (E j * rho i).trace = if i = j then 1 else 0) :
    N ≤ d := by
  classical
  have hUpper (i : Fin N) : E i ≤ 1 := by
    rw [← hSum]
    exact Finset.single_le_sum (fun j _ => (hE j).nonneg) (Finset.mem_univ i)
  have hOne (i : Fin N) := unit_trace_support (E i) (rho i) (hUpper i)
    (hRho i).1 (hRho i).2 (by simpa using hPairing i i)
  have hZero (i j : Fin N) (hij : i ≠ j) := zero_trace_support (E i) (rho j)
    (hE i) (hRho j).1 (by simpa [Ne.symm hij] using hPairing j i)
  have hNonzero (i : Fin N) : rho i ≠ 0 := by
    intro h
    have ht := (hRho i).2
    rw [h, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  have hRange (i : Fin N) : LinearMap.range (rho i).toEuclideanLin ≠ ⊥ := by
    intro h
    apply hNonzero i
    apply Matrix.toEuclideanLin.injective
    simpa only [map_zero] using LinearMap.range_eq_bot.mp h
  choose v hv hvNe using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hRange i)
  have hOrthogonal : Pairwise fun i j => ⟪v i, v j⟫_ℂ = 0 := by
    intro i j hij
    have hFix : (E i).toEuclideanLin (v i) = v i := by
      have h := hOne i (hv i)
      change (1 - E i).toEuclideanLin (v i) = 0 at h
      have hSub : v i - (E i).toEuclideanLin (v i) = 0 := by
        simpa only [map_sub, Matrix.toEuclideanLin, Matrix.toLpLin_one,
          LinearMap.sub_apply, LinearMap.id_apply] using h
      exact (sub_eq_zero.mp hSub).symm
    have hKill : (E i).toEuclideanLin (v j) = 0 := hZero i j hij (hv j)
    calc
      ⟪v i, v j⟫_ℂ = ⟪(E i).toEuclideanLin (v i), v j⟫_ℂ := by rw [hFix]
      _ = ⟪v i, (E i).toEuclideanLin (v j)⟫_ℂ :=
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hE i).isHermitian) _ _
      _ = 0 := by rw [hKill, inner_zero_right]
  have hIndependent := linearIndependent_of_ne_zero_of_inner_eq_zero hvNe hOrthogonal
  simpa using hIndependent.fintype_card_le_finrank

#print axioms finite_memory_history_capacity

end D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
