/- GID: D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Over a fixed classical channel the least trace-distance contraction coefficient of a qubit channel is |a - f|. -/

/-
proof_shape: result: bind-only (instances of the frozen variational trace-norm formula and Kraus
  construction, Mathlib's unitary entry bound, and normalization)
escape_witness: null
admission_basis: open-problem-resolution (issue #10033)
Direct frozen dependencies: D5/S3/Quantum/Foundation/FiniteTraceDistance
  (`traceNorm_eq_max_re_tr_U`, `traceDistance_contract`, `traceDistance_le_one`),
  D5/S3/Quantum/Foundation/FiniteKrausChannel (`finite_kraus_quantum_channel`)
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.LovasAndaiDobrushinInfimum

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped ComplexOrder MatrixOrder

/-- `Q_C(a,f)`: the qubit channels over the classical channel with parameters `a, f` in the
parametrization (eq:matQ) of Lovas–Andai: the Choi blocks `Q₁₁ = Q(|0⟩⟨0|)` and
`Q₂₂ = Q(|1⟩⟨1|)` have `(0,0)` entries `a` and `f`. -/
def classicalFiber (a f : ℝ) : Set (QuantumChannel (Fin 2) (Fin 2)) :=
  {Q | act Q (Matrix.single 0 0 1) 0 0 = (a : ℂ) ∧ act Q (Matrix.single 1 1 1) 0 0 = (f : ℂ)}

/-- The trace-distance contraction coefficient
`η^Tr(Q) = sup {Tr|Q(ρ) - Q(σ)| / Tr|ρ - σ| : ρ, σ qubit states}`. -/
def dobrushin (Q : QuantumChannel (Fin 2) (Fin 2)) : ℝ :=
  sSup {x | ∃ rho sigma : DensityState (Fin 2),
    x = traceDistance (Q.mapState rho) (Q.mapState sigma) / traceDistance rho sigma}

/-- Lovas–Andai (arXiv:1607.01215), Conjecture: `inf {η(Q) : Q ∈ Q_C(a,f)} = |a - f|`;
the infimum is attained. -/
def claim : Prop :=
  ∀ a f : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ f → f ≤ 1 →
    IsLeast (dobrushin '' classicalFiber a f) |a - f|

theorem result : claim := by
  intro a f ha0 ha1 hf0 hf1
  -- Variational lower bound: `re Tr(diag(s, -s) A) ≤ ‖A‖₁` for `s = ±1`.
  have lower : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, |(A 0 0 - A 1 1).re| ≤ traceNorm A := by
    intro A
    have key : ∀ s : ℝ, s * s = 1 → s * (A 0 0 - A 1 1).re ≤ traceNorm A := by
      intro s hs
      have hs' : (s : ℂ) * s = 1 := by exact_mod_cast hs
      have hU : Matrix.diagonal ![(s : ℂ), -(s : ℂ)] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.diagonal, Matrix.mul_apply, Matrix.star_apply, hs']
      have h := (traceNorm_eq_max_re_tr_U A).2 ⟨⟨_, hU⟩, rfl⟩
      have htr : ((Matrix.diagonal ![(s : ℂ), -(s : ℂ)] * A).trace).re =
          s * (A 0 0 - A 1 1).re := by
        simp [Matrix.trace_fin_two, Matrix.diagonal_mul, Complex.mul_re]
        ring
      exact htr ▸ h
    rcases le_total 0 (A 0 0 - A 1 1).re with h | h
    · rw [abs_of_nonneg h]
      simpa using key 1 (by norm_num)
    · rw [abs_of_nonpos h]
      simpa using key (-1) (by norm_num)
  -- Variational upper bound for diagonal matrices: `‖A‖₁ ≤ |A₀₀| + |A₁₁|`.
  have upper : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A 0 1 = 0 → A 1 0 = 0 →
      traceNorm A ≤ ‖A 0 0‖ + ‖A 1 1‖ := by
    intro A h01 h10
    obtain ⟨V, hV⟩ := (traceNorm_eq_max_re_tr_U A).1
    rw [← hV]
    have e : ((V : Matrix (Fin 2) (Fin 2) ℂ) * A).trace =
        (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * A 0 0 + (V : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * A 1 1 := by
      simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h01, h10]
    rw [e]
    have b0 := entry_norm_bound_of_unitary V.2 0 0
    have b1 := entry_norm_bound_of_unitary V.2 1 1
    calc Complex.re ((V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * A 0 0 +
            (V : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * A 1 1)
        ≤ ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * A 0 0 +
            (V : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * A 1 1‖ := Complex.re_le_norm _
      _ ≤ ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ * ‖A 0 0‖ +
            ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ * ‖A 1 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖A 0 0‖ + ‖A 1 1‖ := by
          nlinarith [norm_nonneg (A 0 0), norm_nonneg (A 1 1)]
  -- The pure states `|0⟩⟨0|` and `|1⟩⟨1|`.
  have pure : ∀ i : Fin 2, ∃ rho : DensityState (Fin 2),
      CStarMatrix.ofMatrix.symm rho.1 = Matrix.single i i 1 := by
    intro i
    have hproj : (Matrix.single i i (1 : ℂ)) =
        star (Matrix.single i i (1 : ℂ)) * Matrix.single i i 1 := by
      ext r c
      fin_cases i <;> fin_cases r <;> fin_cases c <;>
        simp [Matrix.mul_apply, Matrix.single, Matrix.star_apply]
    have h0 : (0 : Matrix (Fin 2) (Fin 2) ℂ) ≤ Matrix.single i i 1 := by
      rw [hproj]
      exact star_mul_self_nonneg _
    refine ⟨⟨CStarMatrix.ofMatrix (Matrix.single i i 1),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv h0, ?_⟩, rfl⟩
    show Matrix.trace (Matrix.single i i (1 : ℂ)) = 1
    fin_cases i <;> simp [Matrix.trace_fin_two, Matrix.single]
  -- Trace preservation on the diagonal, and the matrix of an output state.
  have tp : ∀ (Q : QuantumChannel (Fin 2) (Fin 2)) (X : Matrix (Fin 2) (Fin 2) ℂ),
      act Q X 0 0 + act Q X 1 1 = X 0 0 + X 1 1 := by
    intro Q X
    rw [← Matrix.trace_fin_two, ← Matrix.trace_fin_two]
    exact Q.trace_preserving (CStarMatrix.ofMatrix X)
  have mapv : ∀ (Q : QuantumChannel (Fin 2) (Fin 2)) (rho : DensityState (Fin 2)),
      CStarMatrix.ofMatrix.symm (Q.mapState rho).1 = act Q (CStarMatrix.ofMatrix.symm rho.1) :=
    fun _ _ => rfl
  have diagSum : ∀ rho : DensityState (Fin 2),
      CStarMatrix.ofMatrix.symm rho.1 0 0 + CStarMatrix.ofMatrix.symm rho.1 1 1 = 1 := by
    intro rho
    rw [← Matrix.trace_fin_two]
    exact rho.2.2
  have diagReal : ∀ rho : DensityState (Fin 2), (CStarMatrix.ofMatrix.symm rho.1 0 0).im = 0 := by
    intro rho
    have hP : (CStarMatrix.ofMatrix.symm rho.1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
    exact Complex.conj_eq_iff_im.mp (hP.isHermitian.apply 0 0)
  have bdd : ∀ Q : QuantumChannel (Fin 2) (Fin 2), BddAbove {x | ∃ rho sigma : DensityState (Fin 2),
      x = traceDistance (Q.mapState rho) (Q.mapState sigma) / traceDistance rho sigma} := by
    intro Q
    refine ⟨1, ?_⟩
    rintro x ⟨rho, sigma, rfl⟩
    exact div_le_one_of_le₀ (traceDistance_contract Q rho sigma) (traceDistance_nonneg _ _)
  obtain ⟨ρ0, hρ0⟩ := pure 0
  obtain ⟨σ0, hσ0⟩ := pure 1
  -- Every channel over the classical channel contracts `|0⟩⟨0|, |1⟩⟨1|` by at least `|a - f|`.
  have lb : ∀ Q ∈ classicalFiber a f, |a - f| ≤ dobrushin Q := by
    rintro Q ⟨hQa, hQf⟩
    refine le_csSup_of_le (bdd Q) ⟨ρ0, σ0, rfl⟩ ?_
    have hY : 1 ≤ traceDistance ρ0 σ0 := by
      unfold traceDistance
      rw [hρ0, hσ0]
      let D0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1 - Matrix.single 1 1 1
      have h := lower D0
      have e : (D0 0 0 - D0 1 1).re = 2 := by
        simp [D0, Matrix.single]
        norm_num
      rw [e] at h
      norm_num at h
      linarith
    have hX : |a - f| ≤ traceDistance (Q.mapState ρ0) (Q.mapState σ0) := by
      unfold traceDistance
      rw [mapv, mapv, hρ0, hσ0]
      have t0 : act Q (Matrix.single 0 0 1) 0 0 + act Q (Matrix.single 0 0 1) 1 1 = 1 := by
        rw [tp]
        simp
      have t1 : act Q (Matrix.single 1 1 1) 0 0 + act Q (Matrix.single 1 1 1) 1 1 = 1 := by
        rw [tp]
        simp
      have h := lower (act Q (Matrix.single 0 0 1) - act Q (Matrix.single 1 1 1))
      have e : (act Q (Matrix.single 0 0 1) - act Q (Matrix.single 1 1 1)) 0 0 -
          (act Q (Matrix.single 0 0 1) - act Q (Matrix.single 1 1 1)) 1 1 =
            ((2 * (a - f) : ℝ) : ℂ) := by
        simp only [Matrix.sub_apply]
        push_cast
        linear_combination 2 * hQa - 2 * hQf - t0 + t1
      rw [e, Complex.ofReal_re, abs_mul, abs_two] at h
      linarith
    exact hX.trans (le_div_self ((abs_nonneg _).trans hX) (by linarith)
      (traceDistance_le_one ρ0 σ0))
  -- The measure-and-prepare channel `X ↦ Σ_{i,j} w_j(i) X_jj |i⟩⟨i|`.
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → Fin 2 → ℝ, w = ![![a, 1 - a], ![f, 1 - f]] := ⟨_, rfl⟩
  have hw0 : ∀ j i, 0 ≤ w j i := by
    intro j i
    subst hw
    fin_cases j <;> fin_cases i <;> simp <;> linarith
  have hw1 : ∀ j, w j 0 + w j 1 = 1 := by
    intro j
    subst hw
    fin_cases j <;> simp
  have hwa : w 0 0 = a := by subst hw; simp
  have hwf : w 1 0 = f := by subst hw; simp
  have hsq : ∀ j i, ((Real.sqrt (w j i) : ℝ) : ℂ) * (Real.sqrt (w j i) : ℝ) = (w j i : ℂ) := by
    intro j i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw0 j i)]
  let K : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun p => Matrix.single p.1 p.2 ((Real.sqrt (w p.2 p.1) : ℝ) : ℂ)
  have hK : (∑ p, (K p).conjTranspose * K p) = 1 := by
    have h1 : ∀ j, ((w j 0 : ℝ) : ℂ) + (w j 1 : ℝ) = 1 := fun j => by exact_mod_cast hw1 j
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [K, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
        Matrix.conjTranspose_apply]
    · linear_combination hsq 0 0 + hsq 0 1 + h1 0
    · linear_combination hsq 1 0 + hsq 1 1 + h1 1
  obtain ⟨Q0, hQ0act⟩ := D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  have hQ0 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      act Q0 X 0 0 = w 0 0 * X 0 0 + w 1 0 * X 1 1 ∧
      act Q0 X 1 1 = w 0 1 * X 0 0 + w 1 1 * X 1 1 ∧
      act Q0 X 0 1 = 0 ∧ act Q0 X 1 0 = 0 := by
    intro X
    have hX : act Q0 X = ∑ p, K p * X * (K p).conjTranspose := hQ0act X
    rw [hX]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [K, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
        Matrix.conjTranspose_apply]
    · linear_combination X 0 0 * hsq 0 0 + X 1 1 * hsq 1 0
    · linear_combination X 0 0 * hsq 0 1 + X 1 1 * hsq 1 1
  have hQ0fib : Q0 ∈ classicalFiber a f := by
    refine ⟨?_, ?_⟩
    · rw [(hQ0 _).1, hwa]
      simp [Matrix.single]
    · rw [(hQ0 _).1, hwf]
      simp [Matrix.single]
  -- The measure-and-prepare channel contracts every pair of states by at most `|a - f|`.
  have measurePrepare : ∀ rho sigma : DensityState (Fin 2),
      traceDistance (Q0.mapState rho) (Q0.mapState sigma) ≤ |a - f| * traceDistance rho sigma := by
    intro rho sigma
    set P := CStarMatrix.ofMatrix.symm rho.1 with hP
    set S := CStarMatrix.ofMatrix.symm sigma.1 with hS
    have hPtr : P 0 0 + P 1 1 = 1 := diagSum rho
    have hStr : S 0 0 + S 1 1 = 1 := diagSum sigma
    set t := P 0 0 - S 0 0 with ht
    have ht_im : t.im = 0 := by
      rw [ht, Complex.sub_im, diagReal rho, diagReal sigma, sub_zero]
    have hY : ‖t‖ ≤ traceDistance rho sigma := by
      unfold traceDistance
      have h := lower (P - S)
      have e : (P - S) 0 0 - (P - S) 1 1 = 2 * t := by
        simp only [Matrix.sub_apply]
        linear_combination hStr - hPtr
      rw [e, show (2 * t).re = 2 * t.re by simp, abs_mul, abs_two,
        Complex.abs_re_eq_norm.mpr ht_im] at h
      linarith
    have hX : traceDistance (Q0.mapState rho) (Q0.mapState sigma) ≤ |a - f| * ‖t‖ := by
      unfold traceDistance
      rw [mapv, mapv]
      obtain ⟨p00, p11, p01, p10⟩ := hQ0 P
      obtain ⟨s00, s11, s01, s10⟩ := hQ0 S
      have h := upper (act Q0 P - act Q0 S) (by simp [p01, s01]) (by simp [p10, s10])
      have hw1c : ∀ j, ((w j 0 : ℝ) : ℂ) + (w j 1 : ℝ) = 1 := fun j => by exact_mod_cast hw1 j
      have e0 : (act Q0 P - act Q0 S) 0 0 = ((a - f : ℝ) : ℂ) * t := by
        rw [Matrix.sub_apply, p00, s00, hwa, hwf, ht]
        push_cast
        linear_combination (f : ℂ) * hPtr - (f : ℂ) * hStr
      have e1 : (act Q0 P - act Q0 S) 1 1 = ((f - a : ℝ) : ℂ) * t := by
        rw [Matrix.sub_apply, p11, s11, ht]
        have ha' : ((w 0 1 : ℝ) : ℂ) = 1 - a := by
          rw [← hwa]; linear_combination hw1c 0
        have hf' : ((w 1 1 : ℝ) : ℂ) = 1 - f := by
          rw [← hwf]; linear_combination hw1c 1
        rw [ha', hf']
        push_cast
        linear_combination (1 - (f : ℂ)) * hPtr - (1 - (f : ℂ)) * hStr
      rw [e0, e1, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_sub_comm f a] at h
      linarith
    exact hX.trans (mul_le_mul_of_nonneg_left hY (abs_nonneg _))
  have ub : dobrushin Q0 ≤ |a - f| := by
    refine csSup_le ⟨_, ρ0, σ0, rfl⟩ ?_
    rintro x ⟨rho, sigma, rfl⟩
    exact div_le_of_le_mul₀ (traceDistance_nonneg _ _) (abs_nonneg _) (measurePrepare rho sigma)
  exact ⟨⟨Q0, hQ0fib, le_antisymm ub (lb Q0 hQ0fib)⟩, fun y ⟨Q, hQ, hy⟩ => hy ▸ lb Q hQ⟩

#print axioms result

end D5.S3.Quantum.QuantumChannels.LovasAndaiDobrushinInfimum
