/- GID: D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.claim
   digest: A connected barbell of order 23 refutes the path-minimum edge derivative conjecture. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#19527; Refuted)
   Direct frozen dependencies: none (only pinned Mathlib imports).
   Definitions have no proposition-valued proof bodies.
   All theorem proofs use spectral diagonalization, scalar calculus and algebraic or finite normalization.
   Finite rational certificates are certified-instance inputs to result, which refutes claim.
   sum_filter_inv: proof_shape: bind-only; escape_witness: none; consumers: reciprocalRoots_eq_sum.
   reciprocalRoots_eq_sum: proof_shape: bind-only; escape_witness: none; consumers: reciprocalRoots_eq_trace.
   reciprocalRoots_eq_trace: proof_shape: bind-only; escape_witness: none; consumers: conjugate_reciprocal_trace.
   conjugate_reciprocal_trace: proof_shape: bind-only; escape_witness: none; consumers: kemeny_eq_grounded.
   grounded_generalized_inverse: proof_shape: bind-only; escape_witness: none; consumers: kemeny_eq_grounded.
   grounded_trace: proof_shape: bind-only; escape_witness: none; consumers: kemeny_eq_grounded.
   edge_update_grounded: proof_shape: bind-only; escape_witness: none; consumers: update_from_voltage.
   normLap_isHermitian: proof_shape: bind-only; escape_witness: none; consumers: kemeny_eq_grounded.
   normLap_similarity: proof_shape: bind-only; escape_witness: none; consumers: kemeny_eq_grounded.
   kemeny_eq_grounded: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   paramAdj_isSymm: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   paramAdj_degrees: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   paramAdj_laplacian: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   update_from_voltage: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   weightedGreenValue_hasDerivAt: proof_shape: bind-only; escape_witness: none; consumers: kemeny_edge_hasDerivAt.
   greenB_row0: proof_shape: bind-only; escape_witness: none; consumers: barbell_grounded_inverse.
   barbell_connected: proof_shape: bind-only; escape_witness: none; consumers: result.
   derivative_comparison: proof_shape: bind-only; escape_witness: none; consumers: result.
   barbell_degree_vector: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt.
   barbell_grounded_inverse: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt.
   barbell_voltage: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt.
   barbell_green_voltage: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt.
   path_degree_vector: proof_shape: bind-only; escape_witness: none; consumers: path_hasDerivAt.
   path_grounded_inverse: proof_shape: bind-only; escape_witness: none; consumers: path_hasDerivAt.
   path_voltage: proof_shape: bind-only; escape_witness: none; consumers: path_hasDerivAt.
   path_green_voltage: proof_shape: bind-only; escape_witness: none; consumers: path_hasDerivAt.
   derivativeB_Q: proof_shape: bind-only; escape_witness: none; consumers: derivativeB_real.
   derivativeP_Q: proof_shape: bind-only; escape_witness: none; consumers: derivativeP_real.
   kemeny_edge_hasDerivAt: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt, path_hasDerivAt.
   cast_grounded_data: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt, path_hasDerivAt.
   derivativeB_real: proof_shape: bind-only; escape_witness: none; consumers: barbell_hasDerivAt.
   derivativeP_real: proof_shape: bind-only; escape_witness: none; consumers: path_hasDerivAt.
   barbell_hasDerivAt: proof_shape: bind-only; escape_witness: none; consumers: result.
   path_hasDerivAt: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
   The source definitions and minimality assertion use the expressions specified in #19527.
   The edge direction uses Finset.weightedVSubVSubWeights; its body is Pi.single a 1 - Pi.single b 1.
   The public result is the designated refutation result (`basis=refutes`) and is exempt from
   four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation

/-! Definitions from C. Albright, K. P. Hadaway, A. H. Pomerance, J. Jeffries, K. J. Lorenzen and A. K. Nix,
"On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant", arXiv:2211.01495v2: the
parameterized adjacency matrix `A(t) = A + tB` with `B` the indicator of one edge or non-edge `{a, b}` (Section 2), its
normalized Laplacian `L(t) = I − D(t)^{−1/2} A(t) D(t)^{−1/2}`, Kemeny's constant `K = Σ_{λ_L ≠ 0} 1/λ_L`, the edge
derivative of `K`, and Conjecture 3.5. -/

section

open Matrix

variable {n : ℕ}

/-- `A(t) = A + tB`: the adjacency matrix of `G` with the weight of `{a, b}` raised by `t` (Section 2, `B` the symmetric
indicator of the single edge or non-edge `{a, b}`). -/
noncomputable def paramAdj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  G.adjMatrix ℝ + t • (Matrix.single a b 1 + Matrix.single b a 1)

/-- The normalized Laplacian `L = I − D^{−1/2} A D^{−1/2}` of a weighted adjacency matrix, `D` the diagonal matrix of
weighted degrees `d_i = Σ_j A_{ij}`. -/
noncomputable def normLap (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - Matrix.of fun i j => A i j / (Real.sqrt (∑ k, A i k) * Real.sqrt (∑ k, A j k))

/-- Kemeny's constant `K = Σ_{λ_L ≠ 0} 1/λ_L`, the sum over the nonzero eigenvalues of the normalized Laplacian with
multiplicity (the roots of its characteristic polynomial; for a symmetric real matrix it splits over `ℝ`). -/
noncomputable def kemeny (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (((normLap A).charpoly.roots.filter (· ≠ 0)).map (·⁻¹)).sum

/-- Conjecture 3.5: for every connected simple graph `G` of order `n` and every edge or non-edge `{a, b}` (`a ≠ b`), the
derivative of Kemeny's constant at `t = 0` is at least the derivative for the path `P_n` with respect to the non-edge
joining its ends. Stated with `HasDerivAt`, so both derivatives are required to exist. -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) (dG dP : ℝ),
    G.Connected → a ≠ b →
    HasDerivAt (fun t => kemeny (paramAdj G a b t)) dG 0 →
    HasDerivAt (fun t => kemeny (paramAdj (SimpleGraph.pathGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ t)) dP 0 →
    dP ≤ dG

end


open Matrix

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def reciprocalRoots (L : Matrix ι ι ℝ) : ℝ :=
  ((L.charpoly.roots.filter (· ≠ 0)).map (·⁻¹)).sum

private theorem sum_filter_inv (s : Multiset ℝ) :
    ((s.filter (· ≠ 0)).map (·⁻¹)).sum = (s.map (·⁻¹)).sum := by
  have h := Multiset.sum_filter_add_sum_filter_not
    (s := s.map (·⁻¹)) (fun x : ℝ => x ≠ 0)
  have hz : (((s.map (·⁻¹)).filter fun x => ¬ x ≠ 0)).sum = 0 :=
    Multiset.sum_eq_zero (fun x hx => not_ne_iff.mp (Multiset.mem_filter.mp hx).2)
  rw [hz, add_zero] at h
  simpa only [Multiset.filter_map, Function.comp_def, ne_eq, inv_eq_zero] using h

private theorem reciprocalRoots_eq_sum (L : Matrix ι ι ℝ) (hL : L.IsHermitian) :
    reciprocalRoots L = ∑ i, (hL.eigenvalues i)⁻¹ := by
  classical
  rw [reciprocalRoots, sum_filter_inv, hL.roots_charpoly_eq_eigenvalues]
  simp

/-- A spectral reciprocal trace from algebraic generalized-inverse equations. -/
private theorem reciprocalRoots_eq_trace (L P T : Matrix ι ι ℝ) (hL : L.IsHermitian)
    (hLT : L * T = 1 - P) (hLP : L * P = 0) (hPT : P * T = 0) :
    reciprocalRoots L = T.trace := by
  classical
  let f := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hL.eigenvectorUnitary)
  let e := hL.eigenvalues
  let Q := f P
  let N := f T
  have hfL : f L = diagonal e := by
    simpa [f, e] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hDN : diagonal e * N = 1 - Q := by
    simpa only [map_mul, map_sub, map_one, hfL] using congrArg f hLT
  have hDQ : diagonal e * Q = 0 := by
    simpa only [map_mul, map_zero, hfL] using congrArg f hLP
  have hQN : Q * N = 0 := by
    simpa only [map_mul, map_zero] using congrArg f hPT
  have hdiag (i : ι) : N i i = (e i)⁻¹ := by
    by_cases hi : e i = 0
    · have hrow (j : ι) : Q i j = (1 : Matrix ι ι ℝ) i j := by
        have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hDN
        simp only [diagonal_mul, Matrix.sub_apply, hi, zero_mul] at h
        linarith
      have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hQN
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      simp_rw [hrow] at h
      simpa [hi, Matrix.one_apply] using h
    · have hq : Q i i = 0 := by
        have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hDQ
        simpa [diagonal_mul, hi] using h
      have h := congrArg (fun M : Matrix ι ι ℝ => M i i) hDN
      simp only [diagonal_mul, Matrix.sub_apply, one_apply_eq, hq, sub_zero] at h
      apply mul_left_cancel₀ hi
      simpa [hi] using h
  rw [reciprocalRoots_eq_sum L hL]
  have htr : N.trace = T.trace := trace_map f T
  rw [← htr, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => (hdiag i).symm


end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem conjugate_reciprocal_trace (H P T U V : Matrix ι ι ℝ)
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hH : (U * H * V).IsHermitian)
    (hHT : H * T = 1 - P) (hHP : H * P = 0) (hPT : P * T = 0) :
    reciprocalRoots (U * H * V) = T.trace := by
  have hc (A B : Matrix ι ι ℝ) :
      (U * A * V) * (U * B * V) = U * (A * B) * V := by
    calc
      _ = U * A * (V * U) * B * V := by noncomm_ring
      _ = _ := by rw [hVU]; noncomm_ring
  have h1 : (U * H * V) * (U * T * V) = 1 - U * P * V := by
    rw [hc, hHT]
    noncomm_ring [hUV]
  have h2 : (U * H * V) * (U * P * V) = 0 := by
    rw [hc, hHP]; simp
  have h3 : (U * P * V) * (U * T * V) = 0 := by
    rw [hc, hPT]; simp
  rw [reciprocalRoots_eq_trace _ _ _ hH h1 h2 h3, Matrix.trace_mul_cycle]
  simp [← Matrix.mul_assoc, hVU]

private theorem grounded_generalized_inverse (L X D Di P E : Matrix ι ι ℝ)
    (hDiD : Di * D = 1) (hLP : L * P = 0) (hPP : P * P = P)
    (hLX : L * X = 1 - E) (hEDQ : E * D * (1 - P) = 0) :
    let H := Di * L
    let T := (1 - P) * X * D * (1 - P)
    H * T = 1 - P ∧ H * P = 0 ∧ P * T = 0 := by
  dsimp only
  have hLQ : L * (1 - P) = L := by noncomm_ring [hLP]
  have hPQ : P * (1 - P) = 0 := isIdempotentElem_iff_mul_one_sub_self.mp hPP
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = Di * (L * (1 - P)) * X * D * (1 - P) := by noncomm_ring
      _ = Di * (L * X) * D * (1 - P) := by rw [hLQ]; noncomm_ring
      _ = Di * D * (1 - P) - Di * (E * D * (1 - P)) := by rw [hLX]; noncomm_ring
      _ = _ := by rw [hDiD, hEDQ]; simp
  · rw [Matrix.mul_assoc, hLP]; simp
  · calc
      _ = (P * (1 - P)) * X * D * (1 - P) := by noncomm_ring
      _ = _ := by rw [hPQ]; simp

private theorem grounded_trace (X D P : Matrix ι ι ℝ) (hPP : P * P = P) :
    ((1 - P) * X * D * (1 - P)).trace =
      (X * D).trace - (X * D * P).trace := by
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    exact (show IsIdempotentElem P from hPP).one_sub
  calc
    _ = (X * D * (1 - P) * (1 - P)).trace := by
      calc
        _ = ((1 - P) * (X * D * (1 - P))).trace := by
          congr 1
          noncomm_ring
        _ = _ := Matrix.trace_mul_comm _ _
    _ = (X * D * (1 - P)).trace := by
      rw [Matrix.mul_assoc (X * D), hQQ]
    _ = _ := by rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]

private theorem edge_update_grounded (L X B W E : Matrix ι ι ℝ) (r t : ℝ)
    (hLX : L * X = 1 - E) (hLW : L * W = B * X)
    (hBW : B * W = r • (B * X)) (ht : 1 + r * t ≠ 0) :
    (L + t • B) * (X - (t / (1 + r * t)) • W) = 1 - E := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.mul_smul, Matrix.smul_mul, hLX, hLW, hBW, smul_smul]
  have h : t - t / (1 + r * t) - t * (t / (1 + r * t) * r) = 0 := by
    have hc := div_mul_cancel₀ t ht
    linear_combination -hc
  linear_combination (norm := module) h • (B * X)

end

section



private theorem normLap_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : (normLap A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [normLap, Matrix.sub_apply, Matrix.of_apply]
  rw [hA.apply i j, mul_comm (Real.sqrt (∑ k, A j k))]
  congr 1
  simp [Matrix.one_apply, eq_comm]

private theorem normLap_similarity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) (hrow : ∀ i, ∑ j, A i j = d i) :
    let U := Matrix.diagonal (fun i => Real.sqrt (d i))
    let V := Matrix.diagonal (fun i => (Real.sqrt (d i))⁻¹)
    normLap A = U * (Matrix.diagonal (fun i => (d i)⁻¹) *
      (Matrix.diagonal d - A)) * V ∧ U * V = 1 ∧ V * U = 1 := by
  dsimp only
  have hs (i) : Real.sqrt (d i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
  have hsq (i) : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt (hd i).le
  have hsn (i) : Real.sqrt (d i) * (d i)⁻¹ = (Real.sqrt (d i))⁻¹ := by
    simpa only [div_eq_mul_inv] using (Real.sqrt_div_self (x := d i))
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [normLap, Matrix.sub_apply, Matrix.of_apply, hrow,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [← mul_assoc, hsn]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
      field_simp [hs i]
      nlinarith [hsq i]
    · simp only [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      field_simp [hs i, hs j]
      <;> ring
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hs i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hs i)

private theorem kemeny_eq_grounded {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (root : Fin n)
    (hA : A.IsSymm) (hd : ∀ i, 0 < d i) (hrow : ∀ i, ∑ j, A i j = d i)
    (hLX : (Matrix.diagonal d - A) * X =
      1 - Matrix.vecMulVec (Pi.single root 1) (fun _ => 1)) :
    kemeny A = (∑ i, d i * X i i) -
      (d ⬝ᵥ (X *ᵥ d)) / (∑ i, d i) := by
  classical
  letI : Nonempty (Fin n) := ⟨root⟩
  let D := Matrix.diagonal d
  let Di := Matrix.diagonal (fun i => (d i)⁻¹)
  let L := D - A
  let M := ∑ i, d i
  let o : Fin n → ℝ := fun _ => 1
  let P := (1 / M) • Matrix.vecMulVec o d
  let E := Matrix.vecMulVec (Pi.single root 1) o
  let T := (1 - P) * X * D * (1 - P)
  have hM : M ≠ 0 := (Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty).ne'
  have hd1 : d ⬝ᵥ o = M := by simp [dotProduct, o, M]
  have hPP : P * P = P := by
    dsimp only [P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul, smul_smul, hd1]
    congr 1
    field_simp
  have hL1 : L *ᵥ o = 0 := by
    ext i
    simp [L, D, Matrix.sub_mulVec, Matrix.mulVec_diagonal, o,
      Matrix.mulVec, dotProduct, hrow, Matrix.diagonal_apply]
  have hLP : L * P = 0 := by
    dsimp only [P]
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec, hL1]
    simp
  have hdQ : d ᵥ* (1 - P) = 0 := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one]
    dsimp only [P]
    rw [Matrix.vecMul_smul, Matrix.vecMul_vecMulVec, hd1]
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    <;> ring
  have hEDQ : E * D * (1 - P) = 0 := by
    have hoD : o ᵥ* D = d := by ext i; simp [o, D, Matrix.vecMul_diagonal]
    dsimp only [E]
    rw [Matrix.vecMulVec_mul, hoD, Matrix.vecMulVec_mul, hdQ]
    simp
  have hDiD : Di * D = 1 := by
    dsimp only [Di, D]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd i).ne'
  have hG := grounded_generalized_inverse L X D Di P E hDiD hLP hPP hLX hEDQ
  obtain ⟨hsim, hUV, hVU⟩ := normLap_similarity A d hd hrow
  let U := Matrix.diagonal (fun i => Real.sqrt (d i))
  let V := Matrix.diagonal (fun i => (Real.sqrt (d i))⁻¹)
  have hHerm : (U * (Di * L) * V).IsHermitian := by
    rw [← hsim]
    exact normLap_isHermitian A hA
  have htrace : kemeny A = T.trace := by
    change reciprocalRoots (normLap A) = _
    rw [hsim]
    exact conjugate_reciprocal_trace (Di * L) P T U V hUV hVU hHerm hG.1 hG.2.1 hG.2.2
  rw [htrace, grounded_trace X D P hPP]
  have hdiag : (X * D).trace = ∑ i, d i * X i i := by
    simp only [Matrix.trace, Matrix.diag, D, Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hDP : (X * D * P).trace = (d ⬝ᵥ (X *ᵥ d)) / M := by
    have hD1 : D *ᵥ o = d := by ext i; simp [D, o, Matrix.mulVec_diagonal]
    dsimp only [P]
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec, ← Matrix.mulVec_mulVec, hD1,
      Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm]
    simp [div_eq_mul_inv, mul_comm]
  rw [hdiag, hDP]

end

section

open Matrix

variable {n : ℕ}

private def edgeDegrees (a b : Fin n) : Fin n → ℝ := Pi.single a 1 + Pi.single b 1

private theorem paramAdj_isSymm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (t : ℝ) : (paramAdj G a b t).IsSymm := by
  have hE : (Matrix.single a b (1 : ℝ) + Matrix.single b a 1).IsSymm := by
    simpa only [Matrix.transpose_single] using
      Matrix.isSymm_add_transpose_self (Matrix.single a b (1 : ℝ))
  exact (G.isSymm_adjMatrix).add (hE.smul t)

private theorem paramAdj_degrees (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (d : Fin n → ℝ) (hrow : ∀ i, ∑ j, G.adjMatrix ℝ i j = d i)
    (t : ℝ) : ∀ i, ∑ j, paramAdj G a b t i j = d i + t * edgeDegrees a b i := by
  intro i
  have hr : (G.adjMatrix ℝ *ᵥ (fun _ => 1)) i = d i := by
    simpa [Matrix.mulVec, dotProduct] using hrow i
  calc
    _ = (paramAdj G a b t *ᵥ (fun _ => 1)) i := by simp [Matrix.mulVec, dotProduct]
    _ = _ := by
      simp only [paramAdj, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.single_mulVec_eq, Pi.add_apply, Pi.smul_apply, mul_one, hr]
      simp [edgeDegrees, smul_eq_mul]

private theorem paramAdj_laplacian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (d : Fin n → ℝ) (t : ℝ) :
    Matrix.diagonal (fun i => d i + t * edgeDegrees a b i) - paramAdj G a b t =
      (Matrix.diagonal d - G.adjMatrix ℝ) +
      t • Matrix.vecMulVec (Finset.weightedVSubVSubWeights ℝ a b) (Finset.weightedVSubVSubWeights ℝ a b) := by
  have hE : Matrix.diagonal (edgeDegrees a b) -
      (Matrix.single a b 1 + Matrix.single b a 1) =
      Matrix.vecMulVec (Finset.weightedVSubVSubWeights ℝ a b) (Finset.weightedVSubVSubWeights ℝ a b) := by
    have hdiag : Matrix.diagonal (edgeDegrees a b) =
        Matrix.single a a 1 + Matrix.single b b 1 := by
      simpa only [edgeDegrees, Pi.add_def, Matrix.diagonal_single] using
        (Matrix.diagonal_add (α := ℝ) (Pi.single a (1 : ℝ))
          (Pi.single b (1 : ℝ))).symm
    rw [hdiag]
    simp only [Finset.weightedVSubVSubWeights, Matrix.sub_vecMulVec, Matrix.vecMulVec_sub,
      ← Matrix.single_eq_single_vecMulVec_single]
    abel
  have hDiag : Matrix.diagonal (fun i => d i + t * edgeDegrees a b i) =
      Matrix.diagonal d + t • Matrix.diagonal (edgeDegrees a b) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.diagonal_smul] using
      (Matrix.diagonal_add d (t • edgeDegrees a b)).symm
  rw [hDiag, paramAdj]
  linear_combination (norm := module) t • hE


private theorem update_from_voltage (L X : Matrix (Fin n) (Fin n) ℝ) (p b : Fin n → ℝ)
    (E : Matrix (Fin n) (Fin n) ℝ) (r t : ℝ)
    (hLX : L * X = 1 - E) (hLp : L *ᵥ p = -b)
    (hbX : b ᵥ* X = -p) (hbp : b ⬝ᵥ p = -r) (ht : 1 + r * t ≠ 0) :
    (L + t • Matrix.vecMulVec b b) *
      (X - (t / (1 + r * t)) • Matrix.vecMulVec p p) = 1 - E := by
  apply edge_update_grounded L X (Matrix.vecMulVec b b) (Matrix.vecMulVec p p) E r t hLX
  · rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hLp, hbX]
    ext i j
    simp [Matrix.vecMulVec]
  · rw [Matrix.vecMulVec_mul_vecMulVec, hbp, Matrix.vecMulVec_mul, hbX]
    ext i j
    simp [Matrix.vecMulVec]
    ring
  · exact ht

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def weightedGreenValue (d : ι → ℝ) (X : Matrix ι ι ℝ) : ℝ :=
  (∑ i, d i * X i i) - (∑ i, ∑ j, d i * X i j * d j) / (∑ i, d i)

private noncomputable def weightedGreenDerivative {R : Type*} [Field R]
    (d h p : ι → R) (X : Matrix ι ι R) : R :=
  (∑ i, (h i * X i i + d i * (-(p i * p i)))) -
  ((∑ i, ∑ j, ((h i * X i j + d i * (-(p i * p j))) * d j +
      (d i * X i j) * h j)) * (∑ i, d i) -
    (∑ i, ∑ j, d i * X i j * d j) * (∑ i, h i)) / (∑ i, d i)^2

omit [DecidableEq ι] in
private theorem weightedGreenValue_hasDerivAt (d h p : ι → ℝ) (X : Matrix ι ι ℝ)
    (r : ℝ) (hM : (∑ i, d i) ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      weightedGreenValue (fun i => d i + t * h i)
        (fun i j => X i j - (t / (1 + r * t)) * p i * p j))
      (weightedGreenDerivative d h p X) 0 := by
  have ht := hasDerivAt_id (0 : ℝ)
  have hd (i : ι) : HasDerivAt (fun t : ℝ => d i + t * h i) (h i) 0 := by
    simpa only [Pi.add_def, id_eq, one_mul, zero_add] using
      (hasDerivAt_const (0 : ℝ) (d i)).add (ht.mul_const (h i))
  have hf : HasDerivAt (fun t : ℝ => t / (1 + r * t)) 1 0 := by
    have hden : HasDerivAt (fun t : ℝ => 1 + r * t) r 0 := by
      simpa only [Pi.add_def, id_eq, mul_one, zero_add] using
        (hasDerivAt_const (0 : ℝ) 1).add (ht.const_mul r)
    simpa only [id_eq, mul_zero, add_zero, zero_mul, one_mul, sub_zero, one_pow, div_one] using
      ht.fun_div hden (by norm_num)
  have hX (i j : ι) :
      HasDerivAt (fun t : ℝ => X i j - (t / (1 + r * t)) * p i * p j) (-(p i * p j)) 0 := by
    simpa only [Pi.sub_def, one_mul, zero_sub] using
      (hasDerivAt_const (0 : ℝ) (X i j)).sub ((hf.mul_const (p i)).mul_const (p j))
  have htr := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hd i).mul (hX i i))
  have hnum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hd i).mul (hX i j)).mul (hd j)))
  have hden := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  have hnz : (∑ i, (d i + (0 : ℝ) * h i)) ≠ 0 := by simpa using hM
  have hfin := htr.sub (hnum.div hden hnz)
  simpa only [weightedGreenValue, weightedGreenDerivative, Pi.sub_def, Pi.mul_apply, Pi.div_apply, mul_zero, add_zero,
    zero_div, zero_mul, sub_zero] using hfin


end

section

open Matrix

@[reducible] private def rel (i j : Fin 23) : Prop :=
  (i.val < 8 ∧ j.val < 8) ∨
  (8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16) ∨
  (i = 0 ∧ j = 16) ∨ (i = 8 ∧ j = 22) ∨
  (16 ≤ i.val ∧ i.val + 1 = j.val)

@[reducible] private def barbell : SimpleGraph (Fin 23) := SimpleGraph.fromRel rel


private def degB (i : Fin 23) : ℚ :=
  if i = 0 ∨ i = 8 then 8 else if i.val < 16 then 7 else 2

private def posB (i : Fin 23) : ℚ :=
  if i.val < 8 then 0 else if i.val < 16 then 8 else (i.val - 15 : ℕ)

private def greenB : Matrix (Fin 23) (Fin 23) ℚ := fun i j =>
  min (posB i) (posB j) +
  if (0 < i.val ∧ i.val < 8 ∧ 0 < j.val ∧ j.val < 8) ∨
      (8 < i.val ∧ i.val < 16 ∧ 8 < j.val ∧ j.val < 16)
  then (if i = j then 2 else 1) / 8 else 0


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem greenB_row0 : ∀ j, ((diagonal degB - barbell.adjMatrix ℚ) * greenB) 0 j =
    (1 - vecMulVec (Pi.single 0 1) (fun _ : Fin 23 => 1) : Matrix (Fin 23) (Fin 23) ℚ) 0 j := by
  decide +kernel

private theorem barbell_connected : barbell.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable barbell).2
  refine ⟨0, ?_⟩
  have h16 : barbell.Reachable 0 16 := (show barbell.Adj 0 16 by decide).reachable
  have h17 : barbell.Reachable 0 17 := h16.trans (show barbell.Adj 16 17 by decide).reachable
  have h18 : barbell.Reachable 0 18 := h17.trans (show barbell.Adj 17 18 by decide).reachable
  have h19 : barbell.Reachable 0 19 := h18.trans (show barbell.Adj 18 19 by decide).reachable
  have h20 : barbell.Reachable 0 20 := h19.trans (show barbell.Adj 19 20 by decide).reachable
  have h21 : barbell.Reachable 0 21 := h20.trans (show barbell.Adj 20 21 by decide).reachable
  have h22 : barbell.Reachable 0 22 := h21.trans (show barbell.Adj 21 22 by decide).reachable
  have h8 : barbell.Reachable 0 8 := h22.trans (show barbell.Adj 22 8 by decide).reachable
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact (show barbell.Adj 0 1 by decide).reachable
  · exact (show barbell.Adj 0 2 by decide).reachable
  · exact (show barbell.Adj 0 3 by decide).reachable
  · exact (show barbell.Adj 0 4 by decide).reachable
  · exact (show barbell.Adj 0 5 by decide).reachable
  · exact (show barbell.Adj 0 6 by decide).reachable
  · exact (show barbell.Adj 0 7 by decide).reachable
  · exact h8
  · exact h8.trans (show barbell.Adj 8 9 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 10 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 11 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 12 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 13 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 14 by decide).reachable
  · exact h8.trans (show barbell.Adj 8 15 by decide).reachable
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22

private theorem derivative_comparison : (-7683669 / 4096 : ℝ) < -77763 / 44 := by
  norm_num


end


section

open Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem barbell_degree_vector : barbell.adjMatrix ℚ *ᵥ (fun _ => 1) = degB := by
  funext i
  exact (SimpleGraph.adjMatrix_mulVec_const_apply
    (G := barbell) (α := ℚ) (a := 1) (v := i)).trans (by fin_cases i <;> decide +kernel)

private theorem barbell_grounded_inverse : (diagonal degB - barbell.adjMatrix ℚ) * greenB =
    (1 - vecMulVec (Pi.single 0 1) (fun _ : Fin 23 => 1) : Matrix (Fin 23) (Fin 23) ℚ) := by
  ext i j
  fin_cases i
  · exact greenB_row0 j
  all_goals (revert j; decide +kernel)

private theorem barbell_voltage : (diagonal degB - barbell.adjMatrix ℚ) *ᵥ posB = -(Pi.single 0 1 - Pi.single 8 1) := by
  decide +kernel

private theorem barbell_green_voltage : (Pi.single 0 1 - Pi.single 8 1) ᵥ* greenB = -posB := by
  decide +kernel

private def degP (i : Fin 23) : ℚ := if i = 0 ∨ i = 22 then 1 else 2

private def greenP : Matrix (Fin 23) (Fin 23) ℚ := fun i j => min (i.val : ℚ) (j.val : ℚ)


private theorem path_degree_vector : (SimpleGraph.pathGraph 23).adjMatrix ℚ *ᵥ (fun _ => 1) = degP := by
  funext i
  exact (SimpleGraph.adjMatrix_mulVec_const_apply
    (G := (SimpleGraph.pathGraph 23)) (α := ℚ) (a := 1) (v := i)).trans (by fin_cases i <;> decide +kernel)

private theorem path_grounded_inverse : (diagonal degP - (SimpleGraph.pathGraph 23).adjMatrix ℚ) * greenP =
    (1 - vecMulVec (Pi.single 0 1) (fun _ : Fin 23 => 1) : Matrix (Fin 23) (Fin 23) ℚ) := by
  decide +kernel

private theorem path_voltage : (diagonal degP - (SimpleGraph.pathGraph 23).adjMatrix ℚ) *ᵥ (fun i : Fin 23 => (i.val : ℚ)) = -(Pi.single 0 1 - Pi.single 22 1) := by
  decide +kernel

private theorem path_green_voltage : (Pi.single 0 1 - Pi.single 22 1) ᵥ* greenP = -(fun i : Fin 23 => (i.val : ℚ)) := by
  decide +kernel


end

section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem derivativeB_Q : weightedGreenDerivative degB (Pi.single 0 1 + Pi.single 8 1) posB greenB = -7683669 / 4096 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem derivativeP_Q : weightedGreenDerivative degP (Pi.single 0 1 + Pi.single 22 1) (fun i : Fin 23 => (i.val : ℚ)) greenP = -77763 / 44 := by
  decide +kernel


end

section

open Matrix
open scoped Topology

private theorem kemeny_edge_hasDerivAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (d p : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hd : ∀ i, 0 < d i) (hrow : ∀ i, ∑ j, G.adjMatrix ℝ i j = d i)
    (hLX : (Matrix.diagonal d - G.adjMatrix ℝ) * X =
      1 - Matrix.vecMulVec (Pi.single a 1) (fun _ => 1))
    (hLp : (Matrix.diagonal d - G.adjMatrix ℝ) *ᵥ p = -Finset.weightedVSubVSubWeights ℝ a b)
    (hbX : Finset.weightedVSubVSubWeights ℝ a b ᵥ* X = -p)
    (hbp : Finset.weightedVSubVSubWeights ℝ a b ⬝ᵥ p = -r) :
    HasDerivAt (fun t : ℝ => kemeny (paramAdj G a b t))
      (weightedGreenDerivative d (edgeDegrees a b) p X) 0 := by
  classical
  letI : Nonempty (Fin n) := ⟨a⟩
  have hM : (∑ i, d i) ≠ 0 :=
    (Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty).ne'
  apply (weightedGreenValue_hasDerivAt d (edgeDegrees a b) p X r hM).congr_of_eventuallyEq
  have hdegrees : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < d i + t * edgeDegrees a b i := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun t : ℝ => d i + t * edgeDegrees a b i) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    exact continuousAt_const.eventually_lt hcont (by simpa using hd i)
  have hden : ∀ᶠ t : ℝ in 𝓝 0, 1 + r * t ≠ 0 := by
    have hcont : ContinuousAt (fun t : ℝ => 1 + r * t) 0 :=
      continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    exact hcont.eventually_ne (by norm_num)
  filter_upwards [hdegrees, hden] with t hdt ht
  have hupdate := update_from_voltage
    (Matrix.diagonal d - G.adjMatrix ℝ) X p (Finset.weightedVSubVSubWeights ℝ a b)
    (Matrix.vecMulVec (Pi.single a 1) (fun _ => 1)) r t hLX hLp hbX hbp ht
  rw [← paramAdj_laplacian G a b d t] at hupdate
  have hk := kemeny_eq_grounded (paramAdj G a b t)
    (fun i => d i + t * edgeDegrees a b i)
    (X - (t / (1 + r * t)) • Matrix.vecMulVec p p) a
    (paramAdj_isSymm G a b t) hdt (paramAdj_degrees G a b d hrow t) hupdate
  simpa only [weightedGreenValue, dotProduct, Matrix.mulVec, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc] using hk


end

set_option maxRecDepth 10000

section

open Matrix

private theorem cast_grounded_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (d p : Fin n → ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (hdeg : G.adjMatrix ℚ *ᵥ (fun _ => 1) = d)
    (hLX : (Matrix.diagonal d - G.adjMatrix ℚ) * X =
      1 - Matrix.vecMulVec (Pi.single a 1) (fun _ => 1))
    (hLp : (Matrix.diagonal d - G.adjMatrix ℚ) *ᵥ p = -(Pi.single a 1 - Pi.single b 1))
    (hbX : (Pi.single a 1 - Pi.single b 1) ᵥ* X = -p) :
    let dr : Fin n → ℝ := fun i => d i
    let pr : Fin n → ℝ := fun i => p i
    let Xr : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => X i j
    (∀ i, ∑ j, G.adjMatrix ℝ i j = dr i) ∧
    (Matrix.diagonal dr - G.adjMatrix ℝ) * Xr =
      1 - Matrix.vecMulVec (Pi.single a 1) (fun _ => 1) ∧
    (Matrix.diagonal dr - G.adjMatrix ℝ) *ᵥ pr = -Finset.weightedVSubVSubWeights ℝ a b ∧
    Finset.weightedVSubVSubWeights ℝ a b ᵥ* Xr = -pr := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hdeg i)
    simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, apply_ite] using h
  · ext i j
    have h := congrArg (fun q : ℚ => (q : ℝ))
      (congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i j) hLX)
    simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one, Matrix.of_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      Pi.single_apply, apply_ite] using h
  · ext i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hLp i)
    simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one, Pi.sub_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, Finset.weightedVSubVSubWeights, Pi.single_apply, apply_ite] using h
  · ext i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hbX i)
    simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one, Pi.sub_apply, Pi.neg_apply, Matrix.of_apply, Matrix.vecMul, dotProduct, Finset.weightedVSubVSubWeights, Pi.single_apply, apply_ite] using h

end

section

open Matrix

private theorem derivativeB_real : weightedGreenDerivative (fun i : Fin 23 => (degB i : ℝ)) (edgeDegrees 0 8) (fun i : Fin 23 => (posB i : ℝ)) (fun i j : Fin 23 => (greenB i j : ℝ)) = -7683669 / 4096 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) derivativeB_Q
  simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
    Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, Pi.add_apply,
    weightedGreenDerivative,
    edgeDegrees, Pi.single_apply, apply_ite] using h

private theorem derivativeP_real : weightedGreenDerivative (fun i : Fin 23 => (degP i : ℝ)) (edgeDegrees 0 22) (fun i : Fin 23 => (i.val : ℝ)) (fun i j : Fin 23 => (greenP i j : ℝ)) = -77763 / 44 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) derivativeP_Q
  simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
    Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, Pi.add_apply,
    weightedGreenDerivative,
    edgeDegrees, Pi.single_apply, apply_ite] using h

private theorem barbell_hasDerivAt :
    HasDerivAt (fun t => kemeny (paramAdj barbell 0 8 t)) (-7683669 / 4096) 0 := by
  have hdata := cast_grounded_data barbell (0 : Fin 23) 8 degB posB greenB
    barbell_degree_vector barbell_grounded_inverse barbell_voltage barbell_green_voltage
  have hd : ∀ i, 0 < (fun i : Fin 23 => (degB i : ℝ)) i := by
    intro i
    fin_cases i <;> norm_num [degB]
  have hbp : Finset.weightedVSubVSubWeights ℝ (0 : Fin 23) 8 ⬝ᵥ (fun i : Fin 23 => (posB i : ℝ)) = -(8 : ℝ) := by
    simp [Finset.weightedVSubVSubWeights, sub_dotProduct, single_dotProduct, posB]
  have h := kemeny_edge_hasDerivAt barbell (0 : Fin 23) 8 (fun i : Fin 23 => (degB i : ℝ)) (fun i : Fin 23 => (posB i : ℝ)) (fun i j : Fin 23 => (greenB i j : ℝ)) 8
    hd hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hbp
  rw [derivativeB_real] at h
  exact h

private theorem path_hasDerivAt :
    HasDerivAt (fun t => kemeny (paramAdj (SimpleGraph.pathGraph 23) 0 22 t)) (-77763 / 44) 0 := by
  have hdata := cast_grounded_data (SimpleGraph.pathGraph 23) (0 : Fin 23) 22 degP (fun i : Fin 23 => (i.val : ℚ)) greenP
    path_degree_vector path_grounded_inverse path_voltage path_green_voltage
  have hd : ∀ i, 0 < (fun i : Fin 23 => (degP i : ℝ)) i := by
    intro i
    fin_cases i <;> norm_num [degP]
  have hbp : Finset.weightedVSubVSubWeights ℝ (0 : Fin 23) 22 ⬝ᵥ (fun i : Fin 23 => (i.val : ℝ)) = -(22 : ℝ) := by
    simp [Finset.weightedVSubVSubWeights, sub_dotProduct, single_dotProduct]
  have h := kemeny_edge_hasDerivAt (SimpleGraph.pathGraph 23) (0 : Fin 23) 22 (fun i : Fin 23 => (degP i : ℝ)) (fun i : Fin 23 => (i.val : ℝ)) (fun i j : Fin 23 => (greenP i j : ℝ)) 22
    hd hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hbp
  rw [derivativeP_real] at h
  exact h


end

section

theorem result : ¬ claim := by
  intro h
  have hle := h 23 (by decide) barbell (0 : Fin 23) 8
    (-7683669 / 4096) (-77763 / 44) barbell_connected
    (by decide) barbell_hasDerivAt path_hasDerivAt
  exact (not_le_of_gt derivative_comparison) hle


end

end D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
