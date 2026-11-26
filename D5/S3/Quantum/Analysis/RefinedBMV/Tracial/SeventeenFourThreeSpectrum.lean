/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SeventeenFourThreeSpectrum
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree-seventeen four-copy comparison for ordered three-value Hermitian spectral data. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusKernel
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleCycleAllocation
import D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning

/-! Transfer of the normalized surplus inequalities to three positive
spectral values, with the singular case obtained by a scalar limit. -/

namespace RefinedBMV.Tracial.TriangleSurplus

open Matrix FourCopyGap ThreeBlockGram
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open private kernelSurplus_eq from
  D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusAllocation
open private gapDefect_scale allocation_scale from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
open private eigenDiagonal rootDiagonal gapTrace wordMean_conjugation from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

private theorem binaryForm_nonneg {a b c : ℝ} (ha : 0 < a) (hdet : (c / 2) ^ 2 ≤ a * b)
    (u v : ℝ) : 0 ≤ a * u ^ 2 + c * u * v + b * v ^ 2 := by
  have hb : 0 ≤ b - (c / 2) ^ 2 / a := by
    exact sub_nonneg.mpr ((div_le_iff₀ ha).2 (by simpa [mul_comm] using hdet))
  calc
    0 ≤ a * (u + (c / 2) / a * v) ^ 2 + (b - (c / 2) ^ 2 / a) * v ^ 2 := by positivity
    _ = _ := by field_simp [ha.ne']; ring

private theorem normalized_allocation (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
    (hs : 0 < (surplus x y).1 ∧ 0 ≤ (surplus x y).2.1 ∧ 0 ≤ (surplus x y).2.2) :
    ∃ alloc, Allocation (spectralDefect 17 ![1, x ^ 4, (x * y) ^ 4]) alloc := by
  let knots : Fin 3 → ℝ := ![1, x ^ 4, (x * y) ^ 4]
  let K := spectralDefect 17 knots
  let w : Fin 3 → ℝ := ![4, 4, 3 + y ^ 17]
  let M := triangleMatrix K w
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hxy : x < x * y := by simpa using mul_lt_mul_of_pos_left hy hx0
  have h01 : (1 : ℝ) < x ^ 4 := by
    simpa using pow_lt_pow_left₀ hx zero_le_one (by decide : (4 : ℕ) ≠ 0)
  have h12 : x ^ 4 < (x * y) ^ 4 := pow_lt_pow_left₀ hxy hx0.le (by decide)
  have hk (i : Fin 3) : 0 < knots i := by
    fin_cases i
    · exact zero_lt_one
    · exact pow_pos hx0 _
    · exact pow_pos (mul_pos hx0 hy0) _
  have hinj : Function.Injective knots := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [knots, h01.ne, h01.ne', h12.ne, h12.ne', (h01.trans h12).ne, (h01.trans h12).ne']
  have hK (i j k l : Fin 3) : 0 ≤ K i j k l :=
    gapDefect_nonneg 17 (hk i).le (hk j).le (hk k).le (hk l).le
  have hbinary (i j : Fin 3) (hij : i ≠ j) : (g K i j) ^ 2 < 2 * f K i j * f K j i :=
    spectralDefect_binary_conditioning 17 (by decide) knots i j (hk i) (hk j) (hinj.ne hij)
  have hf (i j : Fin 3) (hij : i ≠ j) : 0 < f K i j := by
    have hb := hbinary i j hij
    have hn : 0 ≤ f K i j := hK i i i j
    by_contra! hn'
    rw [le_antisymm hn' hn, mul_zero, zero_mul] at hb
    exact (sq_nonneg _).not_gt hb
  have hdet (i j : Fin 3) (hij : i ≠ j) : (g K i j / 2) ^ 2 ≤ f K i j * f K j i := by
    have hb := hbinary i j hij
    nlinarith only [hb, sq_nonneg (g K i j)]
  have hg (i j : Fin 3) : g K i j = g K j i := by
    simp only [g, K, spectralDefect]
    rw [gapDefect_swap12, gapDefect_swap01, gapDefect_swap23, gapDefect_swap12]
  have hsur : surplus x y = kernelSurplus K w := surplus_eq_kernelSurplus hx0.le hy0.le
  rw [hsur] at hs
  have hinvert : M.det ≠ 0 := by
    intro hz
    let T := (2 : ℝ) • M
    let U := T.adjugate *ᵥ triangleDemand K
    have hT : T.det = 0 := by simp [T, hz]
    have hpos := hs.1
    rw [kernelSurplus_eq] at hpos
    change 0 < T.det ^ 2 - 2 * (w 2) ^ 2 * (kernelEdge K 0 1 2).form (U 0) (U 1) at hpos
    have hq := binaryForm_nonneg (hf 0 1 (by decide)) (hdet 0 1 (by decide)) (U 0) (U 1)
    have he : 0 ≤ (kernelEdge K 0 1 2).form (U 0) (U 1) := by
      have hh : 0 ≤ h K 2 0 1 := hK 2 2 0 1
      have hmul := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hh) hq
      simpa [kernelEdge, edge, Edge.form, mul_add, mul_assoc] using hmul
    rw [hT, zero_pow (by decide), zero_sub] at hpos
    exact (neg_nonpos.mpr (mul_nonneg (by positivity) he)).not_gt hpos
  refine ⟨_, allocation_of_kernelSurplus K w hinvert hg hf hdet ?_ ?_ ?_
    hs.1.le hs.2.1 hs.2.2⟩
  · exact hK 2 2 0 1
  · exact hK 1 1 0 2
  · exact hK 0 0 1 2

private theorem positive_allocation
    (hpos : ∀ x y : ℝ, 1 < x → 1 < y →
      0 < (surplus x y).1 ∧ 0 ≤ (surplus x y).2.1 ∧ 0 ≤ (surplus x y).2.2)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∃ alloc, Allocation (spectralDefect 17 ![a, b, c]) alloc := by
  let x := (b / a) ^ (1 / 4 : ℝ)
  let y := (c / b) ^ (1 / 4 : ℝ)
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hx : 1 < x := by
    apply Real.one_lt_rpow _ (by norm_num)
    exact (lt_div_iff₀ ha).2 (by simpa using hab)
  have hy : 1 < y := by
    apply Real.one_lt_rpow _ (by norm_num)
    exact (lt_div_iff₀ hb).2 (by simpa using hbc)
  have root4 (z : ℝ) (hz : 0 ≤ z) : (z ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = z := by
    rw [← Real.rpow_mul_natCast hz, show (1 / 4 : ℝ) * ↑(4 : ℕ) = 1 by norm_num, Real.rpow_one]
  let Z : Fin 3 → ℝ := ![1, x ^ 4, (x * y) ^ 4]
  have hZ (i : Fin 3) : 0 ≤ Z i := by
    fin_cases i
    · exact zero_le_one
    · exact show 0 ≤ x ^ (4 : ℕ) by positivity
    · exact show 0 ≤ (x * y) ^ (4 : ℕ) by positivity
  have hscale (i : Fin 3) : (![a, b, c] : Fin 3 → ℝ) i = a * Z i := by
    have hx4 : x ^ (4 : ℕ) = b / a := root4 _ (div_nonneg hb.le ha.le)
    have hy4 : y ^ (4 : ℕ) = c / b := root4 _ (div_nonneg hc.le hb.le)
    fin_cases i <;> simp [Z, mul_pow, hx4, hy4] <;> field_simp
  obtain ⟨alloc, halloc⟩ := normalized_allocation x y hx hy (hpos x y hx hy)
  have hkernel (i j k l : Fin 3) :
      spectralDefect 17 ![a, b, c] i j k l = a ^ 17 * spectralDefect 17 Z i j k l := by
    unfold spectralDefect
    rw [hscale i, hscale j, hscale k, hscale l]
    exact gapDefect_scale 17 ha.le (hZ i) (hZ j) (hZ k) (hZ l)
  exact ⟨_, allocation_scale (pow_nonneg ha.le _) hkernel halloc⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem diagonal_bound_of_positive_surplus
    (hpos : ∀ x y : ℝ, 1 < x → 1 < y →
      0 < (surplus x y).1 ∧ 0 ≤ (surplus x y).2.1 ∧ 0 ≤ (surplus x y).2.2)
    (label : n → Fin 3) (B : Matrix n n ℂ) (hB : B.IsHermitian)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) :
    trace ((rootDiagonal label ![a, b, c] 17 * B) ^ 4) ≤
      FourCopyGap.wordMean 17 (eigenDiagonal label ![a, b, c]) B := by
  let knots (t : ℝ) : Fin 3 → ℝ := ![a + t, b + t, c + t]
  let D (t : ℝ) := eigenDiagonal label (knots t)
  let R (t : ℝ) := rootDiagonal label (knots t) 17
  let F (t : ℝ) := FourCopyGap.wordMean 17 (D t) B - trace ((R t * B) ^ 4)
  have hel (i : Fin 3) : Continuous fun t => knots t i := by
    fin_cases i <;> simp [knots] <;> fun_prop
  have hD : Continuous D := by
    unfold D eigenDiagonal
    exact (continuous_pi (fun i ↦ Complex.continuous_ofReal.comp (hel (label i)))).matrix_diagonal
  have hR : Continuous R := by
    unfold R rootDiagonal eigenDiagonal
    exact (continuous_pi (fun i ↦ Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity)).comp (hel (label i))))).matrix_diagonal
  have hF : Continuous F := by
    simp only [F, wordMean_eq_gaps, gapTrace, Matrix.trace, Matrix.diag]
    fun_prop
  have hgood {t : ℝ} (ht : 0 < t) : 0 ≤ F t := by
    have h0 : 0 < a + t := add_pos_of_nonneg_of_pos ha ht
    obtain ⟨alloc, halloc⟩ := positive_allocation hpos h0
      (show a + t < b + t by linarith) (show b + t < c + t by linarith)
    have hx (i : Fin 3) : 0 ≤ knots t i := by
      fin_cases i <;> simp [knots] <;> linarith
    exact sub_nonneg.mpr (diagonal_word_bound_of_triangle_allocation 17 label (knots t) hx
      B hB alloc halloc)
  have hclosed : IsClosed {t : ℝ | 0 ≤ F t} := by
    simp only [Complex.nonneg_iff, Set.ofPred_and]
    exact (isClosed_le continuous_const (Complex.continuous_re.comp hF)).inter
      (isClosed_eq continuous_const (Complex.continuous_im.comp hF))
  have hz : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by simp [closure_Ioi]
  have h0 : (0 : ℝ) ∈ {t : ℝ | 0 ≤ F t} :=
    closure_minimal (fun _ ht => hgood ht) hclosed hz
  change 0 ≤ F 0 at h0
  exact sub_nonneg.mp (by simpa only [F, D, R, knots, add_zero] using h0)

/-- The degree-seventeen comparison for a positive semidefinite first factor
with three ordered spectral labels follows from the open-quadrant surpluses.
The second factor is Hermitian and spectral multiplicities are arbitrary. -/
theorem product_bound_of_positive_surplus
    (hpos : ∀ x y : ℝ, 1 < x → 1 < y →
      0 < (surplus x y).1 ∧ 0 ≤ (surplus x y).2.1 ∧ 0 ≤ (surplus x y).2.2)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (label : n → Fin 3)
    (hlabel : ∀ i, hA.isHermitian.eigenvalues i = (![a, b, c] : Fin 3 → ℝ) (label i)) :
    trace (((A ^ ((17 : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean 17 A B := by
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ _ (star U)
  have hd : φ A = eigenDiagonal label ![a, b, c] := by
    rw [H.conjStarAlgAut_star_eigenvectorUnitary]
    congr 1
    funext i
    exact congrArg Complex.ofReal (hlabel i)
  have hB' : (φ B).IsHermitian := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).IsHermitian
    rw [Unitary.conjStarAlgAut_star_apply]
    exact isHermitian_conjTranspose_mul_mul (U : Matrix n n ℂ) hB
  have hr : φ (A ^ ((17 : ℝ) / 4)) = rootDiagonal label ![a, b, c] 17 := by
    rw [CFC.rpow_eq_cfc_real hA.nonneg, H.cfc_eq, Matrix.IsHermitian.cfc]
    have hφ : φ.symm = Unitary.conjStarAlgAut ℂ _ U := by simp [φ]
    change φ (Unitary.conjStarAlgAut ℂ _ U _) = _
    rw [← hφ, StarAlgEquiv.apply_symm_apply]
    congr 1
    funext i
    change ((H.eigenvalues i ^ ((17 : ℝ) / 4) : ℝ) : ℂ) =
      (((![a, b, c] : Fin 3 → ℝ) (label i) ^ ((17 : ℝ) / 4) : ℝ) : ℂ)
    rw [hlabel i]
  have hm : FourCopyGap.wordMean 17 (eigenDiagonal label ![a, b, c]) (φ B) =
      FourCopyGap.wordMean 17 A B := by
    rw [← hd]
    exact wordMean_conjugation 17 (star U) A B
  have ht : trace ((rootDiagonal label ![a, b, c] 17 * φ B) ^ 4) =
      trace (((A ^ ((17 : ℝ) / 4)) * B) ^ 4) := by
    rw [← hr, ← map_mul φ, ← map_pow φ]
    exact RefinedBMV.trace_conjugation (star U) _
  simpa only [ht, hm] using diagonal_bound_of_positive_surplus hpos label (φ B) hB' ha hab hbc

#print axioms product_bound_of_positive_surplus

end

end RefinedBMV.Tracial.TriangleSurplus
