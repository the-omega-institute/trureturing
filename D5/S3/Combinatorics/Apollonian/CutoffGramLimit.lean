/- GID: D5/S3/Combinatorics/Apollonian/CutoffGramLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/CutoffGramLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed]
   utility: none
   digest: The actual fixed-cutoff Gram matrices converge to the face-degree diagonal. -/

module
public import D5.S3.Combinatorics.Apollonian.CutoffSpectralBounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The finite old vertex set is fixed before the later-stage limit is taken. -/
@[expose] public section
noncomputable section
namespace D5.S3.Combinatorics.Apollonian.CutoffGramLimit
open InnerFaceStages Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

/-- The actual old-to-late Gram matrix with the original squared scaling. -/
def normalizedGram (k t : ℕ) : Matrix (Vertex k) (Vertex k) ℝ :=
  ((2 : ℝ) ^ (k+t))⁻¹ • (cutoffBlock k t * (cutoffBlock k t).transpose)

/-- Each limiting weight is the incident inner-face count at the fixed cutoff, divided by 2^k. -/
def limitingDiagonal (k : ℕ) : Matrix (Vertex k) (Vertex k) ℝ :=
  diagonal (fun u => (faceCount k u : ℝ) / (2 : ℝ)^k)

private theorem faceCount_embed (k t : ℕ) (u : Vertex k) :
    faceCount (k+t) (embed k t u) = 2^t * faceCount k u := by
  induction t with
  | zero => simp [embed]
  | succ t ih =>
    change faceCount (k+t+1) (Sum.inl (embed k t u)) = _
    rw [faceCount_old, ih, pow_succ]
    ring

private theorem degreeCount_embed (k t : ℕ) (u : Vertex k) :
    degreeCount (k+t) (embed k t u) + faceCount k u =
      degreeCount k u + 2^t * faceCount k u := by
  induction t with
  | zero => simp [embed]
  | succ t ih =>
    change degreeCount (k+t+1) (Sum.inl (embed k t u)) + _ = _
    rw [degreeCount_old, faceCount_embed, pow_succ]
    nlinarith

private theorem gram_diagonal_formula (k t : ℕ) (u : Vertex k) :
    (cutoffBlock k t * (cutoffBlock k t).transpose) u u =
      ((2 : ℝ)^t - 1) * (faceCount k u : ℝ) := by
  have hd := degreeCount_embed k t u
  have hp : 1 ≤ (2:ℕ)^t := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) t)
  have hle : degreeCount k u ≤ degreeCount (k+t) (embed k t u) := by nlinarith
  rw [cutoff_gram_diag, ← degreeCount_eq_degree, ← degreeCount_eq_degree, Nat.cast_sub hle]
  have hc : (degreeCount (k+t) (embed k t u) : ℝ) + (faceCount k u : ℝ) =
      (degreeCount k u : ℝ) + (2:ℝ)^t * (faceCount k u : ℝ) := by exact_mod_cast hd
  nlinarith

/-- On the fixed actual old vertex set, the normalized Gram matrix converges in Euclidean
 operator topology to the diagonal face weights. -/
theorem normalized_gram_tendsto (k : ℕ) :
    Tendsto (normalizedGram k) atTop (nhds (limitingDiagonal k)) := by
  apply tendsto_pi_nhds.mpr
  intro u
  apply tendsto_pi_nhds.mpr
  intro v
  have hpow : Tendsto (fun t : ℕ => (1/2 : ℝ)^t) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  by_cases huv : u = v
  · subst v
    have he (t : ℕ) : normalizedGram k t u u =
        (faceCount k u : ℝ) / 2^k - ((faceCount k u : ℝ) / 2^k) * (1/2 : ℝ)^t := by
      simp only [normalizedGram, Matrix.smul_apply, smul_eq_mul, gram_diagonal_formula, pow_add]
      rw [div_pow]
      field_simp
      ring
    simp only [limitingDiagonal, diagonal_apply_eq]
    simp_rw [he]
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
  · have hs (t : ℕ) := cutoff_gram_offdiag k t u v huv
    have hl (t : ℕ) : 0 ≤ normalizedGram k t u v := by
      exact mul_nonneg (by positivity) (hs t).1
    have hu (t : ℕ) : normalizedGram k t u v ≤
        (2 / (2:ℝ)^k) * ((t:ℝ) / (2:ℝ)^t) := by
      have hm := mul_le_mul_of_nonneg_left (hs t).2.1
        (show 0 ≤ ((2:ℝ)^(k+t))⁻¹ by positivity)
      convert hm using 1
      dsimp [normalizedGram]
      rw [pow_add]
      field_simp
    have ht : Tendsto (fun t : ℕ => (t:ℝ)/(2:ℝ)^t) atTop (nhds 0) := by
      simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 2)
    have hz := squeeze_zero hl hu (by simpa using ht.const_mul (2/(2:ℝ)^k))
    simpa [limitingDiagonal, diagonal_apply_ne _ huv] using hz

end D5.S3.Combinatorics.Apollonian.CutoffGramLimit
