/- GID: D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN
   generality: G
   mirror-B: D5/B/S3/Quantum/GaussianStates/PageMultiEntropyLargeN
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Page and equal-tripartition multi-entropy have explicit large-mode error bounds. -/

/-
admission_basis: open-problem-resolution (#22644; Proved).
proof_shape: every explicit declaration is bind-only.
escape_witness: none.
The claim retains the quantified formulas of #22644 under this file's namespace.
The integral-defined Gaussian quantity is reused from GaussianMultiEntropyAsymptotic.
The finite formula applies ReplicaThree.GM3_three_closed, whose proof uses the
all-order ResidualLimit.GM3_eq_fourierGM Fourier product identity.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22846

abs_log_add_le: proof_shape: bind-only; escape_witness: none; consumers: page_error, me_error.
  Direct frozen dependencies: none.
abs_log_sub_inv_le: proof_shape: bind-only; escape_witness: none; consumers: page_error, me_error.
  Direct frozen dependencies: none.
page_error: proof_shape: bind-only; escape_witness: none; consumers: result.
  Direct frozen dependencies: none.
me_error: proof_shape: bind-only; escape_witness: none; consumers: result.
  Direct frozen dependencies: none.
finite_gm: proof_shape: bind-only; escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.GM3 [sha256:cac148d5721ad7e5ff818b4214a43a6ebdd01212812a5973ab782765d441d757]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_closed [sha256:d36ebed88eb9de77dfd0dd7f92d1b926be66ca635ce9244c1dfbb16b636cfb35]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.kappa [sha256:3f4f5c032b0f35bbd798a3d02b7385f37edcd72bbf340a1df2255100694bbd5a]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.pairSum [sha256:94523917795d6c986b7686398ef707f5d6f07ce27664758f0a803ab67fdf9c0f]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.cut [sha256:a2c44c5417fdc4ce9ea924d3fecd29f076e0186af4f75cef64a1fd6c71da21ca]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.GM3_eq_fourierGM [sha256:ad7d547b3e08f7bf91339970d43dba830bf1808e028d0db7fe0e8ca60a6ce589]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.fourierGM [sha256:96b58ad055430893f78439ff0571fa88c337c0f96754950623f22fbde776b8be]
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
  Direct frozen dependencies:
    D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.GM3 [sha256:cac148d5721ad7e5ff818b4214a43a6ebdd01212812a5973ab782765d441d757]
result: proof_shape: bind-only; escape_witness: none; consumers: none (settling result).
  Direct frozen dependencies:
    D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.GM3 [sha256:cac148d5721ad7e5ff818b4214a43a6ebdd01212812a5973ab782765d441d757]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.GM3_three_closed [sha256:d36ebed88eb9de77dfd0dd7f92d1b926be66ca635ce9244c1dfbb16b636cfb35]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.kappa [sha256:3f4f5c032b0f35bbd798a3d02b7385f37edcd72bbf340a1df2255100694bbd5a]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.pairSum [sha256:94523917795d6c986b7686398ef707f5d6f07ce27664758f0a803ab67fdf9c0f]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.cut [sha256:a2c44c5417fdc4ce9ea924d3fecd29f076e0186af4f75cef64a1fd6c71da21ca]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.GM3_eq_fourierGM [sha256:ad7d547b3e08f7bf91339970d43dba830bf1808e028d0db7fe0e8ca60a6ce589]
    D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.fourierGM [sha256:96b58ad055430893f78439ff0571fa88c337c0f96754950623f22fbde776b8be]
-/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ResidualLimit
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option Elab.async false

noncomputable section

namespace D5.S3.Quantum.GaussianStates.PageMultiEntropyLargeN

open D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
open D5.S3.Quantum.Entanglement.GaussianMultiEntropy

private theorem abs_log_add_le (h : ℝ) (hh : 0 ≤ h) : |Real.log (1+h)| ≤ h := by
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  have := Real.log_le_sub_one_of_pos (show 0 < 1+h by linarith)
  linarith

private theorem abs_log_sub_inv_le (N : ℝ) (hN : 2 ≤ N) :
    |Real.log (1-1/N)| ≤ 2/N := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hfrac : 0 < 1-1/N := by apply sub_pos.mpr; exact (div_lt_one hN0).mpr (by linarith)
  have hfrac1 : 1-1/N ≤ 1 := by linarith [div_pos (by norm_num : (0:ℝ)<1) hN0]
  rw [abs_of_nonpos (Real.log_nonpos hfrac.le hfrac1)]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hfrac)
  rw [Real.log_inv] at hl
  have heq : (1-1/N)⁻¹-1 = 1/(N-1) := by field_simp; ring
  rw [heq] at hl
  have hbound : 1/(N-1) ≤ 2/N := by
    apply (div_le_div_iff₀ hN1 hN0).mpr
    linarith
  exact hl.trans hbound


private theorem page_error (N d : ℝ) (hN : 2 ≤ N) (hd : 0 < d) :
    let z := 3*d*N^2/(64*(N-1))
    |(1/12:ℝ)*Real.log ((1+5*z)^2/((1+4*z)*(1+3*z)^2)) +
      (1/12:ℝ)*Real.log (N*d) - (1/12:ℝ)*Real.log (400/27:ℝ)| ≤
      ((2+30/d)/12)/N := by
  let z := 3*d*N^2/(64*(N-1))
  have hn : 0<N := by linarith
  have hn1 : 0<N-1 := by linarith
  have hz : 0<z := by dsimp [z]; positivity
  have hz5 : 0<1+5*z := by positivity
  have hz4 : 0<1+4*z := by positivity
  have hz3 : 0<1+3*z := by positivity
  have hnfrac : 0<1-1/N := by apply sub_pos.mpr; exact (div_lt_one hn).mpr (by linarith)
  have hfactor : ((1+5*z)^2/((1+4*z)*(1+3*z)^2)) * (N*d)/(400/27:ℝ) =
      (1-1/N)*(1+1/(5*z))^2 / ((1+1/(4*z))*(1+1/(3*z))^2) := by
    dsimp [z]
    field_simp
    ring
  have hI5 : 0<1+1/(5*z) := by positivity
  have hI4 : 0<1+1/(4*z) := by positivity
  have hI3 : 0<1+1/(3*z) := by positivity
  have hF : 0<(1+5*z)^2/((1+4*z)*(1+3*z)^2) := by positivity
  have hleft : Real.log (((1+5*z)^2/((1+4*z)*(1+3*z)^2))*(N*d)/(400/27:ℝ)) =
      Real.log ((1+5*z)^2/((1+4*z)*(1+3*z)^2)) + Real.log (N*d) - Real.log (400/27:ℝ) := by
    rw [Real.log_div (mul_pos hF (mul_pos hn hd)).ne' (by norm_num),
      Real.log_mul hF.ne' (mul_pos hn hd).ne']
  have hright : Real.log ((1-1/N)*(1+1/(5*z))^2/((1+1/(4*z))*(1+1/(3*z))^2)) =
      Real.log (1-1/N) + 2*Real.log (1+1/(5*z)) - Real.log (1+1/(4*z)) -
        2*Real.log (1+1/(3*z)) := by
    rw [Real.log_div (mul_pos hnfrac (pow_pos hI5 2)).ne' (mul_pos hI4 (pow_pos hI3 2)).ne',
      Real.log_mul hnfrac.ne' (pow_pos hI5 2).ne',Real.log_pow,
      Real.log_mul hI4.ne' (pow_pos hI3 2).ne',Real.log_pow]
    ring
  have hlog := congrArg Real.log hfactor
  rw [hleft,hright] at hlog
  have h0 := abs_log_sub_inv_le N hN
  have h5 := abs_log_add_le (1/(5*z)) (by positivity)
  have h4 := abs_log_add_le (1/(4*z)) (by positivity)
  have h3 := abs_log_add_le (1/(3*z)) (by positivity)
  obtain ⟨h5l,h5u⟩ := abs_le.mp h5
  obtain ⟨h4l,h4u⟩ := abs_le.mp h4
  obtain ⟨h3l,h3u⟩ := abs_le.mp h3
  obtain ⟨h0l,h0u⟩ := abs_le.mp h0
  have hb : 2/N + 2/(5*z)+1/(4*z)+2/(3*z) ≤ (2+30/d)/N := by
    dsimp [z]
    field_simp
    nlinarith
  change |(1/12:ℝ)*Real.log ((1+5*z)^2/((1+4*z)*(1+3*z)^2)) +
      (1/12:ℝ)*Real.log (N*d) - (1/12:ℝ)*Real.log (400/27:ℝ)| ≤ _
  apply abs_le.mpr
  constructor
  · ring_nf at hlog hb h5l h5u h4l h4u h3l h3u h0l h0u ⊢
    linarith only [hlog,hb,h5l,h5u,h4l,h4u,h3l,h3u,h0l,h0u]
  · ring_nf at hlog hb h5l h5u h4l h4u h3l h3u h0l h0u ⊢
    linarith only [hlog,hb,h5l,h5u,h4l,h4u,h3l,h3u,h0l,h0u]

private theorem me_error (N d : ℝ) (hN : 2 ≤ N) (hd : 0 < d) :
    let z := d*N^2/(12*(N-1))
    |(1/12:ℝ)*Real.log ((1+3*z)^2/(1+2*z)^3) +
      (1/12:ℝ)*Real.log (N*d) - (1/12:ℝ)*Real.log (27/2:ℝ)| ≤
      ((2+30/d)/12)/N := by
  let z := d*N^2/(12*(N-1))
  have hn : 0<N := by linarith
  have hn1 : 0<N-1 := by linarith
  have hz : 0<z := by dsimp [z]; positivity
  have hz2 : 0<1+2*z := by positivity
  have hz3 : 0<1+3*z := by positivity
  have hnfrac : 0<1-1/N := by apply sub_pos.mpr; exact (div_lt_one hn).mpr (by linarith)
  have hfactor : ((1+3*z)^2/(1+2*z)^3) * (N*d)/(27/2:ℝ) =
      (1-1/N)*(1+1/(3*z))^2 / (1+1/(2*z))^3 := by
    dsimp [z]
    field_simp
    ring
  have hI3 : 0<1+1/(3*z) := by positivity
  have hI2 : 0<1+1/(2*z) := by positivity
  have hF : 0<(1+3*z)^2/(1+2*z)^3 := by positivity
  have hleft : Real.log (((1+3*z)^2/(1+2*z)^3)*(N*d)/(27/2:ℝ)) =
      Real.log ((1+3*z)^2/(1+2*z)^3) + Real.log (N*d) - Real.log (27/2:ℝ) := by
    rw [Real.log_div (mul_pos hF (mul_pos hn hd)).ne' (by norm_num),
      Real.log_mul hF.ne' (mul_pos hn hd).ne']
  have hright : Real.log ((1-1/N)*(1+1/(3*z))^2/(1+1/(2*z))^3) =
      Real.log (1-1/N) + 2*Real.log (1+1/(3*z)) - 3*Real.log (1+1/(2*z)) := by
    rw [Real.log_div (mul_pos hnfrac (pow_pos hI3 2)).ne' (pow_pos hI2 3).ne',
      Real.log_mul hnfrac.ne' (pow_pos hI3 2).ne',Real.log_pow,Real.log_pow]
    ring
  have hlog := congrArg Real.log hfactor
  rw [hleft,hright] at hlog
  have h0 := abs_log_sub_inv_le N hN
  have h3 := abs_log_add_le (1/(3*z)) (by positivity)
  have h2 := abs_log_add_le (1/(2*z)) (by positivity)
  obtain ⟨h3l,h3u⟩ := abs_le.mp h3
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2
  obtain ⟨h0l,h0u⟩ := abs_le.mp h0
  have hb : 2/N + 2/(3*z)+3/(2*z) ≤ (2+30/d)/N := by
    dsimp [z]
    field_simp
    nlinarith
  change |(1/12:ℝ)*Real.log ((1+3*z)^2/(1+2*z)^3) +
      (1/12:ℝ)*Real.log (N*d) - (1/12:ℝ)*Real.log (27/2:ℝ)| ≤ _
  apply abs_le.mpr
  constructor
  · ring_nf at hlog hb h3l h3u h2l h2u h0l h0u ⊢
    linarith only [hlog,hb,h3l,h3u,h2l,h2u,h0l,h0u]
  · ring_nf at hlog hb h3l h3u h2l h2u h0l h0u ⊢
    linarith only [hlog,hb,h3l,h3u,h2l,h2u,h0l,h0u]




private theorem finite_gm (NA NB NC : ℕ) (a : ℝ) (ha : 1 ≤ a)
    (hA : 0<NA) (hB : 0<NB) (hC : 0<NC) :
    GM3 3 NA NB NC a =
      let u := 3*(a^2-1)/(4*((NA : ℝ)+NB+NC-1))
      (1/12:ℝ)*Real.log ((1+u*((NA : ℝ)*NB+(NA : ℝ)*NC+(NB : ℝ)*NC))^2 /
        ((1+u*NA*(NB+NC))*(1+u*NB*(NA+NC))*(1+u*NC*(NA+NB)))) := by
  have hf := ReplicaThree.GM3_three_closed NA NB NC a hA hB hC ha
  rw [ResidualLimit.GM3_eq_fourierGM 3 NA NB NC (by norm_num) a ha hA hB hC] at hf ⊢
  simpa only [ReplicaThree.kappa, ReplicaThreeScalar.pairSum, ReplicaThreeScalar.cut,
    div_eq_mul_inv, mul_comm, one_mul] using hf

/-- The fixed-a Page and equal-tripartition large-mode estimates. -/
def claim : Prop :=
  ∀ (a : ℝ), 1 < a →
    ∃ (K : ℝ), 0 < K ∧
      ∀ (k : ℕ), 0 < k →
        (|GM3 3 (2 * k) k k a +
              (1 / 12 : ℝ) * Real.log ((4 * (k : ℝ)) * (a ^ 2 - 1)) -
              (1 / 12 : ℝ) * Real.log (400 / 27 : ℝ)| ≤
            K / (4 * (k : ℝ))) ∧
        (|GM3 3 k k k a +
              (1 / 12 : ℝ) * Real.log ((3 * (k : ℝ)) * (a ^ 2 - 1)) -
              (1 / 12 : ℝ) * Real.log (27 / 2 : ℝ)| ≤
            K / (3 * (k : ℝ)))

theorem result : claim := by
  intro a ha
  let d := a^2-1
  have hd : 0<d := by dsimp [d]; nlinarith
  refine ⟨(2+30/d)/12,by positivity,?_⟩
  intro k hk
  have hkR : (1:ℝ)≤k := by exact Nat.one_le_cast.mpr hk
  have hp := page_error (4*(k : ℝ)) d (by linarith) hd
  have hm := me_error (3*(k : ℝ)) d (by linarith) hd
  have hgp : GM3 3 (2*k) k k a =
      let z := 3*d*(4*(k : ℝ))^2/(64*(4*(k : ℝ)-1))
      (1/12:ℝ)*Real.log ((1+5*z)^2/((1+4*z)*(1+3*z)^2)) := by
    rw [finite_gm (2*k) k k a ha.le (by omega) hk hk]
    dsimp only
    push_cast
    let u : ℝ := 3*(a^2-1)/(4*((2:ℝ)*k+k+k-1))
    let z : ℝ := 3*d*(4*(k:ℝ))^2/(64*(4*(k:ℝ)-1))
    have hsum : (2:ℝ)*k+k+k-1=4*k-1 := by ring
    have hn4 : (4:ℝ)*k-1 ≠ 0 := by linarith
    have hu : u*(k:ℝ)^2=z := by
      dsimp only [u,z,d]
      rw [hsum]
      field_simp [hn4]; ring
    change (1/12:ℝ)*Real.log ((1+u*((2*(k:ℝ))*k+(2*(k:ℝ))*k+(k:ℝ)*k))^2 /
      ((1+u*(2*k)*(k+k))*(1+u*k*(2*k+k))*(1+u*k*(2*k+k)))) =
      (1/12:ℝ)*Real.log ((1+5*z)^2/((1+4*z)*(1+3*z)^2))
    rw [←hu]
    congr 2
    congr 1 <;> ring
  have hgm : GM3 3 k k k a =
      let z := d*(3*(k : ℝ))^2/(12*(3*(k : ℝ)-1))
      (1/12:ℝ)*Real.log ((1+3*z)^2/(1+2*z)^3) := by
    rw [finite_gm k k k a ha.le hk hk hk]
    dsimp only
    let u : ℝ := 3*(a^2-1)/(4*((k:ℝ)+k+k-1))
    let z : ℝ := d*(3*(k:ℝ))^2/(12*(3*(k:ℝ)-1))
    have hsum : (k:ℝ)+k+k-1=3*k-1 := by ring
    have hn3 : (3:ℝ)*k-1 ≠ 0 := by linarith
    have hu : u*(k:ℝ)^2=z := by
      dsimp only [u,z,d]
      rw [hsum]
      field_simp [hn3]; ring
    change (1/12:ℝ)*Real.log ((1+u*((k:ℝ)*k+(k:ℝ)*k+(k:ℝ)*k))^2 /
      ((1+u*k*(k+k))*(1+u*k*(k+k))*(1+u*k*(k+k)))) =
      (1/12:ℝ)*Real.log ((1+3*z)^2/(1+2*z)^3)
    rw [←hu]
    congr 2
    congr 1 <;> ring
  constructor
  · rw [hgp]
    exact hp
  · rw [hgm]
    exact hm

end D5.S3.Quantum.GaussianStates.PageMultiEntropyLargeN
