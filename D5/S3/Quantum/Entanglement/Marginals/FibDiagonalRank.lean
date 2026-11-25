/- GID: D5/S3/Quantum/Entanglement/Marginals/FibDiagonalRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibDiagonalRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two rational norm criteria for diagonal Fibonacci marginals of rank two. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank

/-! Rational rank two for diagonal edge blocks and zero observed couplings. -/

open Matrix Complex
open scoped ComplexOrder ComplexConjugate Matrix
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank (rational_rank_le_two_at_iff)
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank

private abbrev Qubit := Matrix Bool Bool ℂ

/-- The vacuum weight is x and the occupied endpoint has the remaining mass. -/
def diagonalEdgeBlock (b x : ℚ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun i : Bool => ((if i then 1 - b - x else x : ℚ) : ℂ)

private theorem block_rational (b x : ℚ) (i j : Bool) :
    RationalEntry (diagonalEdgeBlock b x i j) := by
  by_cases h : i = j
  · rw [diagonalEdgeBlock, Matrix.diagonal_apply, ite_eq_left h]
    exact SubfieldClass.ratCast_mem rationalComplex _
  · rw [diagonalEdgeBlock, Matrix.diagonal_apply, ite_eq_right h]
    exact rationalComplex.zero_mem

private theorem block_trace (b x : ℚ) :
    (diagonalEdgeBlock b x).trace = 1 - (b : ℂ) := by
  simp [diagonalEdgeBlock, Matrix.trace_diagonal]

private theorem correction_diagonal (b : ℚ) (z : ℂ) :
    let S := Matrix.diagonal (fun i : Bool => (if i then (normSq z / (b : ℝ) : ℝ) else 0 : ℂ))
    partialTraceRight (correction b (middleRow 0 0 0 z)) = S ∧
      partialTraceLeft (correction b (middleRow 0 0 0 z)) = S := by
  have hzz : conj z * z = (normSq z : ℂ) := (mul_comm _ _).trans (mul_conj z)
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [partialTraceRight, partialTraceLeft, correction, middleRow, Matrix.vecMulVec_apply,
      Pi.star_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), hzz, div_eq_inv_mul]

private theorem subtract_diagonal (b x : ℚ) (s : ℝ) :
    diagonalEdgeBlock b x - Matrix.diagonal (fun i : Bool => (if i then (s : ℂ) else 0)) =
      Matrix.diagonal (fun i : Bool =>
        (if i then ((1 - (b : ℝ) - (x : ℝ) - s : ℝ) : ℂ) else (x : ℂ))) := by
  ext i j
  cases i <;> cases j <;> simp [diagonalEdgeBlock]

private theorem det_residual (b x : ℚ) (s : ℝ) :
    (Matrix.diagonal (fun i : Bool =>
        (if i then ((1 - (b : ℝ) - (x : ℝ) - s : ℝ) : ℂ) else (x : ℂ)))).det =
      ((x : ℝ) * (1 - (b : ℝ) - (x : ℝ) - s) : ℝ) := by
  simp [Matrix.det_diagonal, mul_comm]

private theorem rational_rank_two_fixed (b l r : ℚ) (z : ℂ)
    (hb : 0 < b) (hl : 0 < l) (hr : 0 < r) (hne : l ≠ r) (qz : RationalEntry z) :
    (∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧
      MatchesCoherentData b (diagonalEdgeBlock b l) (diagonalEdgeBlock b r) 0 0 0 z ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j)) ↔
    normSq z = (b * (1 - b - l - r) : ℚ) ∧
      (∃ w : ℂ, RationalEntry w ∧ normSq w = (l * r : ℚ)) := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have htrace : (diagonalEdgeBlock b l).trace + (b : ℝ) = 1 := by simp [block_trace]
  have htraceR : (diagonalEdgeBlock b r).trace = (diagonalEdgeBlock b l).trace := by
    rw [block_trace, block_trace]
  have q0 : RationalEntry 0 := rationalComplex.zero_mem
  have hfixed := rational_rank_le_two_at_iff b (diagonalEdgeBlock b l) (diagonalEdgeBlock b r)
    0 0 0 z hbR htrace htraceR (block_rational b l) (block_rational b r) q0 q0 q0 qz
  dsimp only at hfixed
  refine hfixed.trans ?_
  let s := normSq z / (b : ℝ)
  change
    (diagonalEdgeBlock b l - partialTraceRight (correction b (middleRow 0 0 0 z))).PosSemidef ∧
      (diagonalEdgeBlock b r - partialTraceLeft (correction b (middleRow 0 0 0 z))).PosSemidef ∧
      (diagonalEdgeBlock b l - partialTraceRight (correction b (middleRow 0 0 0 z))).det =
        (diagonalEdgeBlock b r - partialTraceLeft (correction b (middleRow 0 0 0 z))).det ∧
      (∃ w : ℂ, RationalEntry w ∧ (normSq w : ℂ) =
        (diagonalEdgeBlock b l - partialTraceRight (correction b (middleRow 0 0 0 z))).det) ↔ _
  rw [(correction_diagonal b z).1, (correction_diagonal b z).2,
    subtract_diagonal, subtract_diagonal, det_residual, det_residual]
  let t : ℝ := 1 - (b : ℝ) - (l : ℝ) - (r : ℝ)
  have heq :
      ((l : ℝ) * (1 - (b : ℝ) - (l : ℝ) - s) : ℝ) =
        ((r : ℝ) * (1 - (b : ℝ) - (r : ℝ) - s) : ℝ) ↔ s = t := by
    constructor
    · intro h
      have hf : ((l : ℝ) - (r : ℝ)) * (t - s) = 0 := by
        dsimp [t]
        linear_combination h
      have hn : (l : ℝ) - (r : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hn)).symm
    · intro h
      rw [h]
      dsimp [t]
      ring
  have hcoupling : s = t ↔ normSq z = (b * (1 - b - l - r) : ℚ) := by
    dsimp only [s, t]
    push_cast
    rw [div_eq_iff hbR.ne', mul_comm]
  have hdet (hs : s = t) : (l : ℝ) * (1 - (b : ℝ) - (l : ℝ) - s) = (l * r : ℚ) := by
    rw [hs]
    dsimp [t]
    push_cast
    ring
  constructor
  · rintro ⟨_, _, hd, w, qw, hw⟩
    have hs := heq.mp (Complex.ofReal_injective hd)
    exact ⟨hcoupling.mp hs, w, qw, (Complex.ofReal_injective hw).trans (hdet hs)⟩
  · rintro ⟨hz, w, qw, hw⟩
    have hs := hcoupling.mpr hz
    have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    have hswapL : (1 - (b : ℝ) - (l : ℝ) - s) = (r : ℝ) := by rw [hs]; dsimp [t]; ring
    have hswapR : (1 - (b : ℝ) - (r : ℝ) - s) = (l : ℝ) := by rw [hs]; dsimp [t]; ring
    refine ⟨?_, ?_, congrArg Complex.ofReal (heq.mpr hs), w, qw,
      congrArg Complex.ofReal (hw.trans (hdet hs).symm)⟩
    · apply Matrix.PosSemidef.diagonal
      intro i
      cases i
      · exact Complex.zero_le_real.mpr hlR.le
      · change 0 ≤ ((1 - (b : ℝ) - (l : ℝ) - s : ℝ) : ℂ)
        rw [hswapL]
        exact Complex.zero_le_real.mpr hrR.le
    · apply Matrix.PosSemidef.diagonal
      intro i
      cases i
      · exact Complex.zero_le_real.mpr hrR.le
      · change 0 ≤ ((1 - (b : ℝ) - (r : ℝ) - s : ℝ) : ℂ)
        rw [hswapR]
        exact Complex.zero_le_real.mpr hlR.le

/-- For distinct positive diagonal vacuum weights, the rational coupling and
the common residual determinant contribute two separate norm equations. -/
theorem rational_rank_le_two_diagonal_iff (b l r : ℚ)
    (hb : 0 < b) (hl : 0 < l) (hr : 0 < r) (hne : l ≠ r) :
    (∃ z : ℂ, ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧
      MatchesCoherentData b (diagonalEdgeBlock b l) (diagonalEdgeBlock b r) 0 0 0 z ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j)) ↔
    (∃ z : ℂ, RationalEntry z ∧ normSq z = (b * (1 - b - l - r) : ℚ)) ∧
    (∃ w : ℂ, RationalEntry w ∧ normSq w = (l * r : ℚ)) := by
  constructor
  · rintro ⟨z, ρ, hp, hm, hk, hq⟩
    have qz : RationalEntry z := hm.2.2.2 ▸ hq (.inl 0) (.inr true)
    obtain ⟨hz, hw⟩ := (rational_rank_two_fixed b l r z hb hl hr hne qz).mp ⟨ρ, hp, hm, hk, hq⟩
    exact ⟨⟨z, qz, hz⟩, hw⟩
  · rintro ⟨⟨z, qz, hz⟩, hw⟩
    exact ⟨z, (rational_rank_two_fixed b l r z hb hl hr hne qz).mpr ⟨hz, hw⟩⟩

end D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank
