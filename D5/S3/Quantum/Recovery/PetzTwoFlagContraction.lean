/- GID: D5/S3/Quantum/Recovery/PetzTwoFlagContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzTwoFlagContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complex two-flag contraction bound with radial and phase deficiency. -/

module

public import Mathlib.Analysis.Complex.Order
import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The two within-flag coherences determine the sharp bound for the weighted contraction objective.
-/

public section

set_option autoImplicit false

namespace D5.S3.Quantum.Recovery.PetzTwoFlagContraction

/-- The radial and phase terms give the full deficiency from the two real corners.
The two radial margins are nonnegative and their sum is positive. -/
theorem twoFlag_maximum (m C f g w v : ℝ) (y z : ℂ)
    (hm : 0 ≤ m) (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (hw : 0 ≤ 8 * m + f * (f + g) / C - w)
    (hv : 0 ≤ 8 * m + g * (f + g) / C - v)
    (hmargin : 0 < (8 * m + f * (f + g) / C - w) + (8 * m + g * (f + g) / C - v))
    (hy : Complex.normSq y ≤ 1) (hz : Complex.normSq z ≤ 1) :
    let objective := w * (1 - Complex.normSq y) + v * (1 - Complex.normSq z) +
      4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C
    let optimum := 16 * m + (f + g) ^ 2 / C
    objective ≤ optimum ∧
      optimum - objective =
        (8 * m + f * (f + g) / C - w) * (1 - Complex.normSq y) +
        (8 * m + g * (f + g) / C - v) * (1 - Complex.normSq z) +
        4 * m * Complex.normSq (y + z) +
        f * (f + g) / C * y.im ^ 2 + g * (f + g) / C * z.im ^ 2 +
        f * g / C * (y.re + z.re) ^ 2 ∧
      (objective = optimum ↔ (y = 1 ∧ z = -1) ∨ (y = -1 ∧ z = 1)) := by
  dsimp only
  have hgap :
      16 * m + (f + g) ^ 2 / C -
        (w * (1 - Complex.normSq y) + v * (1 - Complex.normSq z) +
          4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C) =
        (8 * m + f * (f + g) / C - w) * (1 - Complex.normSq y) +
        (8 * m + g * (f + g) / C - v) * (1 - Complex.normSq z) +
        4 * m * Complex.normSq (y + z) +
        f * (f + g) / C * y.im ^ 2 + g * (f + g) / C * z.im ^ 2 +
        f * g / C * (y.re + z.re) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hySlack := sub_nonneg.mpr hy
  have hzSlack := sub_nonneg.mpr hz
  have hcoherence := mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hm)
    (Complex.normSq_nonneg (y + z))
  have hyCoeff := div_pos (mul_pos hf (add_pos hf hg)) hC
  have hzCoeff := div_pos (mul_pos hg (add_pos hf hg)) hC
  have hphaseCoeff := div_pos (mul_pos hf hg) hC
  have hyPhase := mul_nonneg hyCoeff.le (sq_nonneg y.im)
  have hzPhase := mul_nonneg hzCoeff.le (sq_nonneg z.im)
  have hphase := mul_nonneg hphaseCoeff.le (sq_nonneg (y.re + z.re))
  have hyTerm := mul_nonneg hw hySlack
  have hzTerm := mul_nonneg hv hzSlack
  refine ⟨by linarith only [hgap, hyTerm, hzTerm, hcoherence, hyPhase, hzPhase, hphase],
    hgap, ?_⟩
  constructor
  · intro h
    have hsum := hgap
    rw [h, sub_self] at hsum
    have hyi : y.im = 0 := by
      have hs : y.im ^ 2 = 0 := (mul_eq_zero.mp (show f * (f + g) / C *
        y.im ^ 2 = 0 by
          linarith only [hsum, hyTerm, hzTerm, hcoherence, hyPhase, hzPhase, hphase])).resolve_left
            hyCoeff.ne'
      exact (mul_eq_zero.mp (by simpa only [pow_two] using hs)).elim id id
    have hzi : z.im = 0 := by
      have hs : z.im ^ 2 = 0 := (mul_eq_zero.mp (show g * (f + g) / C *
        z.im ^ 2 = 0 by
          linarith only [hsum, hyTerm, hzTerm, hcoherence, hyPhase, hzPhase, hphase])).resolve_left
            hzCoeff.ne'
      exact (mul_eq_zero.mp (by simpa only [pow_two] using hs)).elim id id
    have hreal : y.re + z.re = 0 := by
      have hs : (y.re + z.re) ^ 2 = 0 := (mul_eq_zero.mp (show f * g / C *
        (y.re + z.re) ^ 2 = 0 by
          linarith only [hsum, hyTerm, hzTerm, hcoherence, hyPhase, hzPhase, hphase])).resolve_left
            hphaseCoeff.ne'
      exact (mul_eq_zero.mp (by simpa only [pow_two] using hs)).elim id id
    have hneg : z.re = -y.re := by linarith only [hreal]
    have hnorm : Complex.normSq y = Complex.normSq z := by
      rw [Complex.normSq_apply, Complex.normSq_apply, hyi, hzi, hneg]
      ring
    have hradial :
        ((8 * m + f * (f + g) / C - w) + (8 * m + g * (f + g) / C - v)) *
          (1 - Complex.normSq y) = 0 := by
      rw [add_mul]
      rw [← hnorm] at hsum hzTerm
      linarith only [hsum, hyTerm, hzTerm, hcoherence, hyPhase, hzPhase, hphase]
    have hyr : Complex.normSq y = 1 :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hradial).resolve_left hmargin.ne')).symm
    have hySign : y.re = 1 ∨ y.re = -1 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      simpa only [Complex.normSq_apply, hyi, mul_zero, add_zero, pow_two, mul_one] using hyr
    rcases hySign with h₁ | h₂
    · exact Or.inl ⟨Complex.ext (by simpa using h₁) (by simpa using hyi),
        Complex.ext (by simp [hneg, h₁]) (by simpa using hzi)⟩
    · exact Or.inr ⟨Complex.ext (by simpa using h₂) (by simpa using hyi),
        Complex.ext (by simp [hneg, h₂]) (by simpa using hzi)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] <;> ring

open scoped BigOperators ComplexOrder

/-- For a Hermitian four-slot contraction the sum over the remaining entries
in each row is bounded by the slack of its within-flag coherence. -/
theorem matrix_twoFlag_maximum
    (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a : Fin 2 × Fin 2 → ℝ) (m C f g : ℝ)
    (hY : Y.IsHermitian) (hY₂ : (1 - Y * Y).PosSemidef)
    (ha : ∀ i, 0 ≤ a i) (hm : 0 ≤ m) (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (hw : 0 ≤ 8 * m + f * (f + g) / C - (a (0, 0) + a (1, 0)))
    (hv : 0 ≤ 8 * m + g * (f + g) / C - (a (0, 1) + a (1, 1)))
    (hmargin : 0 < (8 * m + f * (f + g) / C - (a (0, 0) + a (1, 0))) +
      (8 * m + g * (f + g) / C - (a (0, 1) + a (1, 1)))) :
    let partner (i : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (1 - i.1, i.2)
    let y := Y (0, 0) (1, 0)
    let z := Y (0, 1) (1, 1)
    let objective :=
      (∑ i, a i * ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j)) +
      4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C
    let optimum := 16 * m + (f + g) ^ 2 / C
    objective ≤ optimum ∧
      (objective = optimum ↔ (y = 1 ∧ z = -1) ∨ (y = -1 ∧ z = 1)) := by
  classical
  dsimp only
  simp only [add_assoc]
  let partner (i : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (1 - i.1, i.2)
  let entry (s : Fin 2) := Y (0, s) (1, s)
  let rest (i : Fin 2 × Fin 2) := ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j)
  let coherence := 4 * m * Complex.normSq (entry 0 - entry 1) +
    (f * (entry 0).re - g * (entry 1).re) ^ 2 / C
  let optimum := 16 * m + (f + g) ^ 2 / C
  change (∑ i, a i * rest i) + coherence ≤ optimum ∧
    ((∑ i, a i * rest i) + coherence = optimum ↔
      (entry 0 = 1 ∧ entry 1 = -1) ∨ (entry 0 = -1 ∧ entry 1 = 1))
  have hrest (i : Fin 2 × Fin 2) : 0 ≤ rest i :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hrow (i : Fin 2 × Fin 2) : rest i + Complex.normSq (entry i.2) ≤ 1 := by
    have hdiag := (Complex.nonneg_iff.mp (hY₂.diag_nonneg (i := i))).1
    have hsum : ((Y * Y) i i).re = ∑ j, Complex.normSq (Y i j) := by
      rw [Matrix.mul_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hY.apply j i]
      simp [Complex.star_def, Complex.mul_conj]
    have hpartner : Complex.normSq (Y i (partner i)) = Complex.normSq (entry i.2) := by
      obtain ⟨b, s⟩ := i
      fin_cases b
      · rfl
      · change Complex.normSq (Y (1, s) (0, s)) = _
        rw [← hY.apply (1, s) (0, s)]
        exact Complex.normSq_conj _
    rw [Matrix.sub_apply, Complex.sub_re, hsum,
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (partner i)), hpartner] at hdiag
    simpa [rest] using sub_nonneg.mp hdiag
  have hentry (s : Fin 2) : Complex.normSq (entry s) ≤ 1 :=
    le_trans (le_add_of_nonneg_left (hrest (0, s))) (hrow (0, s))
  have henvelope : (∑ i, a i * rest i) ≤
      (a (0, 0) + a (1, 0)) * (1 - Complex.normSq (entry 0)) +
      (a (0, 1) + a (1, 1)) * (1 - Complex.normSq (entry 1)) := by
    calc
      _ ≤ ∑ i, a i * (1 - Complex.normSq (entry i.2)) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mpr (hrow i)) (ha i)
      _ = _ := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
        ring
  obtain ⟨hbound, _, heq⟩ :=
    twoFlag_maximum m C f g (a (0, 0) + a (1, 0)) (a (0, 1) + a (1, 1))
      (entry 0) (entry 1) hm hC hf hg hw hv hmargin (hentry 0) (hentry 1)
  refine ⟨by dsimp [coherence, optimum]; linarith only [henvelope, hbound], ?_⟩
  constructor
  · intro h
    apply heq.mp
    dsimp [coherence, optimum] at h ⊢
    linarith only [henvelope, hbound, h]
  · intro h
    have habs (s : Fin 2) : Complex.normSq (entry s) = 1 := by
      fin_cases s
      · change Complex.normSq (entry 0) = 1
        rcases h with ⟨h₀, _⟩ | ⟨h₀, _⟩ <;>
          simp only [h₀, Complex.normSq_neg, Complex.normSq_one]
      · change Complex.normSq (entry 1) = 1
        rcases h with ⟨_, h₁⟩ | ⟨_, h₁⟩ <;>
          simp only [h₁, Complex.normSq_neg, Complex.normSq_one]
    have hzero (i : Fin 2 × Fin 2) : rest i = 0 := by
      have hi := hrow i
      rw [habs] at hi
      linarith [hrest i]
    simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add]
    have hcorner := heq.mpr h
    simpa [coherence, optimum, habs, sub_self, add_assoc] using hcorner

end D5.S3.Quantum.Recovery.PetzTwoFlagContraction
