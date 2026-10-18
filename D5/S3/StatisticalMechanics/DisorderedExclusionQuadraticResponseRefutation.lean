/- GID: D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim; result=D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result; claim=D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim
   digest: Four disordered exclusion sites refute the nonzero quadratic-current conjecture. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Field

set_option linter.style.longLine false

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.DisorderedExclusionQuadraticResponseRefutation
open scoped BigOperators Topology Asymptotics

noncomputable def p {L : ℕ} (wp : Fin L → ℝ) (ε : ℝ) (i : Fin L) : ℝ :=
  (1 + ε) / 2 * wp i

noncomputable def q {L : ℕ} (wm : Fin L → ℝ) (ε : ℝ) (i : Fin L) : ℝ :=
  (1 - ε) / 2 * wm i

noncomputable def rate {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) (ε : ℝ)
    (s t : Finset (Fin L)) : ℝ :=
  ∑ i ∈ s, ((if i + 1 ∉ s ∧ t = insert (i + 1) (s.erase i) then p wp ε i else 0) +
    (if i - 1 ∉ s ∧ t = insert (i - 1) (s.erase i) then q wm ε i else 0))

def IsStationary {L : ℕ} [NeZero L] (N : ℕ) (wp wm : Fin L → ℝ) (ε : ℝ)
    (μ : Finset (Fin L) → ℝ) : Prop :=
  (∀ s, s.card ≠ N → μ s = 0) ∧ (∀ s, 0 ≤ μ s) ∧ (∑ s, μ s) = 1 ∧
    ∀ t, (∑ s, μ s * rate wp wm ε s t) = μ t * ∑ s, rate wp wm ε t s

noncomputable def current {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) (ε : ℝ)
    (μ : Finset (Fin L) → ℝ) : ℝ :=
  ∑ s, μ s * ((if 0 ∈ s ∧ 1 ∉ s then p wp ε 0 else 0) -
    (if 1 ∈ s ∧ 0 ∉ s then q wm ε 1 else 0))

def BondRatioUniform {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) : Prop :=
  ∀ ε : ℝ, -1 < ε → ε < 1 → ∀ i j : Fin L,
    p wp ε i / q wm ε (i + 1) = p wp ε j / q wm ε (j + 1)

def InversionCorrespondence {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) : Prop :=
  ∃ k : Fin L, ∀ i : Fin L,
    (∀ ε : ℝ, p wp ε (k + i) = q wm (-ε) (k - i)) ∨
    (∀ ε : ℝ, p wp ε (k + i) = q wm (-ε) (k - i + 1))

def claim : Prop :=
  ∀ (L N : ℕ) [NeZero L], 2 ≤ N → N + 2 ≤ L →
    ∀ wp wm : Fin L → ℝ, (∀ i, 0 < wp i ∧ 0 < wm i) →
    (∏ i, wm i) = (∏ i, wp i) → ¬ BondRatioUniform wp wm →
    ¬ InversionCorrespondence wp wm → ∀ δ : ℝ, 0 < δ →
    ∀ π : ℝ → Finset (Fin L) → ℝ,
    (∀ ε, |ε| < δ → IsStationary N wp wm ε (π ε) ∧
      ∀ μ, IsStationary N wp wm ε μ → μ = π ε) →
    ∀ c₁ c₂ : ℝ,
      (fun ε => current wp wm ε (π ε) - c₁ * ε - c₂ * ε ^ 2)
        =o[𝓝 0] (fun ε => ε ^ 2) → c₂ ≠ 0

private noncomputable def a : Fin 4 → ℝ := ![2, 4, 3, 41]

private def states : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

private noncomputable def D (ε : ℝ) : ℝ :=
  223175 + 17022*ε^2 - 1628*ε^3 - 114725*ε^4 + 1628*ε^5

private noncomputable def B (ε : ℝ) : Fin 6 → ℝ :=
  ![123*(2825-1612*ε+390*ε^2+1256*ε^3-1695*ε^4+148*ε^5),
    164*(2825+518*ε-928*ε^2-370*ε^3-1033*ε^4-148*ε^5),
    12*(2825+5608*ε+4830*ε^2+3036*ε^3+1265*ε^4+148*ε^5),
    82*(2825+1008*ε+1150*ε^2-1564*ε^3-2415*ε^4+148*ε^5),
    6*(2825-222*ε+2672*ε^2+370*ε^3-2873*ε^4-148*ε^5),
    8*(2825-4412*ε+2630*ε^2-1544*ε^3+545*ε^4+148*ε^5)]

private noncomputable def law (ε : ℝ) (s : Finset (Fin 4)) : ℝ :=
  ∑ j : Fin 6, if s = states j then B ε j / (5 * D ε) else 0

private theorem sum_configs (f : Finset (Fin 4) → ℝ) :
    (∑ s, f s) = f {} + f {0} + f {1} + f {2} + f {3} +
      f {0,1} + f {0,2} + f {0,3} + f {1,2} + f {1,3} + f {2,3} +
      f {0,1,2} + f {0,1,3} + f {0,2,3} + f {1,2,3} + f {0,1,2,3} := by
  have hu : (Finset.univ : Finset (Finset (Fin 4))) =
      {{}, {0}, {1}, {2}, {3}, {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3},
        {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {0,1,2,3}} := by decide
  rw [hu]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

private theorem no_uniform : ¬ BondRatioUniform a a := by
  intro h
  have hh := h 0 (by norm_num) (by norm_num) 0 1
  norm_num [p.eq_1, q.eq_1, a.eq_1, Fin.add_def, Fin.sub_def, Fin.neg_def] at hh

private theorem no_inversion : ¬ InversionCorrespondence a a := by
  rintro ⟨k, hk⟩
  have hh : ∀ i : Fin 4,
      p a 0 (k+i) = q a 0 (k-i) ∨ p a 0 (k+i) = q a 0 (k-i+1) := by
    intro i
    exact (hk i).imp (fun h => by simpa using h 0) (fun h => by simpa using h 0)
  fin_cases k <;> norm_num [p.eq_1, q.eq_1, a.eq_1, Fin.forall_fin_succ, Fin.add_def, Fin.sub_def, Fin.neg_def] at hh

private theorem sum_support (μ f : Finset (Fin 4) → ℝ)
    (h : ∀ s, s.card ≠ 2 → μ s = 0) :
    (∑ s, μ s * f s) = ∑ j : Fin 6, μ (states j) * f (states j) := by
  rw [sum_configs]
  simp only [h {} (by decide), h {0} (by decide), h {1} (by decide),
    h {2} (by decide), h {3} (by decide), h {0,1,2} (by decide),
    h {0,1,3} (by decide), h {0,2,3} (by decide), h {1,2,3} (by decide),
    h {0,1,2,3} (by decide), zero_mul, zero_add, add_zero]
  norm_num [Fin.sum_univ_succ, states.eq_1]
  ring

private theorem sum_law (ε : ℝ) (f : Finset (Fin 4) → ℝ) :
    (∑ s, law ε s * f s) = ∑ j : Fin 6, B ε j / (5 * D ε) * f (states j) := by
  simp only [law.eq_1, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

private theorem law_apply (ε : ℝ) (j : Fin 6) :
    law ε (states j) = B ε j / (5 * D ε) := by
  fin_cases j <;> simp only [law.eq_1, states.eq_1, Fin.sum_univ_succ] <;>
    dsimp! only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] <;> norm_num +decide

private theorem law_support (ε : ℝ) (s : Finset (Fin 4)) (hs : s.card ≠ 2) :
    law ε s = 0 := by
  rw [law.eq_1]
  apply Finset.sum_eq_zero
  intro j hj
  apply if_neg
  intro he
  subst s
  fin_cases j <;> exact hs (by decide)

private theorem rate_card {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) (ε : ℝ)
    (s t : Finset (Fin L)) (h : s.card ≠ t.card) : rate wp wm ε s t = 0 := by
  rw [rate.eq_1]
  apply Finset.sum_eq_zero
  intro i hi
  have hz (j : Fin L) : ¬ (j ∉ s ∧ t = insert j (s.erase i)) := by
    rintro ⟨hj, rfl⟩
    apply h
    rw [Finset.card_insert_of_notMem (by simp [hj])]
    exact (Finset.card_erase_add_one hi).symm
  simp only [if_neg (hz _), add_zero]

private noncomputable def F (ε : ℝ) (v : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(-2*ε-6)*v 0 + (3-3*ε)*v 1 + (41*ε+41)*v 4,
    (4*ε+4)*v 0 - 10*v 1 + (41-41*ε)*v 2 + (4-4*ε)*v 3 + (41*ε+41)*v 5,
    (3*ε+3)*v 1 + (39*ε-43)*v 2 + (4-4*ε)*v 4,
    (2*ε+2)*v 1 + (ε-7)*v 3 + (41-41*ε)*v 4,
    (2-2*ε)*v 0 + (2*ε+2)*v 2 + (3*ε+3)*v 3 - 90*v 4 + (3-3*ε)*v 5,
    (2-2*ε)*v 1 + (4*ε+4)*v 4 + (-38*ε-44)*v 5]

set_option maxHeartbeats 1200000 in
-- Expanding six balance equations over the explicit finite configuration sums needs this budget.
private theorem balance_block (ε : ℝ) (μ : Finset (Fin 4) → ℝ)
    (h : ∀ s, s.card ≠ 2 → μ s = 0) (j : Fin 6) :
    F ε (fun k => μ (states k)) j =
      2 * ((∑ s, μ s * rate a a ε s (states j)) -
        μ (states j) * ∑ s, rate a a ε (states j) s) := by
  rw [sum_support μ _ h, sum_configs]
  fin_cases j <;> simp only [F.eq_1, states.eq_1, Fin.sum_univ_succ] <;>
    dsimp! only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat] <;>
    norm_num +decide [Matrix.cons_val, rate.eq_1, p.eq_1, q.eq_1, a.eq_1,
      Fin.add_def, Fin.sub_def, Fin.neg_def] <;> ring

private theorem polynomial_balance (ε : ℝ) (j : Fin 6) : F ε (B ε) j = 0 := by
  fin_cases j <;>
    simp only [F.eq_1, B.eq_1, Matrix.cons_val, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

private theorem sum_B (ε : ℝ) : (∑ j : Fin 6, B ε j) = 5 * D ε := by
  norm_num [B.eq_1, D.eq_1, Fin.sum_univ_succ]
  ring

private theorem positive_polynomials (ε : ℝ) (he : |ε| < (1 / 100 : ℝ)) :
    0 < D ε ∧ ∀ j, 0 < B ε j := by
  have hp (n : ℕ) (hn : n ≠ 0) : -(1 / 100 : ℝ) < ε^n ∧ ε^n < (1 / 100 : ℝ) := by
    apply abs_lt.mp
    rw [abs_pow]
    exact lt_of_le_of_lt
      (pow_le_of_le_one (abs_nonneg ε) (by linarith) hn) he
  have h1 := abs_lt.mp he
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  constructor
  · rw [D.eq_1]
    linarith
  · intro j
    fin_cases j <;> norm_num [B.eq_1, Matrix.cons_val] <;> linarith

private theorem card_two_cases (s : Finset (Fin 4)) (hs : s.card = 2) :
    ∃ j : Fin 6, s = states j := by
  have hm : s ∈ ({ {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3} } :
      Finset (Finset (Fin 4))) := by
    have hu : (Finset.univ.filter (fun t : Finset (Fin 4) => t.card = 2)) =
        {{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} := by decide
    rw [← hu]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h⟩

private theorem stationary_law (ε : ℝ) (he : |ε| < (1 / 100 : ℝ)) :
    IsStationary 2 a a ε (law ε) := by
  obtain ⟨hD, hB⟩ := positive_polynomials ε he
  refine ⟨law_support ε, ?_, ?_, ?_⟩
  · intro s
    rw [law.eq_1]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact div_nonneg (hB j).le (mul_pos (by norm_num) hD).le
    · exact le_rfl
  · have hh := sum_law ε (fun _ => 1)
    simp only [mul_one] at hh
    rw [hh, ← Finset.sum_div, sum_B]
    exact div_self (mul_ne_zero (by norm_num) hD.ne')
  · intro t
    by_cases ht : t.card = 2
    · obtain ⟨j, rfl⟩ := card_two_cases t ht
      have hb := balance_block ε (law ε) (law_support ε) j
      simp only [law_apply] at hb
      have hz : F ε (fun k => B ε k / (5 * D ε)) j = 0 := by
        have hf : F ε (fun k => B ε k / (5 * D ε)) j = F ε (B ε) j / (5 * D ε) := by
          fin_cases j <;>
            simp only [F.eq_1, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
        rw [hf, polynomial_balance, zero_div]
      rw [hz] at hb
      rw [law_apply]
      linarith
    · rw [law_support ε t ht, zero_mul]
      apply Finset.sum_eq_zero
      intro s hs
      by_cases hc : s.card = 2
      · rw [rate_card a a ε s t (by omega), mul_zero]
      · rw [law_support ε s hc, zero_mul]

set_option maxHeartbeats 1200000 in
-- Six adjugate certificates normalize polynomials in the bias and six masses.
private theorem unique_vector (ε : ℝ) (v : Fin 6 → ℝ) (hD : D ε ≠ 0)
    (h : ∀ j, F ε v j = 0) (hn : (∑ j, v j) = 1) (j : Fin 6) :
    v j = B ε j / (5 * D ε) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hD)).mpr
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [F.eq_1, Matrix.cons_val] at h0 h1 h2 h3 h4
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hn
  change v 0 + (v 1 + (v 2 + (v 3 + (v 4 + v 5)))) = 1 at hn
  fin_cases j
  · change v 0 * (5 * D ε) = B ε 0
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      ((31031*ε^4 + 78236*ε^3 + 67058*ε^2 + 676*ε - 297433)/2) * h0 +
      (-3*(4729*ε^4 - 52272*ε^3 + 86862*ε^2 - 48152*ε + 15393)/10) * h1 +
      (-41*(311*ε^4 - 4110*ε^3 + 8812*ε^2 - 1610*ε - 299)/10) * h2 +
      (3*(53613*ε^4 + 310350*ε^3 - 238024*ε^2 - 294550*ε + 81363)/10) * h3 +
      (-41*(3249*ε^4 - 27344*ε^3 - 5314*ε^2 + 29496*ε + 12857)/10) * h4 +
      (123*(148*ε^5 - 1695*ε^4 + 1256*ε^3 + 390*ε^2 - 1612*ε + 2825)) * hn
  · change v 1 * (5 * D ε) = B ε 1
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      (-(57233*ε^4 - 76334*ε^3 + 106816*ε^2 + 72158*ε - 191841)/2) * h0 +
      ((21061*ε^4 - 4392*ε^3 - 56642*ε^2 + 203160*ε - 180467)/10) * h1 +
      (41*(433*ε^4 + 788*ε^3 + 1530*ε^2 + 10348*ε - 523)/10) * h2 +
      (-(293817*ε^4 + 695282*ε^3 + 580160*ε^2 - 1012898*ε - 953897)/10) * h3 +
      (41*(5047*ε^4 - 3170*ε^3 - 28448*ε^2 + 8018*ε + 22489)/10) * h4 +
      (-164*(148*ε^5 + 1033*ε^4 + 370*ε^3 + 928*ε^2 - 518*ε - 2825)) * hn
  · change v 2 * (5 * D ε) = B ε 2
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      ((4169*ε^4 + 2584*ε^3 + 6842*ε^2 + 21264*ε + 13093)/2) * h0 +
      (-3*(511*ε^4 + 922*ε^3 - 572*ε^2 + 3782*ε + 3997)/10) * h1 +
      ((791*ε^4 - 149440*ε^3 - 174598*ε^2 - 211040*ε - 260689)/10) * h2 +
      (3*(7067*ε^4 + 35440*ε^3 + 71894*ε^2 + 63240*ε + 21127)/10) * h3 +
      (-(15031*ε^4 + 23184*ε^3 - 83906*ε^2 - 145496*ε - 50877)/10) * h4 +
      (12*(148*ε^5 + 1265*ε^4 + 3036*ε^3 + 4830*ε^2 + 5608*ε + 2825)) * hn
  · change v 3 * (5 * D ε) = B ε 3
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      ((21109*ε^4 - 107616*ε^3 - 33478*ε^2 + 104824*ε + 36473)/2) * h0 +
      (-(7313*ε^4 + 1996*ε^3 - 136386*ε^2 + 124796*ε + 13801)/10) * h1 +
      (-41*(189*ε^4 - 2300*ε^3 - 7242*ε^2 + 1300*ε - 331)/10) * h2 +
      ((109261*ε^4 - 250940*ε^3 + 851402*ε^2 + 30860*ε - 1521159)/10) * h3 +
      (-41*(1451*ε^4 + 20654*ε^3 - 13716*ε^2 - 25246*ε + 14233)/10) * h4 +
      (82*(148*ε^5 - 2415*ε^4 - 1564*ε^3 + 1150*ε^2 + 1008*ε + 2825)) * hn
  · change v 4 * (5 * D ε) = B ε 4
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      (-(2277*ε^4 + 7574*ε^3 - 8496*ε^2 - 8038*ε + 3131)/2) * h0 +
      (3*(283*ε^4 + 954*ε^3 + 1184*ε^2 - 5210*ε + 2149)/10) * h1 +
      ((677*ε^4 + 6742*ε^3 + 2520*ε^2 - 25718*ε + 3363)/10) * h2 +
      (-3*(4551*ε^4 - 17744*ε^3 - 18870*ε^2 + 29216*ε + 11359)/10) * h3 +
      ((8643*ε^4 + 1900*ε^3 + 96958*ε^2 - 14668*ε - 144609)/10) * h4 +
      (-6*(148*ε^5 + 2873*ε^4 - 370*ε^3 - 2672*ε^2 + 222*ε - 2825)) * hn
  · change v 5 * (5 * D ε) = B ε 5
    simp only [B.eq_1, D.eq_1, Matrix.cons_val]
    linear_combination
      ((3201*ε^4 - 41964*ε^3 + 57898*ε^2 - 62644*ε + 59157)/2) * h0 +
      ((1123*ε^4 - 150524*ε^3 + 175574*ε^2 - 195844*ε + 245991)/10) * h1 +
      ((1279*ε^4 - 152420*ε^3 + 173718*ε^2 - 200220*ε + 252939)/10) * h2 +
      ((16169*ε^4 - 144380*ε^3 + 170538*ε^2 - 262180*ε + 293869)/10) * h3 +
      (-(7839*ε^4 + 123036*ε^3 - 205274*ε^2 + 285316*ε - 282373)/10) * h4 +
      (8*(148*ε^5 + 545*ε^4 - 1544*ε^3 + 2630*ε^2 - 4412*ε + 2825)) * hn

private theorem unique_law (ε : ℝ) (he : |ε| < (1 / 100 : ℝ))
    (μ : Finset (Fin 4) → ℝ) (hμ : IsStationary 2 a a ε μ) : μ = law ε := by
  have hvec (j : Fin 6) : F ε (fun k => μ (states k)) j = 0 := by
    rw [balance_block ε μ hμ.1, hμ.2.2.2, sub_self, mul_zero]
  have hnorm : (∑ j : Fin 6, μ (states j)) = 1 := by
    have hm := sum_support μ (fun _ => 1) hμ.1
    simp only [mul_one] at hm
    rw [← hm]
    exact hμ.2.2.1
  funext s
  by_cases hs : s.card = 2
  · obtain ⟨j, rfl⟩ := card_two_cases s hs
    rw [law_apply]
    exact unique_vector ε _ (positive_polynomials ε he).1.ne' hvec hnorm j
  · rw [hμ.1 s hs, law_support ε s hs]

private theorem current_closed (ε : ℝ) (hD : D ε ≠ 0) :
    current a a ε (law ε) = 7872 * ε * (25 + 9*ε^2 - 16*ε^4) / D ε := by
  rw [current.eq_1, sum_law]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, states.eq_1, B.eq_1,
    p.eq_1, q.eq_1, a.eq_1, Matrix.cons_val, Matrix.cons_val_succ]
  norm_num +decide
  field_simp (disch := first | assumption | norm_num)
  ring

private noncomputable def remainder_factor (ε : ℝ) : ℝ :=
  -7872 * (1628*ε^3 + 28107*ε^2 - 1628*ε - 63321) / (8927 * D ε)

private theorem quadratic_expansion :
    (fun ε => current a a ε (law ε) - (7872/8927 : ℝ) * ε - 0 * ε^2)
      =o[𝓝 0] (fun ε => ε^2) := by
  have hg : ContinuousAt remainder_factor 0 := by
    unfold remainder_factor
    apply ContinuousAt.div
    · fun_prop
    · unfold D
      fun_prop
    · norm_num [D.eq_1]
  have ho : (fun ε : ℝ => ε^3 * remainder_factor ε) =o[𝓝 0] (fun ε => ε^2) := by
    simpa only [mul_one] using
      (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by decide : 2 < 3)).mul_isBigO
        (hg.isBigO (F := ℝ))
  apply ho.congr' ?_ Filter.EventuallyEq.rfl
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < (1 / 100 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 / 100 : ℝ))]
      with ε hε
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  filter_upwards [hnear] with ε he
  have hD : D ε ≠ 0 := (positive_polynomials ε he).1.ne'
  rw [current_closed ε hD, remainder_factor.eq_1]
  field_simp (disch := first | assumption | norm_num)
  simp only [D.eq_1]
  ring

/-- The interacting four-site trap law has zero quadratic response without either rate symmetry. -/
theorem result : ¬ claim := by
  intro h
  have hc := h 4 2 (by norm_num) (by norm_num) a a
    (by intro i; fin_cases i <;> norm_num [a.eq_1]) rfl no_uniform no_inversion
    (1/100) (by norm_num) law
    (fun ε he => ⟨stationary_law ε he, fun μ hμ => unique_law ε he μ hμ⟩)
    (7872/8927) 0 quadratic_expansion
  exact hc rfl

end D5.S3.StatisticalMechanics.DisorderedExclusionQuadraticResponseRefutation
