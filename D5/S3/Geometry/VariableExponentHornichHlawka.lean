/- GID: D5/S3/Geometry/VariableExponentHornichHlawka
   generality: I
   mirror-B: D5/B/S3/Geometry/VariableExponentHornichHlawka
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/VariableExponentHornichHlawka.claim; result=D5/S3/Geometry/VariableExponentHornichHlawka.result; claim=D5/S3/Geometry/VariableExponentHornichHlawka.claim
   digest: A two-valued variable exponent gives a Luxemburg norm violating Hornich–Hlawka. -/

/- Source: Marinescu–Niculescu, "A survey of the Hornich-Hlawka inequality",
   arXiv:2407.03278, §3, Problem 3. The Luxemburg norm follows
   Diening–Harjulehto–Hästö–Růžička.
   admission_basis: open-problem-resolution (#15667; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Reuse: Measurable.ite, lintegral_union, setLIntegral_congr_fun,
     setLIntegral_const, Real.volume_Ioo, Real.volume_Ico,
     Real.rpow_one, Real.rpow_two, ENNReal.ofReal_mul, ENNReal.ofReal_add,
     ENNReal.ofReal_le_one, Real.sq_sqrt, Real.sqrt_le_iff,
     Real.sqrt_eq_iff_eq_sq, Real.sqrt_lt', IsLeast.csInf_eq.
   Definitions:
     modular: proof_shape definition; consumers=luxNorm, InLp, modular_J, scale_iff
     luxNorm: proof_shape definition; consumers=claim, luxNorm_J, pair_norms, result
     InLp: proof_shape definition; consumers=claim, J_InLp
     claim: proof_shape definition; consumer=result
     exponent: proof_shape definition; consumers=exponent_measurable,
       exponent_range, modular_J, luxNorm_J, J_InLp, pair_norms, result
     J: proof_shape definition; consumers=J_measurable, J_add, modular_J,
       scale_iff, luxNorm_J, J_InLp, pair_norms, result
     N: proof_shape definition; consumers=scale_iff, luxNorm_J, J_InLp,
       N_special, pair_norms, result
   Per-declaration proof_shape and live consumers:
     exponent_measurable: bind-only; consumer=result
     exponent_range: bind-only; consumer=result
     J_measurable: bind-only; consumer=J_InLp
     J_add: bind-only; consumer=result
     modular_J: bind-only; consumer=scale_iff
     scale_iff: bind-only; consumers=luxNorm_J, J_InLp
     luxNorm_J: bind-only; consumers=pair_norms, result
     J_InLp: bind-only; consumer=result
     N_special: bind-only; consumer=result
     base_positive: bind-only; consumer=result
     pair_norms: bind-only; consumer=result
     result: bind-only; designated refutation conclusion
   Interval integration, square-root comparisons, and algebraic normalization
   suffice after applying the pinned Mathlib results. Admission uses the
   external open-problem resolution exception, not an escape witness.
   The exponent is one on the first half and two on the second half.
   Three step functions give pair-sum norms 1, 2, 2 and four remaining
   norms (1 + √2)/2. Thus 5 > 2 + 2√2 refutes the proposed inequality. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace D5.S3.Geometry.VariableExponentHornichHlawka
open MeasureTheory

/-- The variable-exponent modular of `f` at scale `λ` on `(0, 1)`. -/
noncomputable def modular (p f : ℝ → ℝ) (lam : ℝ) : ENNReal :=
  ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (|f t / lam| ^ p t)

/-- The Luxemburg norm of `f` in `L^{p(·)}(0, 1)`. -/
noncomputable def luxNorm (p f : ℝ → ℝ) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧ modular p f lam ≤ 1}

/-- `f` belongs to `L^{p(·)}(0, 1)`: measurable with finite modular at some scale. -/
def InLp (p f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ lam : ℝ, 0 < lam ∧ modular p f lam ≤ 1

def claim : Prop :=
  ∀ p : ℝ → ℝ, Measurable p → (∀ t ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ p t ∧ p t ≤ 2) →
    ∀ f g h : ℝ → ℝ, InLp p f → InLp p g → InLp p h →
      luxNorm p (f + g) + luxNorm p (g + h) + luxNorm p (h + f) ≤
        luxNorm p f + luxNorm p g + luxNorm p h + luxNorm p (f + g + h)

private def exponent (t : ℝ) : ℝ := if t < 1 / 2 then 1 else 2

private def J (a b c : ℝ) (t : ℝ) : ℝ :=
  if t ∈ Set.Ioo (0 : ℝ) (1 / 4) then 4 * a
  else if t ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) then 4 * b
  else if t ∈ Set.Ico (1 / 2 : ℝ) 1 then Real.sqrt 2 * c else 0

private lemma exponent_measurable : Measurable exponent :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

private lemma exponent_range (t : ℝ) : 1 ≤ exponent t ∧ exponent t ≤ 2 := by
  unfold exponent
  split_ifs <;> norm_num

private lemma J_measurable (a b c : ℝ) : Measurable (J a b c) :=
  Measurable.ite measurableSet_Ioo measurable_const
    (Measurable.ite measurableSet_Ico measurable_const
      (Measurable.ite measurableSet_Ico measurable_const measurable_const))

private lemma J_add (a b c d e f : ℝ) :
    J a b c + J d e f = J (a + d) (b + e) (c + f) := by
  funext t
  simp only [Pi.add_apply, J]
  split_ifs <;> ring

private lemma modular_J (a b c lam : ℝ) (hlam : 0 < lam) :
    modular exponent (J a b c) lam =
      ENNReal.ofReal ((|a| + |b|) / lam + c ^ 2 / lam ^ 2) := by
  have hdis₁ : Disjoint (Set.Ioo (0 : ℝ) (1 / 4)) (Set.Ico (1 / 4 : ℝ) (1 / 2)) := by
    rw [Set.disjoint_left]
    intro t ht hu
    exact (not_lt_of_ge hu.1) ht.2
  have hdis₂ : Disjoint
      (Set.Ioo (0 : ℝ) (1 / 4) ∪ Set.Ico (1 / 4 : ℝ) (1 / 2))
      (Set.Ico (1 / 2 : ℝ) 1) := by
    rw [Set.disjoint_left]
    intro t ht hu
    rcases ht with ht | ht <;> rcases ht with ⟨h₁, h₂⟩ <;> rcases hu with ⟨h₃, h₄⟩ <;> linarith
  have hsplit : Set.Ioo (0 : ℝ) 1 =
      (Set.Ioo (0 : ℝ) (1 / 4) ∪ Set.Ico (1 / 4 : ℝ) (1 / 2)) ∪
        Set.Ico (1 / 2 : ℝ) 1 := by
    ext t
    simp only [Set.mem_Ioo, Set.mem_Ico, Set.mem_union]
    constructor
    · rintro ⟨h₀, h₁⟩
      by_cases hq : t < 1 / 4
      · exact Or.inl (Or.inl ⟨h₀, hq⟩)
      · by_cases hh : t < 1 / 2
        · exact Or.inl (Or.inr ⟨le_of_not_gt hq, hh⟩)
        · exact Or.inr ⟨le_of_not_gt hh, h₁⟩
    · rintro ((⟨h₀, hq⟩ | ⟨hq, hh⟩) | ⟨hh, h₁⟩) <;> constructor <;> linarith
  have h₁ : (∫⁻ t in Set.Ioo (0 : ℝ) (1 / 4),
      ENNReal.ofReal (|J a b c t / lam| ^ exponent t)) =
      ENNReal.ofReal (|a| / lam) := by
    calc
      _ = ∫⁻ _ in Set.Ioo (0 : ℝ) (1 / 4), ENNReal.ofReal |4 * a / lam| := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hh : t < 1 / 2 := by linarith [ht.2]
        simp only [J, if_pos ht, exponent, if_pos hh, Real.rpow_one]
      _ = ENNReal.ofReal (|a| / lam) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 1
        rw [abs_div, abs_of_pos hlam, abs_mul]
        norm_num
        ring
  have h₂ : (∫⁻ t in Set.Ico (1 / 4 : ℝ) (1 / 2),
      ENNReal.ofReal (|J a b c t / lam| ^ exponent t)) =
      ENNReal.ofReal (|b| / lam) := by
    calc
      _ = ∫⁻ _ in Set.Ico (1 / 4 : ℝ) (1 / 2), ENNReal.ofReal |4 * b / lam| := by
        apply setLIntegral_congr_fun measurableSet_Ico
        intro t ht
        have hq : t ∉ Set.Ioo (0 : ℝ) (1 / 4) := fun h => (not_lt_of_ge ht.1) h.2
        simp only [J, if_neg hq, if_pos ht, exponent, if_pos ht.2, Real.rpow_one]
      _ = ENNReal.ofReal (|b| / lam) := by
        rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 1
        rw [abs_div, abs_of_pos hlam, abs_mul]
        norm_num
        ring
  have h₃ : (∫⁻ t in Set.Ico (1 / 2 : ℝ) 1,
      ENNReal.ofReal (|J a b c t / lam| ^ exponent t)) =
      ENNReal.ofReal (c ^ 2 / lam ^ 2) := by
    calc
      _ = ∫⁻ _ in Set.Ico (1 / 2 : ℝ) 1,
          ENNReal.ofReal ((Real.sqrt 2 * c / lam) ^ 2) := by
        apply setLIntegral_congr_fun measurableSet_Ico
        intro t ht
        have hq : t ∉ Set.Ioo (0 : ℝ) (1 / 4) := by
          intro h
          linarith [h.2, ht.1]
        have hh : t ∉ Set.Ico (1 / 4 : ℝ) (1 / 2) := fun h => (not_lt_of_ge ht.1) h.2
        have hh' : ¬ t < 1 / 2 := not_lt_of_ge ht.1
        simp only [J, if_neg hq, if_neg hh, if_pos ht, exponent, if_neg hh',
          Real.rpow_two, sq_abs]
      _ = ENNReal.ofReal (c ^ 2 / lam ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  rw [modular, hsplit, lintegral_union measurableSet_Ico hdis₂,
    lintegral_union measurableSet_Ico hdis₁, h₁, h₂, h₃,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

private def N (a b c : ℝ) : ℝ :=
  (|a| + |b| + Real.sqrt ((|a| + |b|) ^ 2 + 4 * c ^ 2)) / 2

private lemma scale_iff (a b c lam : ℝ) (hlam : 0 < lam) :
    modular exponent (J a b c) lam ≤ 1 ↔ N a b c ≤ lam := by
  rw [modular_J a b c lam hlam, ENNReal.ofReal_le_one]
  let A := |a| + |b|
  have hfrac : A / lam + c ^ 2 / lam ^ 2 = (A * lam + c ^ 2) / lam ^ 2 := by
    field_simp
  change A / lam + c ^ 2 / lam ^ 2 ≤ 1 ↔ _
  rw [hfrac, div_le_iff₀ (sq_pos_of_pos hlam), one_mul]
  change A * lam + c ^ 2 ≤ lam ^ 2 ↔ (A + Real.sqrt (A ^ 2 + 4 * c ^ 2)) / 2 ≤ lam
  constructor
  · intro h
    have hAlam : A ≤ lam := by
      by_contra hn
      have hp := mul_pos hlam (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith [sq_nonneg c]
    have hr : Real.sqrt (A ^ 2 + 4 * c ^ 2) ≤ 2 * lam - A := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by linarith, by nlinarith⟩
    linarith
  · intro h
    have hr : Real.sqrt (A ^ 2 + 4 * c ^ 2) ≤ 2 * lam - A := by linarith
    have hsquare := ((Real.sqrt_le_iff).mp hr).2
    nlinarith

private lemma luxNorm_J (a b c : ℝ) (hN : 0 < N a b c) :
    luxNorm exponent (J a b c) = N a b c := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨hN, (scale_iff a b c _ hN).mpr le_rfl⟩
  · intro lam hlam
    exact (scale_iff a b c lam hlam.1).mp hlam.2

private lemma J_InLp (a b c : ℝ) (hN : 0 < N a b c) : InLp exponent (J a b c) :=
  ⟨J_measurable a b c, N a b c, hN, (scale_iff a b c _ hN).mpr le_rfl⟩

private lemma N_special (a b c : ℝ) (ha : |a| + |b| = 1) (hc : c ^ 2 = 1 / 4) :
    N a b c = (1 + Real.sqrt 2) / 2 := by
  simp only [N, ha, hc]
  norm_num

private lemma base_positive : 0 < (1 + Real.sqrt 2) / 2 := by
  positivity

private lemma pair_norms :
    luxNorm exponent (J 0 0 1) = 1 ∧
      luxNorm exponent (J (-1) (-1) 0) = 2 ∧
      luxNorm exponent (J (-1) 1 0) = 2 := by
  have hsqrt : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₁ : N 0 0 1 = 1 := by norm_num [N]; rw [hsqrt]; norm_num
  have h₂ : N (-1) (-1) 0 = 2 := by norm_num [N]; rw [hsqrt]; norm_num
  have h₃ : N (-1) 1 0 = 2 := by norm_num [N]; rw [hsqrt]; norm_num
  exact ⟨(luxNorm_J _ _ _ (by rw [h₁]; norm_num)).trans h₁,
    (luxNorm_J _ _ _ (by rw [h₂]; norm_num)).trans h₂,
    (luxNorm_J _ _ _ (by rw [h₃]; norm_num)).trans h₃⟩

theorem result : ¬ claim := by
  intro hclaim
  have hx : N 0 1 (1 / 2) = (1 + Real.sqrt 2) / 2 := N_special _ _ _ (by norm_num) (by norm_num)
  have hy : N 0 (-1) (1 / 2) = (1 + Real.sqrt 2) / 2 := N_special _ _ _ (by norm_num) (by norm_num)
  have hz : N (-1) 0 (-(1 / 2)) = (1 + Real.sqrt 2) / 2 := N_special _ _ _ (by norm_num) (by norm_num)
  have hw : N (-1) 0 (1 / 2) = (1 + Real.sqrt 2) / 2 := N_special _ _ _ (by norm_num) (by norm_num)
  have hxpos : 0 < N 0 1 (1 / 2) := hx.symm ▸ base_positive
  have hypos : 0 < N 0 (-1) (1 / 2) := hy.symm ▸ base_positive
  have hzpos : 0 < N (-1) 0 (-(1 / 2)) := hz.symm ▸ base_positive
  have hwpos : 0 < N (-1) 0 (1 / 2) := hw.symm ▸ base_positive
  have h := hclaim exponent exponent_measurable (fun t _ => exponent_range t)
    (J 0 1 (1 / 2)) (J 0 (-1) (1 / 2)) (J (-1) 0 (-(1 / 2)))
    (J_InLp _ _ _ hxpos) (J_InLp _ _ _ hypos) (J_InLp _ _ _ hzpos)
  simp only [J_add] at h
  norm_num only at h
  rw [pair_norms.1, pair_norms.2.1, pair_norms.2.2,
    luxNorm_J _ _ _ hxpos, luxNorm_J _ _ _ hypos, luxNorm_J _ _ _ hzpos,
    luxNorm_J _ _ _ hwpos, hx, hy, hz, hw] at h
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

end D5.S3.Geometry.VariableExponentHornichHlawka
