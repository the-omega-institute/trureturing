/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized critical renewal terminal rewards and signed adjacent-grid evidence. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

/-! Source-normalized terminal phase statistics and their adjacent-grid evidence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators NNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap


def reward (r J : ℕ) (z : Fin (J + 1)) : ℝ :=
  if z.val < J then 1 / (2 : ℝ)^(r*(z.val+1)) else 0

def phase (J : ℕ) (f : PMF ℕ) : PMF (Fin (J + 1)) :=
  f.bind (GeometricPhaseOccupation.finiteCappedLaw J)

def average {J : ℕ} (p : PMF (Fin (J + 1))) (v : Fin (J + 1) → ℝ) : ℝ :=
  ∑ z, (p z).toReal * v z

def grid (r J : ℕ) : ℝ := (J : ℝ)/(2 : ℝ)^(r*J)

private lemma pmf_sum_real {α : Type*} [Fintype α] (p : PMF α) :
    ∑ z, (p z).toReal = 1 := by
  simpa only [tsum_fintype, p.tsum_coe, ENNReal.toReal_one] using
    (ENNReal.tsum_toReal_eq p.apply_ne_top).symm

private lemma average_nonneg {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (hv : ∀ z, 0 ≤ v z) : 0 ≤ average p v :=
  sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (hv z)

private lemma average_le {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (C : ℝ) (hv : ∀ z, v z ≤ C) :
    average p v ≤ C := by
  calc
    _ ≤ ∑ z, (p z).toReal * C :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hv z) ENNReal.toReal_nonneg
    _ = C := by rw [← sum_mul, pmf_sum_real, one_mul]

private lemma reward_bounds (r J : ℕ) (hr : 1 ≤ r) (z : Fin (J + 1)) :
    0 ≤ reward r J z ∧ reward r J z ≤ 1/(2 : ℝ)^r ∧
      reward r J z ≤ 1/2 := by
  have hpow : (2 : ℝ)^r ≤ (2 : ℝ)^(r*(z.val+1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^r := by
    simpa using pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr
  unfold reward
  split_ifs <;> constructor <;> try positivity
  · constructor
    · exact one_div_le_one_div_of_le (by positivity) hpow
    · exact one_div_le_one_div_of_le (by norm_num) (htwo.trans hpow)
  · constructor <;> positivity

private lemma discounted_real (m : ℕ) (s : ℝ) (k : ℕ) :
    (GeometricPhaseOccupation.discountedWeight m s k).toReal = CriticalRenewalSource.term m s k := by
  by_cases hk : k = 0
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk]
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

private lemma occupation_series (m J : ℕ) (j : Fin J) (s eta : ℝ)
    (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1) :
    Summable (fun k => CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) ∧
    (∑' k, CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) = GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.lowerConstant m * (2 : ℝ)^((j.val+1)*(m+1)) ≤
      GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.occupation m s (j.val+1) ≤
      GeometricPhaseOccupation.upperConstant m * (2 : ℝ)^((j.val+1)*(m+1)) := by
  have hj : j.val+1 ≤ J := by omega
  have hsj : s*(2 : ℝ)^(j.val+1) ≤ eta :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) hj) hs.le).trans hscale
  have h := GeometricPhaseOccupation.uniform_discounted_phase_occupation m (j.val+1) (by omega)
    s eta hs hsj heta
  have he := h.2.2.2.2.2.2.2 J hj
  have hcast : (⟨j.val+1-1, by omega⟩ : Fin (J + 1)) = j.castSucc :=
    Fin.ext (by simp)
  rw [hcast] at he
  have hf : (∑' k, GeometricPhaseOccupation.discountedWeight m s k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ := by
    exact he.trans_ne h.2.2.2.1
  have hh := ENNReal.hasSum_toReal hf
  simp only [ENNReal.toReal_mul, discounted_real] at hh
  refine ⟨hh.summable, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  change _ = (GeometricPhaseOccupation.actualOccupation
    (GeometricPhaseOccupation.discountedWeight m s) ((j.val+1)-1)).toReal
  rw [← he, ENNReal.tsum_toReal_eq (fun k => by finiteness)]
  simp only [ENNReal.toReal_mul, discounted_real]

private lemma phase_live_mass (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s*(2 : ℝ)^J ≤ eta) (heta : eta ≤ 1)
    (i : Bool) (j : Fin J) :
    (phase J (CriticalRenewalSource.gapLaw r hr c hc i s hs) j.castSucc).toReal =
      (GeometricPhaseOccupation.occupation (2*r-1) s (j.val+1) +
        if i then c*GeometricPhaseOccupation.occupation (r-1) s (j.val+1) else 0) /
        CriticalRenewalSource.normalizer r c i s := by
  have hsrc := (CriticalRenewalSource.source_laws r hr c hc s hs).1.1 i
  have he (k : ℕ) : (CriticalRenewalSource.gapLaw r hr c hc i s hs k).toReal = CriticalRenewalSource.density r c i s k :=
    ENNReal.toReal_ofReal (hsrc.density_nonnegative k)
  have hd := occupation_series (2*r-1) J j s eta hs hscale heta
  have hl := occupation_series (r-1) J j s eta hs hscale heta
  have hb := ENNReal.hasSum_toReal
    (show (∑' k, CriticalRenewalSource.gapLaw r hr c hc i s hs k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ from
        by rw [← PMF.bind_apply]; exact (phase J _).apply_ne_top _)
  simp only [ENNReal.toReal_mul, he] at hb
  rw [phase, PMF.bind_apply, ENNReal.tsum_toReal_eq (fun k => by finiteness)]
  simp only [ENNReal.toReal_mul, he]
  simp only [CriticalRenewalSource.density, CriticalRenewalSource.weight, add_div, mul_add, add_mul, div_mul_eq_mul_div]
  cases i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_div, zero_mul]
    rw [tsum_div_const, hd.2.1]
  | true =>
    simp only [↓reduceIte]
    have hs2 := hl.1.mul_left c
    rw [tsum_add (hd.1.div_const _) (by simpa only [mul_assoc] using hs2.div_const _),
      tsum_div_const, hd.2.1, tsum_div_const, ← tsum_mul_left, hl.2.1]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap
