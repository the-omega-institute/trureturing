/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Derivative, unique minimum and boundaries of the labelled B=C curve. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree

/-!
The labelled curve has A=N-2b and B=C=b. Its positive scalar domain is
0<b<N/2; physical mode counts additionally must be positive integers.
Haobo Ma then Wenlin Zhang, 4 November 2026, CC BY 4.0; Camargo–Nishida
for the physical family and its equal-party observation. Subsystem size
is not a dynamical evaporation parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve

open ReplicaThreeScalar ReplicaThree

/-- The B=C curve of the scalar extension, with its labelled A party. -/
def curve (k N b : ℝ) : ℝ := value k (N - 2 * b) b b

private def main (k N b : ℝ) : ℝ := 1 + k * (2 * N * b - 3 * b ^ 2)
private def leftCut (k N b : ℝ) : ℝ := 1 + 2 * k * b * (N - 2 * b)
private def rightCut (k N b : ℝ) : ℝ := 1 + k * b * (N - b)

private lemma curve_formula (k N b : ℝ) :
    curve k N b = (2 * Real.log (main k N b) -
      Real.log (leftCut k N b) - 2 * Real.log (rightCut k N b)) / 12 := by
  have hs : pairSum (N - 2 * b) b b = 2 * N * b - 3 * b ^ 2 := by
    unfold pairSum; ring
  have hl : cut k (N - 2 * b) b b = leftCut k N b := by
    unfold cut leftCut; ring
  have hr : cut k b (N - 2 * b) b = rightCut k N b := by
    unfold cut rightCut; ring
  unfold curve value
  rw [hs, hl, hr]
  unfold main
  ring

private lemma factors_pos (k N b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b)
    (hA : 0 ≤ N - 2 * b) :
    0 < main k N b ∧ 0 < leftCut k N b ∧ 0 < rightCut k N b := by
  have hm : main k N b = 1 + k * (2 * (N - 2 * b) * b + b ^ 2) := by
    unfold main; ring
  have hr : rightCut k N b = 1 + k * b * ((N - 2 * b) + b) := by
    unfold rightCut; ring
  rw [hm, hr]
  unfold leftCut
  exact ⟨by positivity, by positivity, by positivity⟩

/-- The exact derivative coefficient; its denominator is positive in the
positive scalar domain and its only sign-changing factor is `3*b-N`. -/
def curveDerivative (k N b : ℝ) : ℝ :=
  k ^ 2 * b * (3 * b - N) *
    (N + k * (2 * (N - 2 * b) ^ 2 * b + 3 * (N - 2 * b) * b ^ 2 + 2 * b ^ 3)) /
      (6 * leftCut k N b * rightCut k N b * main k N b)

private lemma derivative_formula (k N b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b)
    (hA : 0 ≤ N - 2 * b) :
    HasDerivAt (curve k N) (curveDerivative k N b) b := by
  obtain ⟨hm,hl,hr⟩ := factors_pos k N b hk hb hA
  have dm : HasDerivAt (main k N) (k * (2 * N - 6 * b)) b := by
    convert ((((hasDerivAt_id b).const_mul (2 * N)).sub
      (((hasDerivAt_id b).pow 2).const_mul 3)).const_mul k).const_add 1 using 1 <;>
      (try funext x) <;> dsimp [main] <;> ring
  have dl : HasDerivAt (leftCut k N) (2 * k * (N - 4 * b)) b := by
    convert ((((hasDerivAt_id b).const_mul (2 * k)).mul
      ((hasDerivAt_const b N).sub ((hasDerivAt_id b).const_mul 2))).const_add 1)
      using 1 <;> (try funext x) <;> dsimp [leftCut] <;> ring
  have dr : HasDerivAt (rightCut k N) (k * (N - 2 * b)) b := by
    convert ((((hasDerivAt_id b).const_mul k).mul
      ((hasDerivAt_const b N).sub (hasDerivAt_id b))).const_add 1)
      using 1 <;> (try funext x) <;> dsimp [rightCut] <;> ring
  have hd := ((((dm.log hm.ne').const_mul 2).sub (dl.log hl.ne')).sub
    ((dr.log hr.ne').const_mul 2)).div_const 12
  have he : (2 * (k * (2 * N - 6 * b) / main k N b) -
      2 * k * (N - 4 * b) / leftCut k N b -
      2 * (k * (N - 2 * b) / rightCut k N b)) / 12 = curveDerivative k N b := by
    unfold curveDerivative
    field_simp
    unfold main leftCut rightCut
    ring
  rw [he] at hd
  convert hd using 1
  exact funext (curve_formula k N)

/-- Exact derivative and its negative/zero/positive classification on the
whole positive scalar domain. Strict signs require nonvacuum `k>0`. -/
theorem curve_derivative (k N b : ℝ) (hk : 0 < k) (hN : 0 < N)
    (hb : b ∈ Ioo 0 (N / 2)) :
    HasDerivAt (curve k N) (curveDerivative k N b) b ∧
      (deriv (curve k N) b < 0 ↔ b < N / 3) ∧
      (deriv (curve k N) b = 0 ↔ b = N / 3) ∧
      (0 < deriv (curve k N) b ↔ N / 3 < b) := by
  have hb0 : 0 < b := hb.1
  have hA : 0 < N - 2 * b := by linarith [hb.2]
  have hd := derivative_formula k N b hk.le hb.1.le hA.le
  obtain ⟨hm,hl,hr⟩ := factors_pos k N b hk.le hb.1.le hA.le
  have hbr : 0 < N + k * (2 * (N - 2 * b) ^ 2 * b +
      3 * (N - 2 * b) * b ^ 2 + 2 * b ^ 3) := by positivity
  have hden : 0 < 6 * leftCut k N b * rightCut k N b * main k N b := by positivity
  have hc : 0 < k ^ 2 * b *
      (N + k * (2 * (N - 2 * b) ^ 2 * b + 3 * (N - 2 * b) * b ^ 2 + 2 * b ^ 3)) :=
    mul_pos (mul_pos (sq_pos_of_pos hk) hb.1) hbr
  have he : curveDerivative k N b =
      (k ^ 2 * b * (N + k * (2 * (N - 2 * b) ^ 2 * b +
        3 * (N - 2 * b) * b ^ 2 + 2 * b ^ 3)) / (6 * leftCut k N b *
          rightCut k N b * main k N b)) * (3 * b - N) := by
    unfold curveDerivative
    ring
  have hcoeff := div_pos hc hden
  refine ⟨hd, ?_, ?_, ?_⟩ <;> rw [hd.deriv, he]
  · have hn : ¬ (k ^ 2 * b *
        (N + k * (2 * (N - 2 * b) ^ 2 * b + 3 * (N - 2 * b) * b ^ 2 + 2 * b ^ 3)) /
          (6 * leftCut k N b * rightCut k N b * main k N b)) < 0 := not_lt_of_gt hcoeff
    simp only [mul_neg_iff, hcoeff, hn, true_and, false_and, or_false, false_or]
    constructor <;> intro h <;> linarith
  · rw [mul_eq_zero, or_iff_right (ne_of_gt hcoeff)]; constructor <;> intro h <;> linarith
  · rw [mul_pos_iff_of_pos_left hcoeff]; constructor <;> intro h <;> linarith

private lemma continuousAt_curve (k N b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b)
    (hA : 0 ≤ N - 2 * b) : ContinuousAt (curve k N) b :=
  (derivative_formula k N b hk hb hA).continuousAt

/-- Strict decrease and increase on either side of the unique continuous
minimum. Vacuum instead gives the constant zero curve, including boundaries. -/
theorem curve_minimum (k N : ℝ) (hk : 0 < k) (hN : 0 < N) :
    StrictAntiOn (curve k N) (Ioc 0 (N / 3)) ∧
      StrictMonoOn (curve k N) (Ico (N / 3) (N / 2)) ∧
      ∀ b ∈ Ioo 0 (N / 2), curve k N (N / 3) ≤ curve k N b ∧
        (curve k N b = curve k N (N / 3) ↔ b = N / 3) := by
  have ha : StrictAntiOn (curve k N) (Ioc 0 (N / 3)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    · intro b hb
      exact (continuousAt_curve k N b hk.le hb.1.le (by linarith [hb.2])).continuousWithinAt
    · intro b hb
      have hb' : b ∈ Ioo 0 (N / 3) := by simpa using hb
      exact (curve_derivative k N b hk hN ⟨hb'.1, by linarith [hb'.2]⟩).2.1.mpr hb'.2
  have hm : StrictMonoOn (curve k N) (Ico (N / 3) (N / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
    · intro b hb
      exact (continuousAt_curve k N b hk.le (by linarith [hb.1])
        (by linarith [hb.2])).continuousWithinAt
    · intro b hb
      have hb' : b ∈ Ioo (N / 3) (N / 2) := by simpa using hb
      exact (curve_derivative k N b hk hN ⟨by linarith [hb'.1], hb'.2⟩).2.2.2.mpr hb'.1
  refine ⟨ha, hm, ?_⟩
  intro b hb
  rcases lt_trichotomy b (N / 3) with h | h | h
  · have hlt := ha ⟨hb.1,h.le⟩ ⟨by positivity,le_rfl⟩ h
    exact ⟨hlt.le, iff_of_false (Ne.symm hlt.ne) (ne_of_lt h)⟩
  · subst b
    exact ⟨le_rfl, iff_of_true rfl rfl⟩
  · have hlt := hm ⟨le_rfl,by linarith⟩ ⟨h.le,hb.2⟩ h
    exact ⟨hlt.le, iff_of_false (Ne.symm hlt.ne) (ne_of_gt h)⟩

/-- Scalar endpoints are zero and the one-sided limits are zero. Neither
endpoint belongs to the physical theorem with three positive parties. -/
theorem curve_boundaries (k N : ℝ) (hk : 0 ≤ k) (hN : 0 < N) :
    curve k N 0 = 0 ∧ curve k N (N / 2) = 0 ∧
      Tendsto (curve k N) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (curve k N) (𝓝[<] (N / 2)) (𝓝 0) ∧
      (∀ b : ℝ, curve 0 N b = 0) := by
  have h0 : curve k N 0 = 0 := by simp [curve_formula, main, leftCut, rightCut]
  have hhalf : curve k N (N / 2) = 0 := by
    have hm : main k N (N / 2) = rightCut k N (N / 2) := by
      unfold main rightCut; ring
    have hl : leftCut k N (N / 2) = 1 := by unfold leftCut; ring
    rw [curve_formula, hm, hl, Real.log_one]
    ring
  refine ⟨h0,hhalf, ?_, ?_, ?_⟩
  · have ht := (continuousAt_curve k N 0 hk le_rfl (by linarith)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [h0] using ht
  · have ht := (continuousAt_curve k N (N / 2) hk (by positivity) (by linarith)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (N / 2)))
    simpa only [hhalf] using ht
  · intro b
    simp [curve, value, cut]

/-- When the total is divisible by three the physical positive-integer B=C
curve has its unique minimum at `b=N/3`. At that point B+C is exactly `2N/3`.
The first clause identifies the actual integral with the labelled scalar curve;
no fractional-mode interpretation is made. -/
theorem physical_curve_minimum (N : ℕ) (hN : 3 ≤ N) (hdiv : 3 ∣ N)
    (a : ℝ) (ha : 1 < a) (b : ℕ) (hb : 0 < b) (hA : 2 * b < N) :
    GaussianMultiEntropyAsymptotic.GM3 3 (N - 2 * b) b b a =
        curve (kappa N a) N b ∧
    GaussianMultiEntropyAsymptotic.GM3 3 (N / 3) (N / 3) (N / 3) a ≤
        GaussianMultiEntropyAsymptotic.GM3 3 (N - 2 * b) b b a ∧
    (GaussianMultiEntropyAsymptotic.GM3 3 (N - 2 * b) b b a =
        GaussianMultiEntropyAsymptotic.GM3 3 (N / 3) (N / 3) (N / 3) a ↔ b = N / 3) ∧
    (b = N / 3 ↔ (b : ℝ) + b = 2 * (N : ℝ) / 3) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hk : 0 < kappa N a := by
    unfold kappa
    exact div_pos (by nlinarith) (by linarith)
  have hrepr (c : ℕ) (hc : 0 < c) (hcA : 2 * c < N) :
      GaussianMultiEntropyAsymptotic.GM3 3 (N - 2 * c) c c a =
        curve (kappa N a) N c := by
    have hs : (N - 2 * c : ℕ) + c + c = N := by omega
    have hsc : ((N - 2 * c : ℕ) : ℝ) + c + c = N := by exact_mod_cast hs
    have hAc : ((N - 2 * c : ℕ) : ℝ) = (N : ℝ) - 2 * c := by linarith
    rw [GM3_three_closed _ _ _ a (by omega) hc hc ha.le, hsc]
    rw [← value_eq_log_ratio _ _ _ _ hk.le (by positivity) (by positivity) (by positivity)]
    rw [curve, hAc]
  have hq : 0 < N / 3 := Nat.div_pos hN (by norm_num)
  have hmod : N % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsum : N / 3 * 3 = N := by omega
  have hqr : ((N / 3 : ℕ) : ℝ) = (N : ℝ) / 3 := by
    have he : ((N / 3 : ℕ) : ℝ) * 3 = N := by exact_mod_cast hsum
    linarith
  have hqA : 2 * (N / 3) < N := by omega
  have heqA : N - 2 * (N / 3) = N / 3 := by omega
  have hrq : GaussianMultiEntropyAsymptotic.GM3 3 (N / 3) (N / 3) (N / 3) a =
      curve (kappa N a) N ((N : ℝ) / 3) := by
    simpa only [heqA, hqr] using hrepr (N / 3) hq hqA
  have hbr : (b : ℝ) ∈ Ioo 0 ((N : ℝ) / 2) := by
    constructor
    · exact_mod_cast hb
    · have : 2 * (b : ℝ) < N := by exact_mod_cast hA
      linarith
  obtain ⟨hle,heq⟩ := (curve_minimum (kappa N a) N hk (by linarith)).2.2 b hbr
  refine ⟨hrepr b hb hA, ?_, ?_, ?_⟩
  · rw [hrq, hrepr b hb hA]
    exact hle
  · rw [hrq, hrepr b hb hA, heq, ← hqr]
    exact Nat.cast_inj
  · constructor
    · intro h
      have he : (b : ℝ) = (N / 3 : ℕ) := by exact_mod_cast h
      linarith
    · intro h
      exact_mod_cast (show (b : ℝ) = (N / 3 : ℕ) by linarith)

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
