/- GID: D5/S3/StatisticalMechanics/DelayedCooling/Volterra
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/Volterra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise uniqueness and derived regularity for the integrated cooling equation. -/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# The raw integrated delay equation

The input is the finite-Lebesgue meaning of the source equation, with an
equilibrated past starting at an arbitrary real time. Neither continuity of
the sample nor separate integrability of the bath is an input. Bath functions
remain raw functions; no almost-everywhere quotient or essential supremum is
used. This does not identify every unspecified source integral convention
with the Lebesgue convention.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.Volterra

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A raw sample satisfying the integrated DDE with its own finite equilibrium
past. The integrability field gives the meaning of the input integral, not a
separate bath-regularity assumption. Values at quench times are retained. -/
structure IntegratedSolution (τ a q : ℝ) (b T : ℝ → ℝ) : Prop where
  past : ∀ t ≤ a, T t = q
  forcing_integrable : ∀ t, a ≤ t →
    IntervalIntegrable (fun s => b s - T (s - τ)) volume a t
  equation : ∀ t, a ≤ t → T t = q + ∫ s in a..t, (b s - T (s - τ))

private theorem primitive_ac {a q : ℝ} {f T : ℝ → ℝ}
    {t : ℝ} (ht : a ≤ t) (hint : IntervalIntegrable f volume a t)
    (heq : ∀ s, a ≤ s → T s = q + ∫ u in a..s, f u) :
    AbsolutelyContinuousOnInterval T a t := by
  have hi := hint.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => q) a t := by
    exact (LipschitzWith.const q).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add hi).congr
  rw [uIcc_of_le ht]
  intro s hs
  exact (heq s hs.1).symm

private theorem primitive_continuous {a q : ℝ} {f T : ℝ → ℝ}
    (hpast : ∀ t ≤ a, T t = q)
    (hint : ∀ t, a ≤ t → IntervalIntegrable f volume a t)
    (heq : ∀ t, a ≤ t → T t = q + ∫ u in a..t, f u) : Continuous T := by
  have hp : ContinuousOn T (Iic a) := continuousOn_const.congr
    (fun s hs => hpast s hs)
  apply continuous_iff_continuousAt.mpr
  intro t
  let B := max a t + 1
  have haB : a ≤ B := by dsimp [B]; have := le_max_left a t; linarith
  have htB : t < B := by dsimp [B]; have := le_max_right a t; linarith
  have hc := (primitive_ac haB (hint B haB) heq).continuousOn
  rw [uIcc_of_le haB] at hc
  have hu := hp.union_of_isClosed hc isClosed_Iic isClosed_Icc
  rw [Iic_union_Icc_eq_Iic haB] at hu
  exact hu.continuousAt (Iic_mem_nhds htB)

private theorem solution_ac {τ a q : ℝ} {b T : ℝ → ℝ}
    (hT : IntegratedSolution τ a q b T) {t : ℝ} (ht : a ≤ t) :
    AbsolutelyContinuousOnInterval T a t :=
  primitive_ac ht (hT.forcing_integrable t ht) hT.equation

private theorem solution_continuous {τ a q : ℝ} {b T : ℝ → ℝ}
    (hT : IntegratedSolution τ a q b T) : Continuous T :=
  primitive_continuous hT.past hT.forcing_integrable hT.equation

private theorem solution_unique {τ a q : ℝ} {b T U : ℝ → ℝ}
    (hτ : 0 < τ) (hT : IntegratedSolution τ a q b T)
    (hU : IntegratedSolution τ a q b U) : T = U := by
  have steps : ∀ n : ℕ, ∀ t : ℝ, t ≤ a + n * τ → T t = U t := by
    intro n
    induction n with
    | zero =>
        intro t ht
        simp only [Nat.cast_zero, zero_mul, add_zero] at ht
        rw [hT.past t ht, hU.past t ht]
    | succ n ih =>
        intro t ht
        by_cases hta : t ≤ a
        · rw [hT.past t hta, hU.past t hta]
        have hat := (lt_of_not_ge hta).le
        rw [hT.equation t hat, hU.equation t hat]
        congr 1
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hat]
        intro s hs
        have he : T (s - τ) = U (s - τ) := ih _ (by
          push_cast at ht
          nlinarith [hs.2])
        dsimp
        rw [he]
  funext t
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / τ)
  apply steps n t
  have := (div_lt_iff₀ hτ).mp hn
  linarith

/-- The integrated equation forces a continuous raw sample, local absolute
continuity and bath integrability, and has at most one pointwise solution.
At each ordinary time where the raw bath is continuous it gives the original
DDE. No continuity premise on the sample is needed. -/
theorem integrated_solution_bridge {τ a q : ℝ} {b T : ℝ → ℝ}
    (hτ : 0 < τ) (hT : IntegratedSolution τ a q b T) :
    Continuous T ∧
    (∀ t, a ≤ t → AbsolutelyContinuousOnInterval T a t) ∧
    (∀ t, a ≤ t → IntervalIntegrable b volume a t) ∧
    (∀ t, a < t → ContinuousAt b t →
      HasDerivAt T (b t - T (t - τ)) t) ∧
    (∀ U, IntegratedSolution τ a q b U → T = U) := by
  have hc := solution_continuous hT
  have hdelay : Continuous (fun s => T (s - τ)) :=
    hc.comp (continuous_id.sub continuous_const)
  refine ⟨hc, (fun t ht => solution_ac hT ht), ?_, ?_, ?_⟩
  · intro t ht
    have hi := (hT.forcing_integrable t ht).add
      (hdelay.intervalIntegrable a t)
    simpa only [sub_add_cancel] using hi
  · intro t ht hb
    let f : ℝ → ℝ := fun s => b s - T (s - τ)
    have hf : ContinuousAt f t := hb.sub
      ((hc.comp (continuous_id.sub continuous_const)).continuousAt)
    have hi := hT.forcing_integrable (t + 1) (by linarith)
    have hm : StronglyMeasurableAtFilter f (𝓝 t) volume :=
      ⟨Ioc a (t + 1), Ioc_mem_nhds ht (by linarith), hi.1.aestronglyMeasurable⟩
    have hd := (intervalIntegral.integral_hasDerivAt_right
      (hT.forcing_integrable t ht.le) hm hf).const_add q
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hT.equation s hs.le
  · intro U hU
    exact solution_unique hτ hT hU

private def approximation (τ a q : ℝ) (b : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => q
  | n + 1 => fun t => if t ≤ a then q else
      q + ∫ s in a..t, b s - approximation τ a q b n (s - τ)

private theorem approximation_past (τ a q : ℝ) (b : ℝ → ℝ) (n : ℕ)
    {t : ℝ} (ht : t ≤ a) : approximation τ a q b n t = q := by
  cases n <;> simp [approximation, ht]

private theorem approximation_equation (τ a q : ℝ) (b : ℝ → ℝ) (n : ℕ)
    {t : ℝ} (ht : a ≤ t) : approximation τ a q b (n + 1) t =
      q + ∫ s in a..t, b s - approximation τ a q b n (s - τ) := by
  by_cases he : t ≤ a
  · have heq : t = a := le_antisymm he ht
    subst t
    simp [approximation]
  · simp [approximation, he]

private theorem approximation_continuous {τ a q : ℝ} {b : ℝ → ℝ}
    (hb : ∀ t, a ≤ t → IntervalIntegrable b volume a t) :
    ∀ n, Continuous (approximation τ a q b n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      apply primitive_continuous
        (fun t ht => approximation_past τ a q b (n + 1) ht)
        (fun t ht => (hb t ht).sub
          ((ih.comp (continuous_id.sub continuous_const)).intervalIntegrable a t))
        (fun t ht => approximation_equation τ a q b n ht)

private theorem approximation_stable {τ a q : ℝ} (b : ℝ → ℝ) :
    ∀ n m : ℕ, n ≤ m → ∀ t : ℝ, t ≤ a + n * τ →
      approximation τ a q b m t = approximation τ a q b n t := by
  intro n
  induction n with
  | zero =>
      intro m _ t ht
      have hta : t ≤ a := by simpa using ht
      rw [approximation_past τ a q b m hta, approximation_past τ a q b 0 hta]
  | succ n ih =>
      intro m hnm t ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      by_cases hta : t ≤ a
      · rw [approximation_past τ a q b (k + 1) hta,
          approximation_past τ a q b (n + 1) hta]
      have hat : a ≤ t := (lt_of_not_ge hta).le
      rw [approximation_equation τ a q b k hat, approximation_equation τ a q b n hat]
      congr 1
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hat]
      intro s hs
      dsimp
      rw [ih k (by omega) (s - τ) (by push_cast at ht; nlinarith [hs.2])]

/-- Every bath that is Lebesgue integrable on each finite interval after the
individual preparation start has exactly one integrated raw sample. Finite
method-of-steps approximations stabilize on each delay-length past, so no
solution or convolution is assumed in this existence result. -/
theorem exists_unique_integrated_solution {τ a q : ℝ} (hτ : 0 < τ) (b : ℝ → ℝ)
    (hb : ∀ t, a ≤ t → IntervalIntegrable b volume a t) :
    ∃! T, IntegratedSolution τ a q b T := by
  let N : ℝ → ℕ := fun t => ⌊(t - a) / τ⌋₊ + 1
  let T : ℝ → ℝ := fun t => approximation τ a q b (N t) t
  have hN (t : ℝ) : t ≤ a + (N t : ℝ) * τ := by
    have hf := Nat.lt_floor_add_one ((t - a) / τ)
    have hh := (div_lt_iff₀ hτ).mp hf
    dsimp [N]
    push_cast
    linarith
  have heq (n : ℕ) (t : ℝ) (ht : t ≤ a + n * τ) :
      T t = approximation τ a q b n t := by
    dsimp [T]
    rcases le_total n (N t) with h | h
    · exact approximation_stable b n (N t) h t ht
    · exact (approximation_stable b (N t) n h t (hN t)).symm
  have hT : IntegratedSolution τ a q b T := by
    constructor
    · intro t ht
      exact approximation_past τ a q b (N t) ht
    · intro t ht
      obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / τ)
      have htn : t ≤ a + n * τ := by have := (div_lt_iff₀ hτ).mp hn; linarith
      have hc : Continuous (fun s => approximation τ a q b n (s - τ)) :=
        (approximation_continuous (τ := τ) (q := q) hb n).comp
          (continuous_id.sub continuous_const)
      have hi := (hb t ht).sub (hc.intervalIntegrable a t)
      apply hi.congr
      rw [uIoc_of_le ht]
      intro s hs
      dsimp
      rw [heq n (s - τ) (by linarith [hs.2])]
    · intro t ht
      obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / τ)
      have htn : t ≤ a + n * τ := by have := (div_lt_iff₀ hτ).mp hn; linarith
      rw [heq (n + 1) t (by push_cast; nlinarith), approximation_equation τ a q b n ht]
      congr 1
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht]
      intro s hs
      dsimp
      rw [heq n (s - τ) (by linarith [hs.2])]
  exact ⟨T, hT, fun U hU => solution_unique hτ hU hT⟩

end

end D5.S3.StatisticalMechanics.DelayedCooling.Volterra
