/- GID: D5/S3/Arith/Lattices/Klartag/Completion/PackingBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/PackingBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.AdoptedConstants95
import D5.S3.Arith.Lattices.Klartag.Contact.CutVariance
import D5.S3.Arith.Lattices.Klartag.Tail.TailWiring
import D5.S3.Arith.Lattices.Klartag.Walk.ChainShortfall
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R5
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaIntegrated99
import D5.S3.Arith.Lattices.Klartag.Completion.FailTotalBound99

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.Lemma43R3
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Packing

open MeasureTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2
open D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4
open D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge

/-- The same with the ceiling on the failure budget free as well. -/
theorem budget_lt_one'' {num den F Anum Bden Fb : ℝ} (hA : 0 ≤ Anum) (hB : 0 < Bden)
    (hnum : num ≤ Anum) (hden : Bden ≤ den) (hF : F ≤ Fb)
    (hsum : Anum / Bden + Fb < 1) : num / den + F < 1 := by
  have hd0 : (0 : ℝ) < den := by linarith
  have hratio : num / den ≤ Anum / Bden := div_le_div₀ hA hnum hB hden
  linarith

section Qrt

variable {n : ℕ}

/-- **`r₀ ≤ 8/q`.**  `log n/n ≤ 4/q³ ≤ 1/(9q²)` because `q ≥ 36`, and the square root of the
right-hand side is `1/(3q)`. -/
theorem r0_le_qrt (hn : 2073600 ≤ n) :
    DriftStopped6.r0Adopted n ≤ 8 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set qq := Real.sqrt (Real.sqrt (n : ℝ)) with hqdef
  have hq37 : (37 : ℝ) ≤ qq := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < qq := by linarith
  have hqne : qq ≠ 0 := ne_of_gt hq0
  have hq4 : qq ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn0.le
  have hlog : Real.log n ≤ 4 * qq := WindowR.log_le_four_qrt hn
  have hkey : Real.log n / (n : ℝ) ≤ (1 / (3 * qq)) ^ 2 := by
    rw [div_le_iff₀ hn0]
    have hid : (1 / (3 * qq)) ^ 2 * (n : ℝ) = qq ^ 2 / 9 := by
      rw [← hq4]; field_simp; ring
    rw [hid]
    nlinarith [hlog, hq37, hq0]
  have hs : Real.sqrt (Real.log n / (n : ℝ)) ≤ 1 / (3 * qq) := by
    have h0 : (0 : ℝ) ≤ 1 / (3 * qq) := by positivity
    calc Real.sqrt (Real.log n / (n : ℝ))
        ≤ Real.sqrt ((1 / (3 * qq)) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = 1 / (3 * qq) := Real.sqrt_sq h0
  have hid2 : (24 : ℝ) * (1 / (3 * qq)) = 8 / qq := by field_simp; ring
  rw [DriftStopped6.r0Adopted, ← hid2]
  linarith

/-- **`η ≤ 1/q`.**  `η ≤ √2/n³ ≤ 2/q¹² ≤ 1/q`. -/
theorem eta_le_qrt (hn : 2073600 ≤ n) :
    DriftStopped6.etaAdopted n ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hcube : (n : ℝ) ^ 3 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 :=
    DriftStopped6c.cube_eq_qrt hn0.le
  have h1 : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
    rw [DriftStopped6.etaAdopted]; exact ParamsAdopted2.eta2_le (by omega)
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc0 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have h4 : Real.sqrt 2 / (n : ℝ) ^ 3 ≤ 2 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hc0 hc0]; nlinarith [h2, hc0]
  have hq12 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 ≤ Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : (2 : ℝ) / (n : ℝ) ^ 3 ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ hc0 hq0, one_mul, hcube]
    nlinarith [hq37, hq0, hq12]
  linarith

/-- `card (UT n) > 0`. -/
theorem card_UT_pos (hn : 3 ≤ n) : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
  have hpos : 0 < Fintype.card (UT n) := by
    rw [ChainWiring.card_UT]
    have h34 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  exact_mod_cast hpos

/-- `η > 0`: `η² = 2·h·card·n` and all three factors are positive. -/
theorem eta_pos (hn : 3 ≤ n) : (0 : ℝ) < DriftStopped6.etaAdopted n := by
  have hsq := TruncSumMean.etaAdopted_sq (n := n) hn
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n :=
    TailSideSetup2.stepSizeAdopted2_pos hn
  have hD := card_UT_pos (n := n) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (0 : ℝ) < DriftStopped6.etaAdopted n ^ 2 := by rw [hsq]; positivity
  exact lt_of_le_of_ne DriftStopped7.etaAdopted_nonneg
    (by intro h; rw [← h] at h2; norm_num at h2)

/-- **`failTotal` is nonnegative.** -/
theorem failTotal_nonneg (hn : 3 ≤ n) {pcnt : ℝ} (hpc : 0 ≤ pcnt) :
    0 ≤ GoodPathBounds.failTotal n pcnt := by
  have hlog0 : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  rw [GoodPathBounds.failTotal]
  have ha : (0 : ℝ) ≤ 33 * (n : ℝ) ^ 9 * Real.log (n : ℝ) := mul_nonneg (by positivity) hlog0
  have hb : (0 : ℝ) ≤ (33 * (n : ℝ) ^ 9 * Real.log (n : ℝ) + 4) * Real.exp (-(n : ℝ)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have hc : (0 : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
      * (2 * (4 * Real.exp (-((1 : ℝ) ^ 2 * (n : ℝ))))) := by positivity
  linarith

end Qrt

section KappaCq

/-- `1/mm² ≤ 1 + 8u`, hence `(1/2 + 2rr)/mm² ≤ 1/2 + 12u + 2rr`. -/
theorem kappa_upper {u mm rr : ℝ} (hmu : 1 - u ≤ mm) (hm2 : 1 / 2 ≤ mm) (hm1 : mm ≤ 1)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 3) (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2) :
    (1 / 2 + 2 * rr) / mm ^ 2 ≤ 1 / 2 + 12 * u + 2 * rr := by
  have hm0 : (0 : ℝ) < mm := by linarith
  have hinv : 1 / mm ^ 2 ≤ 1 + 8 * u := by
    have hpos : (0 : ℝ) ≤ 1 - u := by linarith
    have hsq : (1 - u) ^ 2 ≤ mm ^ 2 := by nlinarith [hmu, hpos]
    have hquad : (0 : ℝ) ≤ 6 - 15 * u + 8 * u ^ 2 := by
      nlinarith [sq_nonneg (u - 1 / 2), hu, hu0]
    have hone : (1 : ℝ) ≤ (1 + 8 * u) * (1 - u) ^ 2 := by nlinarith [mul_nonneg hu0 hquad]
    have hmul : (1 + 8 * u) * (1 - u) ^ 2 ≤ (1 + 8 * u) * mm ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsplit : (1 / 2 + 2 * rr) / mm ^ 2 = (1 / 2 + 2 * rr) * (1 / mm ^ 2) := by ring
  rw [hsplit]
  nlinarith [hinv, mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 1 / 2 - rr), hrr0, hu0]

/-- `1/(2Z²) ≥ 1/2 − 4u − 3δ` whenever `1 ≤ Z` and `Z² ≤ 1 + 8u + 6δ`. -/
theorem cq_of_Z {Z u dd : ℝ} (hZ1 : 1 ≤ Z) (hZsq : Z ^ 2 ≤ 1 + 8 * u + 6 * dd)
    (hu0 : 0 ≤ u) (hd0 : 0 ≤ dd) : 1 / 2 - 4 * u - 3 * dd ≤ 1 / (2 * Z ^ 2) := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZ2 : (1 : ℝ) ≤ Z ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hZsq, hZ2,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * u + 6 * dd) (by linarith : (0 : ℝ) ≤ Z ^ 2 - 1)]

/-- `1/2 − 1/(2·MM²(1+δ)²) ≤ 4u + 3δ` at `MM ≤ 1 + 2u`. -/
theorem cq_lower {u MM dd : ℝ} (hM1 : 1 ≤ MM) (hMu : MM ≤ 1 + 2 * u)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 3) (hd0 : 0 ≤ dd) (hd : dd ≤ 1 / 4) :
    1 / 2 - 4 * u - 3 * dd ≤ 1 / (2 * MM ^ 2 * (1 + dd) ^ 2) := by
  have hZ1 : (1 : ℝ) ≤ MM * (1 + dd) := by nlinarith
  have hY : MM * (1 + dd) ≤ 1 + 2 * u + 5 * dd / 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hMu (by linarith : (0 : ℝ) ≤ 1 + dd),
      mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 1 / 3 - u)]
  have hZsq : (MM * (1 + dd)) ^ 2 ≤ 1 + 8 * u + 6 * dd := by
    nlinarith [hY, hZ1, hu0, hd0, hu, hd]
  have hid : 2 * MM ^ 2 * (1 + dd) ^ 2 = 2 * (MM * (1 + dd)) ^ 2 := by ring
  rw [hid]
  exact cq_of_Z hZ1 hZsq hu0 hd0

end KappaCq

section Cen

variable {n : ℕ}

/-- **`driftCen ≤ κ((1+ε)·K·c²·dim + (1+1/ε)(c₃η)²)`** — `TruncSumMean.integral_sum_sqTrunc_le`
on the truncated sum, the `(1+1/ε)` piece kept as it stands.  This is the companion of
`TruncSumMean.driftCen_ge`, in the direction `hbudget` needs. -/
theorem driftCen_le (hn : 3 ≤ n) {c κ ε c₃ η : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (K : ℕ) :
    DriftChargeTotal.driftCen (n := n) c η c₃ κ ε K
      ≤ κ * ((1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)))
          + (1 + 1 / ε) * (c₃ * η) ^ 2) := by
  have hG := TruncSumMean.integral_sum_sqTrunc_le (n := n) hn (c := c) (cap := η ^ 2)
    (by positivity) K
  have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left hG h1
  rw [DriftChargeTotal.driftCen]
  exact mul_le_mul_of_nonneg_left (by linarith) hκ

end Cen

section HS

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {P : Measure Ω} [IsProbabilityMeasure P]

/-- On `goodCut … K` the stopping time exceeds `K`, so it exceeds every `k ≤ K`. -/
theorem measureReal_compl_lt_tau_le_cut {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K k : ℕ} (hKN : K < N) (hk : k ≤ K)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ pbad := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _)) hbad
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
  intro hg
  have := GoodPathBounds.lt_tau_of_goodCut hg hKN
  omega

theorem sum_compl_lt_tau_le_cut {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hKN : K < N)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ (K : ℝ) * pbad := by
  calc ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ _k ∈ Finset.range K, pbad :=
        Finset.sum_le_sum fun k hk =>
          measureReal_compl_lt_tau_le_cut hKN (by have := Finset.mem_range.1 hk; omega) hbad
    _ = (K : ℝ) * pbad := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`hS` at the cut index.**  `GoodPathBounds.hS_of_intWeight` with the `{k < τ}` total
collapsed against `goodCut … K` — the event whose count the tail side does supply. -/
theorem hS_of_intWeight_cut {r thr η r₀ c₃ hstep Θ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hstep0 : 0 < hstep) (hKN : K < N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ y ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep K y ≤ Θ)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((K : ℝ) * pbad)
      ≤ ∑ k ∈ Finset.range K, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  have hbase := GoodPathBounds.hS_of_intWeight (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (N := N) (m := K) hstep0 hξ hτ hlight
  have hsum := sum_compl_lt_tau_le_cut (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (r := r) (thr := thr) (Wacc := Wacc) hKN hbad
  have hdim : (0 : ℝ) ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hdim
  linarith

/-- **The `goodCut` failure is `failTotal`** — `goodPathCut`'s own union bound, extracted. -/
theorem goodCut_fail_le (hn : 3 ≤ n) {c₃ pcnt : ℝ} {K : ℕ}
    {q' : ι → EuclideanSpace ℝ (UT n)} {W' : Finset ι} {A₀' : EuclideanSpace ℝ (UT n)}
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (StateInvariant4.countGood q' W' A₀' (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) K c₃)ᶜ
      ≤ pcnt) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (GoodPathBounds.goodCut 1 (ChainSetup.coord 0)
          (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted n)) (6 * 1 * 1 * Real.sqrt (n : ℝ))
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n)
          q' W' A₀' (DriftStopped6.r0Adopted n) c₃ K)ᶜ
      ≤ GoodPathBounds.failTotal n pcnt := by
  refine le_trans (GoodPathBounds.measureReal_compl_goodCut_le _ _ _ _ _ _ _ _) ?_
  rw [GoodPathBounds.failTotal]
  have h1 := GoodPathBounds.chainGood_failure (n := n) hn (r := 1) one_pos
  have h2 := GoodPathBounds.accGood_failure (q := q') (W := W') (A₀ := A₀') hn
  linarith

end HS

section Lb

variable {n : ℕ}

/-- `N·X = T·dim·(1 − 50/n)` at the adopted parameters — `TruncSumMean.driftCen_ge_adopted`'s own
identity, extracted so a shorter horizon can use it. -/
theorem numSteps_mul_step_eq (hn : 3 ≤ n) :
    ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2
            / DriftStopped6.etaAdopted n ^ 2)
      = ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := TailSideSetup2.stepSizeAdopted2_pos hn
  have hD : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    have hpos : 0 < Fintype.card (UT n) := by
      rw [ChainWiring.card_UT]
      have hge : 12 ≤ n * (n + 1) := by nlinarith [hn]
      omega
    exact_mod_cast hpos
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) = (Fintype.card (UT n) : ℝ) := by
    rw [finrank_euclideanSpace]
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
  rw [TruncSumMean.cAdopted_sq hn, hfr, TruncSumMean.etaAdopted_sq hn]
  field_simp
  nlinarith [hNh, hh0, hD, hn0]

/-- One step of the drift is at most `1`: `c²·dim = h·card ≤ n²/n⁹`. -/
theorem step_mul_dim_le_one (hn : 2073600 ≤ n) :
    D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) = (Fintype.card (UT n) : ℝ) := by
    rw [finrank_euclideanSpace]
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hh := ParamsAdopted2.stepSizeAdopted2_le hn3
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n := ParamsAdopted2.stepSizeAdopted2_nonneg hn3
  rw [TruncSumMean.cAdopted_sq hn3, hfr]
  have hmul : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
      ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 := by
    apply mul_le_mul hh hd hd0 (by positivity)
  have hfin : (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [hnR, hn0, pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : 2 ≤ 9)]
  linarith

/-- **`log n/n ≤ 1/200`** — sharper than `AdoptedConstants95.log_ratio_le`, and what the
short-horizon `hLb` needs: `log n ≤ 4q` and `n = q⁴` give `log n/n ≤ 4/q³ ≤ 4/50 653`. -/
theorem log_div_le (hn : 2073600 ≤ n) : Real.log n / (n : ℝ) ≤ 1 / 200 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set qq := Real.sqrt (Real.sqrt (n : ℝ)) with hqdef
  have hq37 : (37 : ℝ) ≤ qq := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < qq := by linarith
  have hq4 : qq ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn0.le
  have hlog : Real.log n ≤ 4 * qq := WindowR.log_le_four_qrt hn
  have hcube : 800 * qq ≤ qq ^ 4 := by
    have hq3 : (37 : ℝ) ^ 3 ≤ qq ^ 3 := pow_le_pow_left₀ (by norm_num) hq37 3
    have h4 : qq ^ 4 = qq ^ 3 * qq := by ring
    rw [h4]
    nlinarith [hq3, hq0]
  rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 200)]
  linarith [hlog, hcube, hq4]

theorem driftCen_ge_cut (hn : 2073600 ≤ n) {κ ε c₃ : ℝ} {K : ℕ}
    (hκ : 1 / 2 ≤ κ) (hκ0 : 0 ≤ κ) (hε : 0 < ε)
    (hK : K + 1 = ParamsAdopted2.numStepsAdopted2 n) :
    4 * Real.log n - 200 * (Real.log n / (n : ℝ)) - 1 / 2
      ≤ DriftChargeTotal.driftCen (n := n) (D5.S3.Arith.Lattices.Klartag.cAdopted n)
          (DriftStopped6.etaAdopted n) c₃ κ ε K := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
  have hD : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    have hpos : 0 < Fintype.card (UT n) := by
      rw [ChainWiring.card_UT]
      have hge : 12 ≤ n * (n + 1) := by nlinarith [hn3]
      omega
    exact_mod_cast hpos
  have hcap : (0 : ℝ) < DriftStopped6.etaAdopted n ^ 2 := by
    rw [TruncSumMean.etaAdopted_sq hn3]
    have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n :=
      TailSideSetup2.stepSizeAdopted2_pos hn3
    positivity
  have hbase := TruncSumMean.driftCen_ge (n := n) (c := D5.S3.Arith.Lattices.Klartag.cAdopted n)
    (cap := DriftStopped6.etaAdopted n ^ 2) (κ := κ) (ε := ε) (c₃ := c₃)
    (η := DriftStopped6.etaAdopted n) hcap hκ0 hε K rfl
  have hNX := numSteps_mul_step_eq (n := n) hn3
  have hKR : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) = (K : ℝ) + 1 := by
    rw [← hK]; push_cast; ring
  have hone := step_mul_dim_le_one (n := n) hn
  have hTd := TruncSumMean.horizon_mul_card_ge (n := n) hn3
  have hsmall := log_div_le (n := n) hn
  have hloss : (0 : ℝ) ≤ 1 - 50 / (n : ℝ) := by
    have : 50 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
    linarith
  set XX := D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - 100 * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2
        / DriftStopped6.etaAdopted n ^ 2 with hXX
  have hXle : XX ≤ 1 := by
    rw [hXX]
    have : (0 : ℝ) ≤ 100 * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2) ^ 2
        * ((Fintype.card (UT n) : ℝ)) ^ 2 / DriftStopped6.etaAdopted n ^ 2 := by positivity
    linarith
  have hAA : ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) - 1
      ≤ (K : ℝ) * XX := by
    rw [← hNX, hKR]
    nlinarith [hXle]
  have hid : 8 * Real.log n * (1 - 50 / (n : ℝ))
      = 8 * Real.log n - 400 * (Real.log n / (n : ℝ)) := by field_simp; ring
  have hAge : 8 * Real.log n - 400 * (Real.log n / (n : ℝ))
      ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) := by
    have h1 : 8 * Real.log n * (1 - 50 / (n : ℝ))
        ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hTd hloss
    linarith [hid.le, hid.ge]
  have hpos : (0 : ℝ) ≤ (K : ℝ) * XX := by linarith
  have hke : (1 : ℝ) / 2 ≤ κ * (1 + ε) := by nlinarith [hκ, hε]
  have hkap : (K : ℝ) * XX / 2 ≤ κ * ((1 + ε) * ((K : ℝ) * XX)) := by
    nlinarith [hke, hpos]
  linarith

/-- **`hLb` with the drift horizon one step short of `N`** — the two `4·log n` cancel. -/
theorem hLb_of_bounds_cut (hn : 2073600 ≤ n) {κ ε c₃ C' s' t : ℝ} {K : ℕ}
    (hκ : 1 / 2 ≤ κ) (hκ0 : 0 ≤ κ) (hε : 0 < ε) (hs' : 0 ≤ s') (ht : 0 ≤ t)
    (hK : K + 1 = ParamsAdopted2.numStepsAdopted2 n) (hC : 5 ≤ C') :
    ChainWiring.logDet (A0C n)
        - (DriftChargeTotal.driftCen (n := n) (D5.S3.Arith.Lattices.Klartag.cAdopted n)
            (DriftStopped6.etaAdopted n) c₃ κ ε K + s') - t
      < C' - 4 * Real.log n := by
  have hcen := driftCen_ge_cut (n := n) (c₃ := c₃) hn hκ hκ0 hε hK
  have hA0 := AdoptedConstants95.logDet_A0C_le (n := n) (by omega)
  have hsmall := log_div_le (n := n) hn
  linarith

end Lb

section Thresholds

variable {n : ℕ}

theorem C3_eq_terminal_formB (hn : 2 ≤ n) {α B0 : ℝ} :
    TailAtStepR5W2.C3 n 1 (B0 / (n : ℝ) ^ 2) α
      = ((4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2)
        * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hne : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
  rw [TailAtStepR5W2.C3, Lemma43R.C1R]
  field_simp

/-- **The combined threshold is `n`-free** at `B m = B₀/n²`. -/
theorem thetaTight_combB_le {p : ℕ} {α B0 : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hB0 : 0 ≤ B0)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = Section5.kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (TailAtStepR5W2.C3 n 1 (B0 / (n : ℝ) ^ 2) α)
      ≤ 3308 * (32 * Real.exp 2 + 4 * B0) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have height : (0 : ℝ) < 8 - 8 / (n : ℝ) ^ 2 := Lemma43R.eight_sub_pos (by omega)
  have hex0 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hb0 : (0 : ℝ) ≤ (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2 := by
    have hnum : (0 : ℝ) ≤ 4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0 := by nlinarith
    positivity
  rw [C3_eq_terminal_formB (by omega)]
  refine le_trans (TerminalRatio2.theta_tight_terminal_bound (p := p) hn hα hb0 hdef halpha
    hp hpn hppos) ?_
  have hid : 4 * ((4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2) * 827
        * (n : ℝ) ^ 2
      = 3308 * (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) := by
    field_simp; ring
  rw [hid]
  have hle8 : 8 - 8 / (n : ℝ) ^ 2 ≤ 8 := by
    have : (0 : ℝ) ≤ 8 / (n : ℝ) ^ 2 := by positivity
    linarith
  nlinarith [hex0, hle8]

/-- **The count ratio, with the `q³` kept.**  `c₃'' = n²·q³`, so a terminal weight `θT ≤ Kc·n²`
gives a Markov ratio `2·Kc/q³` — the `q³` is what makes `log n · pcnt` bounded. -/
theorem count_ratio_q {θT Kc : ℝ} (hn : 2073600 ≤ n) (_hKc : 0 ≤ Kc)
    (hθ : θT ≤ Kc * (n : ℝ) ^ 2) :
    (2 * θT + 0) / DriftStopped6c.c3Adopted'' n
      ≤ 2 * Kc / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hq3 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by positivity
  rw [DriftStopped6c.c3Adopted'', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hθ hq3.le]

/-- **`T·dim ≤ 16·log n`** — the companion of `TruncSumMean.horizon_mul_card_ge`. -/
theorem horizon_mul_card_le (hn : 2073600 ≤ n) :
    ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) ≤ 16 * Real.log n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three (by omega)
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  rw [ChainDrift.horizon]
  have hstep : 16 * Real.log n / (n : ℝ) ^ 2 * (Fintype.card (UT n) : ℝ)
      ≤ 16 * Real.log n / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have hid : 16 * Real.log n / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = 16 * Real.log n := by
    field_simp
  linarith [hid.le, hid.ge]

theorem const_le_inv (hn : 2073600 ≤ n) :
    173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20) ≤ 1 / (1000 * (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hid : 173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20) = 173 * 20 ^ 20 / (n : ℝ) ^ 10 := by
    field_simp
  rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
  have hbig : ((1000000 : ℝ)) ^ 9 ≤ (n : ℝ) ^ 9 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 9
  have hpow : (n : ℝ) ^ 10 = (n : ℝ) ^ 9 * (n : ℝ) := by ring
  have hval : (173 : ℝ) * 20 ^ 20 * 1000 ≤ (1000000 : ℝ) ^ 9 := by norm_num
  rw [hpow]
  nlinarith [hbig, hn0, hval]

/-- **`failTotal n pcnt ≤ pcnt + 1/(1000·n)`.** -/
theorem failTotal_le_inv (hn : 2073600 ≤ n) (pcnt : ℝ) :
    GoodPathBounds.failTotal n pcnt ≤ pcnt + 1 / (1000 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hE0 : (0 : ℝ) ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
  have hEb : Real.exp (-(n : ℝ)) ≤ 20 ^ 20 / (n : ℝ) ^ 20 := ExpDecay99.exp_neg_nat_le hn1
  have hpoly := FailTotalBound99.poly_le hn1
  have hstep1 : ((33 * (n : ℝ) ^ 9 * Real.log n + 4)
        + 8 * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ)) :=
    mul_le_mul_of_nonneg_right hpoly hE0
  have hstep2 : (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * (20 ^ 20 / (n : ℝ) ^ 20) :=
    mul_le_mul_of_nonneg_left hEb (by positivity)
  have hstep3 := const_le_inv hn
  rw [GoodPathBounds.failTotal]
  simp only [one_pow, one_mul]
  linarith

/-- **The threshold at `B₀ = 140`, as a number**: `3308·(32e² + 560) ≤ 2.64·10⁶`. -/
theorem thetaTight_le_2800000 {p : ℕ} {α : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = Section5.kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (TailAtStepR5W2.C3 n 1 (140 / (n : ℝ) ^ 2) α) ≤ 2800000 := by
  have h := thetaTight_combB_le (n := n) (p := p) (α := α) (B0 := 140) hn hα (by norm_num)
    hdef halpha hp hpn hppos
  have hex : Real.exp 2 ≤ 7.4 := ThetaIntegrated99.exp_two_le
  linarith

end Thresholds

section NumArith

theorem num_le_const {kap eps cq G Th pbad Ea CB sp tt ss qv xx cen : ℝ}
    (hqv : 37 ≤ qv) (heps : eps = 1 / qv)
    (hcen : cen ≤ kap * ((1 + eps) * G + (1 + 1 / eps) * xx))
    (hgap : kap * (1 + eps) - cq ≤ 200 / qv)
    (hG0 : 0 ≤ G) (hG : G ≤ 64 * qv)
    (_hkap0 : 0 ≤ kap) (hkap : kap ≤ 5)
    (hx0 : 0 ≤ xx) (hx : xx ≤ 4 / qv ^ 2)
    (_hcq0 : 0 ≤ cq) (hcqh : cq ≤ 1 / 2)
    (hTh0 : 0 ≤ Th) (hTh : Th ≤ 2800000)
    (hpbad0 : 0 ≤ pbad) (hpb : qv * pbad ≤ 16)
    (hEa : Ea ≤ 1) (hCB : CB ≤ 1) (hsp : sp ≤ 1) (htt : tt ≤ 1) (hss : ss ≤ 20) :
    cen - cq * G + cq * Th + cq * G * pbad + Ea + CB + sp + tt + ss ≤ 1450000 := by
  have hqv0 : (0 : ℝ) < qv := by linarith
  have hring : kap * ((1 + eps) * G + (1 + 1 / eps) * xx) - cq * G
      = (kap * (1 + eps) - cq) * G + kap * (1 + 1 / eps) * xx := by ring
  have hA : cen - cq * G ≤ (kap * (1 + eps) - cq) * G + kap * (1 + 1 / eps) * xx := by
    rw [← hring]; linarith
  have h2 : (kap * (1 + eps) - cq) * G ≤ 200 / qv * G := mul_le_mul_of_nonneg_right hgap hG0
  have h3 : 200 / qv * G ≤ 200 / qv * (64 * qv) := mul_le_mul_of_nonneg_left hG (by positivity)
  have h4 : 200 / qv * (64 * qv) = 12800 := by field_simp; ring
  have heinv : 1 / eps = qv := by rw [heps]; field_simp
  have h5 : kap * (1 + 1 / eps) * xx ≤ 2 := by
    rw [heinv]
    have hq1 : (0 : ℝ) ≤ 1 + qv := by linarith
    have hs1 : kap * (1 + qv) ≤ 5 * (1 + qv) := by nlinarith
    have hs2 : kap * (1 + qv) * xx ≤ 5 * (1 + qv) * xx := mul_le_mul_of_nonneg_right hs1 hx0
    have hs3 : 5 * (1 + qv) * xx ≤ 5 * (1 + qv) * (4 / qv ^ 2) :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    have hs4 : 5 * (1 + qv) * (4 / qv ^ 2) ≤ 2 := by
      rw [show (5 : ℝ) * (1 + qv) * (4 / qv ^ 2) = 20 * (1 + qv) / qv ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      nlinarith [hqv, hqv0]
    linarith
  have h7 : cq * Th ≤ 1400000 := by
    nlinarith [mul_le_mul hcqh hTh hTh0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h8 : cq * G * pbad ≤ 512 := by
    have hb1 : cq * G ≤ 1 / 2 * (64 * qv) := mul_le_mul hcqh hG hG0 (by norm_num)
    have hb2 : cq * G * pbad ≤ 1 / 2 * (64 * qv) * pbad :=
      mul_le_mul_of_nonneg_right hb1 hpbad0
    nlinarith [hb2, hpb]
  linarith [h4.le, h4.ge]

/-- The shortfall total at `t' = s' = 1`, with both variance terms below `1`. -/
theorem shortfall_le_twenty {v w kp : ℝ} (_hv0 : 0 ≤ v) (hv : v ≤ 1) (_hw0 : 0 ≤ w)
    (hw : w ≤ 1) (hkp0 : 0 ≤ kp) (hkp : kp ≤ 6) :
    v / (4 * 1) + 1 + (2 * kp ^ 2 * w + 2 * v) / (4 * 1) ≤ 20 := by
  have hk2 : kp ^ 2 ≤ 36 := by nlinarith
  have hkw : kp ^ 2 * w ≤ 36 := by nlinarith [sq_nonneg kp]
  linarith

/-- `q ≤ q⁴` for `q ≥ 37`. -/
theorem qrt_le_self {qv nn : ℝ} (h37 : 37 ≤ qv) (h4 : qv ^ 4 = nn) : qv ≤ nn := by
  have h3 : (1 : ℝ) ≤ qv ^ 3 := one_le_pow₀ (by linarith)
  nlinarith [h3, h37, h4.le, h4.ge]

/-- `η/m ≤ 2/q` from `η ≤ 1/q` and `m ≥ 1/2`. -/
theorem delta_le_two_div {et mm qv : ℝ} (hq0 : 0 < qv) (het : et ≤ 1 / qv) (hmm : 1 / 2 ≤ mm) :
    et / mm ≤ 2 / qv := by
  have h1 : et * qv ≤ 1 / qv * qv := mul_le_mul_of_nonneg_right het hq0.le
  have h2 : 1 / qv * qv = 1 := by field_simp
  rw [div_le_div_iff₀ (by linarith) hq0]
  linarith [h1, h2.le, h2.ge]

/-- `2·rr = 4η + 4c₃η ≤ 12/q`. -/
theorem rr_le_twelve {c3 et qv : ℝ} (hq0 : 0 < qv) (het : et ≤ 1 / qv)
    (hce : c3 * et ≤ 2 / qv) : 2 * (2 * (1 + c3) * et) ≤ 12 / qv := by
  have hqne : qv ≠ 0 := ne_of_gt hq0
  have hexp : 2 * (2 * (1 + c3) * et) = 4 * et + 4 * (c3 * et) := by ring
  have h4 : (12 : ℝ) / qv = 4 * (1 / qv) + 4 * (2 / qv) := by field_simp; ring
  rw [hexp, h4]
  linarith

/-- `(1+c₃)η ≤ rr·m` at `rr = 2(1+c₃)η` and `m ≥ 1/2`. -/
theorem rm_ge {c3 et mm : ℝ} (hnn : 0 ≤ (1 + c3) * et) (hmm : 1 / 2 ≤ mm) :
    (1 + c3) * et ≤ 2 * (1 + c3) * et * mm := by
  nlinarith [mul_nonneg hnn (by linarith : (0 : ℝ) ≤ 2 * mm - 1)]

/-- `20000/q² ≤ 15` at `q ≥ 37`. -/
theorem twenty_k_div_sq_le {qv : ℝ} (h37 : 37 ≤ qv) : 20000 / qv ^ 2 ≤ 15 := by
  have hq0 : (0 : ℝ) < qv := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h37, hq0]

/-- **The gap, as bare arithmetic**: `κ(1+ε) − cq ≤ 183·(1/q) ≤ 200·(1/q)`. -/
theorem gap_le {kap cq u rr dd eps iq : ℝ} (hiq : 0 ≤ iq)
    (hkapup : kap ≤ 1 / 2 + 12 * u + 2 * rr) (hcqlow : 1 / 2 - 4 * u - 3 * dd ≤ cq)
    (hu : u ≤ 10 * iq) (hrr : 2 * rr ≤ 12 * iq) (hdd : dd ≤ 2 * iq)
    (hkeps : kap * eps ≤ 5 * iq) : kap * (1 + eps) - cq ≤ 200 * iq := by
  have hexp : kap * (1 + eps) = kap + kap * eps := by ring
  rw [hexp]
  linarith

/-- **The numerator identity.**  `S = K·dim − Θ/h − dim·(K·pbad)` and
`L = logDet A₀ − (driftCen + 1) − 1`, so `driftRHS_acc − L + 20` is the term list
`num_le_const` bounds. -/
theorem rhs_identity {ld cq h dim KK Th pb Ea CB cen : ℝ} (hh : h ≠ 0) :
    ld - cq * h * (KK * dim - Th / h - dim * (KK * pb)) + (Ea + CB)
        - (ld - (cen + 1) - 1) + 20
      = cen - cq * (KK * (h * dim)) + cq * Th + cq * (KK * (h * dim)) * pb
        + Ea + CB + 1 + 1 + 20 := by
  field_simp
  ring

/-- `κ(1+ε) ≤ 6` at `κ ≤ 5`, `ε ≤ 1/5`. -/
theorem kp_le_six {kap eps : ℝ} (hkap0 : 0 ≤ kap) (hkap : kap ≤ 5) (_heps0 : 0 ≤ eps)
    (heps : eps ≤ 1 / 5) : kap * (1 + eps) ≤ 6 := by nlinarith

/-- `20000/q³ ≤ 0.396` at `q ≥ 37` (measured `0.394 8`; the ceiling is chosen above it). -/
theorem twenty_k_div_cube_le {qv : ℝ} (h37 : 37 ≤ qv) : 2 * 10000 / qv ^ 3 ≤ 396 / 1000 := by
  have hq0 : (0 : ℝ) < qv := by linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have hq3 : (37 : ℝ) ^ 3 ≤ qv ^ 3 := pow_le_pow_left₀ (by norm_num) h37 3
  nlinarith [hq3]

end NumArith

section VW

variable {n : ℕ}

/-- `K·c²·(n/m²) ≤ 1`: `K·h ≤ T = 16 log n/n²`, `n/m² ≤ 4n`, and `log n/n ≤ 1/200`. -/
theorem vterm_le (hn : 2073600 ≤ n) {K : ℕ} {mm : ℝ}
    (hK : (K : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) (hmm : 1 / 2 ≤ mm) :
    (K : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 * ((n : ℝ) / mm ^ 2)) ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n :=
    (TailSideSetup2.stepSizeAdopted2_pos hn3).le
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
  have hKh : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n := by
    rw [← hNh]; nlinarith [hK, hh0]
  have hm0 : (0 : ℝ) < mm := by linarith
  have hmsq : (1 : ℝ) / 4 ≤ mm ^ 2 := by nlinarith [hmm]
  have hratio : (n : ℝ) / mm ^ 2 ≤ 4 * (n : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hmsq, hn0, mul_nonneg (by linarith : (0 : ℝ) ≤ mm ^ 2 - 1 / 4) hn0.le]
  have hrat0 : (0 : ℝ) ≤ (n : ℝ) / mm ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := by
    rw [ChainDrift.horizon]
    have : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
    positivity
  have hassoc : (K : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted n ^ 2 * ((n : ℝ) / mm ^ 2))
      = ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) * ((n : ℝ) / mm ^ 2) := by
    rw [TruncSumMean.cAdopted_sq hn3]; ring
  rw [hassoc]
  have hstep : ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) * ((n : ℝ) / mm ^ 2)
      ≤ ChainDrift.horizon n * (4 * (n : ℝ)) :=
    mul_le_mul hKh hratio hrat0 hT0
  have hfin : ChainDrift.horizon n * (4 * (n : ℝ)) = 64 * (Real.log n / (n : ℝ)) := by
    rw [ChainDrift.horizon]; field_simp; ring
  have hsmall := log_div_le (n := n) hn
  linarith [hfin.le, hfin.ge]

/-- `K·(η²/2)² ≤ 1`: `η²/2 = h·card·n`, `h ≤ n⁻⁹`, `card ≤ n²`, and `K·h ≤ 16 log n/n²`. -/
theorem wterm_le (hn : 2073600 ≤ n) {K : ℕ}
    (hK : (K : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) :
    (K : ℝ) * (DriftStopped6.etaAdopted n ^ 2 / 2) ^ 2 ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n :=
    (TailSideSetup2.stepSizeAdopted2_pos hn3).le
  have hh := ParamsAdopted2.stepSizeAdopted2_le hn3
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
  have hKh : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n := by
    rw [← hNh]; nlinarith [hK, hh0]
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := by
    rw [ChainDrift.horizon]
    have : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
    positivity
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hn0; linarith
  have hid : (K : ℝ) * (DriftStopped6.etaAdopted n ^ 2 / 2) ^ 2
      = ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        * (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
    rw [TruncSumMean.etaAdopted_sq hn3]; ring
  rw [hid]
  have hrest : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2
      ≤ (1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2 := by
    have hc2 : (Fintype.card (UT n) : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 := by nlinarith [hd, hd0]
    have h1 : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2
        ≤ (1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 :=
      mul_le_mul hh hc2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hrest0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n
      * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hprod : ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        * (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2)
      ≤ ChainDrift.horizon n * ((1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2) :=
    mul_le_mul hKh hrest hrest0 hT0
  have hval : ChainDrift.horizon n * ((1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2)
      = 16 * Real.log n / (n : ℝ) ^ 5 := by
    rw [ChainDrift.horizon]; field_simp
  have hlast : 16 * Real.log n / (n : ℝ) ^ 5 ≤ 1 := by
    have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h24 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ (n : ℝ) by linarith) 4
      norm_num at h24
      linarith
    have hpow : (n : ℝ) ^ 5 = (n : ℝ) ^ 4 * (n : ℝ) := by ring
    rw [div_le_one (by positivity), hpow]
    nlinarith [hlogn, hn0, mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 4 - 16) hn0.le]
  linarith [hval.le, hval.ge]

end VW

end D5.S3.Arith.Lattices.Klartag.Completion.Packing
