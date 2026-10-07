/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailWiring
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailWiring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailHypsWindow
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4

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

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailWiring

open MeasureTheory
open Set
open Real
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2
open D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4

noncomputable section

variable {p m : ℕ} {α R A B : ℝ} {g : Fin (m + 1) → ZMod p}

/-- Abbreviation for the chain the drift side runs: the reach-2 window, the chain's own `q` and
`A₀`, and the adopted Gaussian step. -/
abbrev Wg (α : ℝ) (p m : ℕ) (g : Fin (m + 1) → ZMod p) : Finset (Fin (m + 1) → ℤ) :=
  windowOfR2 α p m g

theorem hsteps_win
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))) (hn : 3 ≤ m + 1)
    (hα : 0 < α) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → ∀ y ∈ Wg α p m g,
      (gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          {ω | y ∈ contactSet (qC α) (Wg α p m g) (A0C (m + 1))
            (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) k ω}
        ≤ 4 * profStepRW2 α (m + 1) (ParamsAdopted2.stepSizeAdopted2 (m + 1)) y k :=
  hsteps_of_walkRW2 (TailHypsWindow.hq_j_win hα hn) (TailHypsWindow.hA₀_win hα hn)
    (TailHypsWindow.hwin_win hα hn) (TailHypsWindow.hr_win hα hn)
    (TailHypsWindow.hy_win hα hn) (TailHypsWindow.hprop_win hraw hnd hn)

/-- `intWeight` is monotone in the step count. -/
theorem intWeight_mono_steps {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Cset : ℕ → Ω → Finset ι} {hstep : ℝ} (hstep0 : 0 ≤ hstep)
    {K N : ℕ} (hKN : K ≤ N) (y : ι) :
    ContactIntegrated.intWeight P Cset hstep K y
      ≤ ContactIntegrated.intWeight P Cset hstep N y :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKN)
    (fun _k _ _ => mul_nonneg hstep0 measureReal_nonneg)

/-- **The integrated bound on `windowOfR2`, pointwise and real.**  `intWeight_leRW2` at the window,
then `intWeight_mono_steps` down to any `K ≤ N`. -/
theorem intWeight_le_prof_win {K : ℕ}
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))) (hn : 3 ≤ m + 1)
    (hα : 0 < α) (hKN : K ≤ ParamsAdopted2.numStepsAdopted2 (m + 1)) :
    ∀ y ∈ Wg α p m g, ContactIntegrated.intWeight
        (gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (fun k ω => (Chain.chain (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) k ω).2)
        (ParamsAdopted2.stepSizeAdopted2 (m + 1)) K y
      ≤ 4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon (m + 1)),
          profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1) t ‖toE (m + 1) y‖ := by
  intro y hy
  refine le_trans (intWeight_mono_steps (adopted_stepSize_pos hn).le hKN y) ?_
  exact intWeight_leRW2 hα (adopted_stepSize_pos hn) (adopted_horizon hn)
    (contactSet (qC α) (Wg α p m g) (A0C (m + 1)) (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))))
    (fun k hk => hsteps_win hraw hnd hn hα k hk y hy)

/-- **The terminal bound on `windowOfR2`, in the exact `htail` shape** — `2·weight + 0` with
`weight y = 2·profileAt … (horizon (m+1)) ‖toE (m+1) y‖`, at **every** `K < N`. -/
theorem htail_win {K : ℕ}
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))) (hn : 3 ≤ m + 1)
    (hα : 0 < α) (hK : K < ParamsAdopted2.numStepsAdopted2 (m + 1)) :
    ∀ y ∈ Wg α p m g, (gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        {ω | y ∈ (Chain.chain (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) K ω).2}
      ≤ 2 * (2 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
          (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖) + 0 := by
  intro y hy
  have hstep := hsteps_win hraw hnd hn hα K hK y hy
  have hKle : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1)
      ≤ ChainDrift.horizon (m + 1) := by
    have heq := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
    have hh0 : 0 ≤ ParamsAdopted2.stepSizeAdopted2 (m + 1) := (adopted_stepSize_pos hn).le
    have hle : (K : ℝ) ≤ (ParamsAdopted2.numStepsAdopted2 (m + 1) : ℝ) := by
      have : K ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by omega
      exact_mod_cast this
    nlinarith [heq, hle, hh0]
  have hbump := profStep_le_horizon (α := α) hn (K := K) y hKle
  have hc : (gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
      {ω | y ∈ contactSet (qC α) (Wg α p m g) (A0C (m + 1))
        (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) K ω}
      = (gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        {ω | y ∈ (Chain.chain (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) K ω).2} := rfl
  rw [hc] at hstep
  linarith

theorem θ3_pos {p m : ℕ} [Fact (Nat.Prime p)] (hm1 : 2073600 ≤ m + 1) (hα : 0 < α)
    (hA : 0 < A) (hB : 0 ≤ B) : 0 < ThetaTight.thetaTight p (m + 1) (C3 (m + 1) A B α) := by
  have hC := C3_pos hm1 hα hA hB
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
  have hpn : (1 : ℝ) < (p : ℝ) ^ (m + 1) := one_lt_pow₀ hpR (by omega)
  have hκ : 0 < kappa (m + 1) := kappa_pos (by omega)
  have hnR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < m + 1 := by omega
    exact_mod_cast this
  rw [ThetaTight.thetaTight]
  exact div_pos (by positivity) (by linarith)

theorem θ3_ne_zero {p m : ℕ} [Fact (Nat.Prime p)] (hm1 : 2073600 ≤ m + 1) (hα : 0 < α)
    (hA : 0 < A) (hB : 0 ≤ B) : θ3 A B p m α ≠ 0 := by
  have h := θ3_pos (p := p) (m := m) (α := α) (A := A) (B := B) hm1 hα hA hB
  rw [θ3]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact h

theorem θ3_ne_top {p m : ℕ} : θ3 A B p m α ≠ ⊤ := by
  rw [θ3]; exact ENNReal.ofReal_ne_top

/-- A sum of `ENNReal.ofReal`s below `ENNReal.ofReal Θ` is a real strict inequality. -/
theorem sum_lt_of_sum_ofReal {ι : Type*} {S : Finset ι} {v : ι → ℝ} {Θ : ℝ}
    (hv : ∀ y, 0 ≤ v y) (hΘ : 0 < Θ)
    (h : ∑ y ∈ S, ENNReal.ofReal (v y) < ENNReal.ofReal Θ) : ∑ y ∈ S, v y < Θ := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hv y)] at h
  exact (ENNReal.ofReal_lt_ofReal_iff hΘ).1 h

open Classical in
/-- **The two sums, from one light-contact hypothesis at the combined `profileAt` family.**
The first is `FinalDischarge2.hS_of_intWeight_wired`'s `hlight`; the second is
`TerminalCount.countGood_of_terminal_weight`'s `hθ`, at the weight `htail_win` supplies. -/
theorem sums_at_windowOfR2 {p m : ℕ} [NeZero p] [Fact (Nat.Prime p)] {Θ ΘT : ℝ} {K : ℕ}
    (hm : Threshold2.n₁ ≤ m) (hα : 0 < α) (hA : 0 < A) (hB : 0 ≤ B)
    (g : Fin (m + 1) → ZMod p)
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hKN : K ≤ ParamsAdopted2.numStepsAdopted2 (m + 1)) (hΘ : 0 < Θ) (hΘT : 0 < ΘT)
    (h₁ : θ3 A B p m α ≤ ENNReal.ofReal A * ENNReal.ofReal Θ)
    (h₂ : θ3 A B p m α ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * ΘT))
    (hlight : Theorem2.LightContact (wComb A B p m α) (shellR α (m + 1)) (θ3 A B p m α) g) :
    (∑ y ∈ Wg α p m g, ContactIntegrated.intWeight
        (gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (fun k ω => (Chain.chain (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) k ω).2)
        (ParamsAdopted2.stepSizeAdopted2 (m + 1)) K y < Θ) ∧
      (∑ y ∈ Wg α p m g, 2 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
          (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖ ≤ ΘT) := by
  have hm1 : 2073600 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hn : 3 ≤ m + 1 := by omega
  have hsum : ∑ y ∈ Wg α p m g,
      (ENNReal.ofReal A * wProf α (m + 1) y + ENNReal.ofReal B * wProfT α (m + 1) y)
        < θ3 A B p m α := by
    have hl := hlight
    simp only [Theorem2.LightContact, wComb] at hl
    rwa [filter_eq_windowOfR2] at hl
  obtain ⟨hI, hT⟩ := sums_split (θ₁ := ENNReal.ofReal Θ) (θ₂ := ENNReal.ofReal (2 * ΘT))
    (θ3_ne_zero hm1 hα hA hB) θ3_ne_top hsum h₁ h₂
  constructor
  · have hreal : ∑ y ∈ Wg α p m g,
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon (m + 1)),
          profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1) t ‖toE (m + 1) y‖) < Θ :=
      sum_lt_of_sum_ofReal
        (fun y => by
          have : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon (m + 1)),
              profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1) t ‖toE (m + 1) y‖ :=
            setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t _)
          linarith)
        hΘ hI
    refine lt_of_le_of_lt (Finset.sum_le_sum ?_) hreal
    exact intWeight_le_prof_win hraw hnd hn hα hKN
  · have hreal : ∑ y ∈ Wg α p m g,
        (4 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
          (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖) < 2 * ΘT :=
      sum_lt_of_sum_ofReal
        (fun y => by
          have : (0 : ℝ) ≤ profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
              (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖ := profile_nonneg _ _
          linarith)
        (by linarith) hT
    have hhalf : ∑ y ∈ Wg α p m g, 2 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
        (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖
        = (∑ y ∈ Wg α p m g, 4 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
            (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hhalf]
    linarith

/-- **`hS`'s hypothesis, in `FinalDischarge2.hS_of_intWeight_wired`'s exact shape** (`≤`). -/
theorem hS_light_win {p m : ℕ} [NeZero p] [Fact (Nat.Prime p)] {Θ ΘT : ℝ} {K : ℕ}
    (hm : Threshold2.n₁ ≤ m) (hα : 0 < α) (hA : 0 < A) (hB : 0 ≤ B)
    (g : Fin (m + 1) → ZMod p)
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hKN : K ≤ ParamsAdopted2.numStepsAdopted2 (m + 1)) (hΘ : 0 < Θ) (hΘT : 0 < ΘT)
    (h₁ : θ3 A B p m α ≤ ENNReal.ofReal A * ENNReal.ofReal Θ)
    (h₂ : θ3 A B p m α ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * ΘT))
    (hlight : Theorem2.LightContact (wComb A B p m α) (shellR α (m + 1)) (θ3 A B p m α) g) :
    ∑ y ∈ Wg α p m g, ContactIntegrated.intWeight
        (gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (fun k ω => (Chain.chain (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) k ω).2)
        (ParamsAdopted2.stepSizeAdopted2 (m + 1)) K y ≤ Θ :=
  le_of_lt (sums_at_windowOfR2 hm hα hA hB g hraw hnd hKN hΘ hΘT h₁ h₂ hlight).1

/-- **`hcnt`, finished** — `TerminalCount.countGood_of_terminal_weight` at `htail_win` and the
second sum.  Holds at **every** `K < N`, so the count index is the caller's choice. -/
theorem hcnt_win {p m : ℕ} [NeZero p] [Fact (Nat.Prime p)] {Θ ΘT c₃ : ℝ} {K : ℕ}
    (hm : Threshold2.n₁ ≤ m) (hα : 0 < α) (hA : 0 < A) (hB : 0 ≤ B)
    (g : Fin (m + 1) → ZMod p)
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hK : K < ParamsAdopted2.numStepsAdopted2 (m + 1)) (hc₃ : 0 < c₃)
    (hΘ : 0 < Θ) (hΘT : 0 < ΘT)
    (h₁ : θ3 A B p m α ≤ ENNReal.ofReal A * ENNReal.ofReal Θ)
    (h₂ : θ3 A B p m α ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * ΘT))
    (hlight : Theorem2.LightContact (wComb A B p m α) (shellR α (m + 1)) (θ3 A B p m α) g) :
    (gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        (StateInvariant4.countGood (qC α) (Wg α p m g) (A0C (m + 1))
          (step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))) K c₃)ᶜ ≤ (2 * ΘT + 0) / c₃ := by
  have hn : 3 ≤ m + 1 := by
    have hm1 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact TerminalCount.countGood_of_terminal_weight
    (fun k => measurable_step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1)) k) hc₃
    (fun y => 2 * profileAt (a0C (m + 1)) α (windowR2 α (m + 1)) (m + 1)
      (ChainDrift.horizon (m + 1)) ‖toE (m + 1) y‖)
    (htail_win hraw hnd hn hα hK)
    (sums_at_windowOfR2 hm hα hA hB g hraw hnd hK.le hΘ hΘT h₁ h₂ hlight).2

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailWiring
