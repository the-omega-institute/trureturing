/- GID: D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualEndpointPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional actual endpoint phase and canonical defect amplitude. -/

import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
import D5.S1.Deficit.ZeckendorfDisplacementReading

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 3000

namespace D5.S1.Recurrence.Invariants.CloitreActualEndpointPhase

open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S0.Conventions

local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

/-- Nonnegative canonical golden defect on positive indices under Hyp21_1. -/
noncomputable def canonicalDefect (n : ℕ) : ℕ := C n - G n

/-- The right-width canonical defect, distinct from a right-profile deficit. -/
noncomputable def widthDefect (t : ℕ) : ℕ := t - G t

/-- All points visited from the actual prescribed-depth selector. -/
def selectedOrbit (N : ℕ) : Set ℕ := Set.range (fun i : ℕ => (T N)^[i] (g N))

/-- Oscillation of canonical defect on the selector and its successor.
The endpoint and zero-width conclusions identify this pair with the complete selected orbit. -/
noncomputable def selectedPairAmplitude (N : ℕ) : ℕ :=
  max (canonicalDefect (g N)) (canonicalDefect (T N (g N))) -
    min (canonicalDefect (g N)) (canonicalDefect (T N (g N)))

/-- First collar entry, least preperiod, absolute phase, actual depth, complete cycle,
and canonical oscillation for a positive right width. -/
def EndpointPhase (t k : ℕ) : Prop :=
  let N := F k + t
  let A := F (k - 1)
  ∃ μ : ℕ,
    X N μ ∈ I k t ∧
    (∀ i : ℕ, i < μ → X N i ∉ I k t) ∧
    μ % 2 = 0 ∧ X N μ = A + t ∧
    X N μ ∈ Function.periodicPts (T N) ∧
    (∀ i : ℕ, i < μ → X N i ∉ Function.periodicPts (T N)) ∧
    μ ≤ d N ∧
    (∀ i : ℕ, μ ≤ i → X N i = if i % 2 = 0 then A + t else A) ∧
    d N = A + t - 1 ∧
    g N = (if (A + t - 1) % 2 = 0 then A + t else A) ∧
    Function.minimalPeriod (T N) (g N) = 2 ∧
    selectedOrbit N = {A, A + t} ∧
    canonicalDefect A = 0 ∧ canonicalDefect (A + t) = widthDefect t ∧
    selectedPairAmplitude N = widthDefect t

/-- Zero offset reaches and selects the Fibonacci fixed point, with full singleton
selected orbit, shortest preperiod, period one and zero canonical oscillation. -/
def ZeroPhase (k : ℕ) : Prop :=
  let N := F k
  let A := F (k - 1)
  ∃ μ : ℕ,
    X N μ = A ∧
    (∀ i : ℕ, i < μ → X N i ≠ A) ∧
    X N μ ∈ Function.periodicPts (T N) ∧
    (∀ i : ℕ, i < μ → X N i ∉ Function.periodicPts (T N)) ∧
    μ ≤ d N ∧ (∀ i : ℕ, μ ≤ i → X N i = A) ∧
    g N = A ∧ Function.minimalPeriod (T N) (g N) = 1 ∧
    selectedOrbit N = {A} ∧ canonicalDefect A = 0 ∧ selectedPairAmplitude N = 0

set_option maxHeartbeats 1600000 in
-- Exterior-orbit induction and the canonical readout share arithmetic side conditions.
/-- Complete conditional actual endpoint theorem: every admissible positive width,
uniform divergence over arbitrary admissible orders, and the separate zero offset. -/
theorem full22_1 (U : ℕ → ℕ) (h : Hyp21_1 U) :
    (∀ t k : ℕ, 1 ≤ t → 12 * t + 7 ≤ k → EndpointPhase t k) ∧
    widthDefect 1 = 0 ∧
    (∀ t : ℕ, 2 ≤ t → 0 < widthDefect t) ∧
    (∀ M t k : ℕ, 3 * M + 2 ≤ t → 12 * t + 7 ≤ k →
      M < selectedPairAmplitude (F k + t) ∧
      Function.minimalPeriod (T (F k + t)) (g (F k + t)) = 2) ∧
    (∀ k : ℕ, 6 ≤ k → ZeroPhase k) := by
  let α : ℝ := Real.goldenRatio⁻¹
  have ha0 : 0 < α := inv_pos.mpr Real.goldenRatio_pos
  have ha1 : α < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have haPhi : α = Real.goldenRatio - 1 := by
    dsimp [α]
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have haSq : α ^ 2 + α = 1 := by
    rw [haPhi]
    nlinarith [Real.goldenRatio_sq]
  have haHalf : (1 : ℝ) < 2 * α := by nlinarith
  have haThird : α < (2 : ℝ) / 3 := by nlinarith
  have goldenMono : Monotone G := by
    intro a b hab
    unfold D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.add_le_add_right hab 1
    · exact ha0.le
  have goldenLe : ∀ n : ℕ, G n ≤ n := by
    intro n
    have hf := Nat.floor_le (show 0 ≤ ((n : ℝ) + 1) * α by positivity)
    have hx : ((n : ℝ) + 1) * α < (n : ℝ) + 1 := by nlinarith
    have hn : (G n : ℝ) < (n : ℝ) + 1 := lt_of_le_of_lt hf hx
    have hn' : G n < n + 1 := by exact_mod_cast hn
    omega
  have domainInv : ∀ N : ℕ, 3 ≤ N → Set.MapsTo (T N) (D N) (D N) := by
    intro N hN x hx
    have hb := h.bounds x hx.1
    change 1 ≤ x ∧ x ≤ N - 1 at hx
    change 1 ≤ N - C x ∧ N - C x ≤ N - 1
    omega
  have orbitDomain : ∀ N i : ℕ, 3 ≤ N → X N i ∈ D N := by
    intro N i hN
    exact (domainInv N hN).iterate i ⟨by omega, le_rfl⟩
  have shiftRead : ∀ n : ℕ, displacementDecode n = n + G n := by
    intro n
    have hr := displacement_decode_eq_beatty_floor n
    have he : ((n : ℝ) + 1) * Real.goldenRatio =
        ((n : ℝ) + 1) * α + (n + 1 : ℕ) := by
      rw [haPhi]
      push_cast
      ring
    rw [he, Int.floor_add_natCast,
      ← Int.natCast_floor_eq_floor (show 0 ≤ ((n : ℝ) + 1) * α by positivity)] at hr
    change (displacementDecode n : ℤ) = (G n : ℤ) + (n + 1 : ℕ) - 1 at hr
    exact_mod_cast (show (displacementDecode n : ℤ) = (n : ℤ) + (G n : ℤ) by omega)
  have positive : ∀ t k : ℕ, 1 ≤ t → 12 * t + 7 ≤ k → EndpointPhase t k := by
    intro t k ht hk
    let A := F (k - 1)
    let B := F (k - 2)
    let N := F k + t
    have hA : 1 ≤ A := by have := Nat.le_fib_add_one (k - 1); dsimp [A]; omega
    have hB : 2 * t + 1 < B := by
      have := Nat.le_fib_add_one (k - 2)
      dsimp [B]
      omega
    have fAB : F k = A + B := by
      have hf := Nat.fib_add_two (n := k - 2)
      rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at hf
      dsimp [A, B]
      omega
    have nEq : N = A + B + t := by dsimp [N]; omega
    have hN : 3 ≤ N := by omega
    have profile : ∀ v : ℕ, v ≤ 2 * t → C (A + v) = B + v := by
      intro v hv
      have hp := full21_3 U h v (k - 1) (by omega)
      simpa only [Nat.sub_sub] using hp
    have reflect : ∀ u : ℕ, u ≤ t → T N (A + u) = A + t - u := by
      intro u hu
      have hp := profile u (by omega)
      unfold T
      rw [hp]
      omega
    have lowerMap : T N A = A + t := by simpa using reflect 0 (by omega)
    have upperMap : T N (A + t) = A := by have := reflect t le_rfl; omega
    have collarPeriodic : ∀ x : ℕ, x ∈ I k t → x ∈ Function.periodicPts (T N) := by
      intro x hx
      change A ≤ x ∧ x ≤ A + t at hx
      have ex : x = A + (x - A) := by omega
      have hp : Function.IsPeriodicPt (T N) 2 x := by
        change T N (T N x) = x
        rw [ex, reflect (x - A) (by omega)]
        have e2 : A + t - (x - A) = A + (t - (x - A)) := by omega
        rw [e2, reflect (t - (x - A)) (by omega)]
        omega
      exact ⟨2, by omega, hp⟩
    have leftMap : ∀ x : ℕ, x ∈ D N → x < A → A + t ≤ T N x := by
      intro x hx hxa
      have hb := (h.bounds x hx.1).2.2.1
      have hu := h.uMono x A hx.1 (by omega)
      have ha := (h.anchors (k - 1) (by omega)).1
      change U A = B at ha
      unfold T
      omega
    have farFloor : B + t + 1 ≤ G (A + 2 * t + 1) := by
      have ha := (h.plusOne (k - 1) (by omega)).1
      change G (A + 1) = B + 1 at ha
      have hf := Nat.floor_le (show 0 ≤ ((A + 1 : ℕ) + 1 : ℝ) * α by positivity)
      change (G (A + 1) : ℝ) ≤ ((A + 1 : ℕ) + 1 : ℝ) * α at hf
      rw [ha] at hf
      have hreal : (B + t + 1 : ℕ) ≤ ((A + 2 * t + 1 : ℕ) + 1 : ℝ) * α := by
        push_cast at hf ⊢
        nlinarith [show (0 : ℝ) ≤ t by positivity]
      exact (Nat.le_floor_iff (by positivity)).mpr hreal
    have rightMap : ∀ x : ℕ, x ∈ D N → A + t < x → T N x < A := by
      intro x hx hxa
      have hc : B + t + 1 ≤ C x := by
        by_cases hnear : x ≤ A + 2 * t
        · have ex : x = A + (x - A) := by omega
          have hp := profile (x - A) (by omega)
          rw [← ex] at hp
          omega
        · have hm := goldenMono (show A + 2 * t + 1 ≤ x by omega)
          have hb := (h.bounds x hx.1).2.1
          omega
      unfold T
      omega
    obtain ⟨μ, hpμ, hbefore, hμd⟩ := h.depthEntry N hN
    have hμI : X N μ ∈ I k t :=
      h.cyclesInside k t (X N μ) (by omega) (orbitDomain N μ hN) hpμ
    have beforeI : ∀ i : ℕ, i < μ → X N i ∉ I k t := by
      intro i hi hx
      exact hbefore i hi (collarPeriodic _ hx)
    have hμpos : 0 < μ := by
      by_contra hn
      have e : μ = 0 := by omega
      rw [e] at hμI
      change A ≤ N - 1 ∧ N - 1 ≤ A + t at hμI
      omega
    have exterior : ∀ i : ℕ, i < μ →
        (i % 2 = 0 ∧ A + t < X N i) ∨ (i % 2 = 1 ∧ X N i < A) := by
      intro i
      induction i with
      | zero =>
        intro hi
        left
        change 0 % 2 = 0 ∧ A + t < N - 1
        omega
      | succ i ih =>
        intro hi
        have prev := ih (by omega)
        have hx := orbitDomain N i hN
        have step : X N (i + 1) = T N (X N i) :=
          Function.iterate_succ_apply' (T N) i (N - 1)
        have hn := beforeI (i + 1) hi
        change ¬(A ≤ X N (i + 1) ∧ X N (i + 1) ≤ A + t) at hn
        rcases prev with ⟨he, hr⟩ | ⟨ho, hl⟩
        · have hm := rightMap _ hx hr
          right
          rw [step]
          constructor <;> omega
        · have hm := leftMap _ hx hl
          left
          rw [step] at hn ⊢
          constructor <;> omega
    have μstep : X N μ = T N (X N (μ - 1)) := by
      have := Function.iterate_succ_apply' (T N) (μ - 1) (N - 1)
      change X N (μ - 1 + 1) = T N (X N (μ - 1)) at this
      simpa only [show μ - 1 + 1 = μ by omega] using this
    have μphase : μ % 2 = 0 ∧ X N μ = A + t := by
      have prev := exterior (μ - 1) (by omega)
      have hx := orbitDomain N (μ - 1) hN
      change A ≤ X N μ ∧ X N μ ≤ A + t at hμI
      rcases prev with ⟨he, hr⟩ | ⟨ho, hl⟩
      · have hm := rightMap _ hx hr
        rw [← μstep] at hm
        omega
      · have hm := leftMap _ hx hl
        rw [← μstep] at hm
        constructor <;> omega
    have tail : ∀ j : ℕ, X N (μ + j) = if (μ + j) % 2 = 0 then A + t else A := by
      intro j
      induction j with
      | zero => simpa [μphase.1] using μphase.2
      | succ j ih =>
        have step : X N (μ + (j + 1)) = T N (X N (μ + j)) := by
          simpa only [X, Nat.succ_eq_add_one, Nat.add_assoc] using
            Function.iterate_succ_apply' (T N) (μ + j) (N - 1)
        rw [step, ih]
        by_cases he : (μ + j) % 2 = 0
        · rw [if_pos he, upperMap, if_neg (by omega)]
        · rw [if_neg he, lowerMap, if_pos (by omega)]
    have phase : ∀ i : ℕ, μ ≤ i → X N i = if i % 2 = 0 then A + t else A := by
      intro i hi
      have hh := tail (i - μ)
      simpa only [show μ + (i - μ) = i by omega] using hh
    have depthValue : d N = A + t - 1 := by
      have hh := full21_3 U h (t - 1) k (by omega)
      have he : N - 1 = F k + (t - 1) := by dsimp [N]; omega
      unfold d
      rw [he, hh]
      omega
    have selected : g N = if (A + t - 1) % 2 = 0 then A + t else A := by
      have hh := phase (d N) hμd
      change g N = _ at hh
      rwa [depthValue] at hh
    have perLower : Function.IsPeriodicPt (T N) 2 A := by
      change T N (T N A) = A
      rw [lowerMap, upperMap]
    have perUpper : Function.IsPeriodicPt (T N) 2 (A + t) := by
      change T N (T N (A + t)) = A + t
      rw [upperMap, lowerMap]
    have minPeriod : Function.minimalPeriod (T N) (g N) = 2 := by
      rw [selected]
      split
      · apply Function.minimalPeriod_eq_prime perUpper
        change ¬ T N (A + t) = A + t
        rw [upperMap]
        omega
      · apply Function.minimalPeriod_eq_prime perLower
        change ¬ T N A = A
        rw [lowerMap]
        omega
    have allLower : ∀ i : ℕ, (T N)^[i] A = if i % 2 = 0 then A else A + t := by
      intro i
      rw [← perLower.iterate_mod_apply i]
      by_cases hi : i % 2 = 0
      · simp [hi]
      · have hi' : i % 2 = 1 := by omega
        simp [hi', lowerMap]
    have allUpper : ∀ i : ℕ, (T N)^[i] (A + t) = if i % 2 = 0 then A + t else A := by
      intro i
      rw [← perUpper.iterate_mod_apply i]
      by_cases hi : i % 2 = 0
      · simp [hi]
      · have hi' : i % 2 = 1 := by omega
        simp [hi', upperMap]
    have support : selectedOrbit N = {A, A + t} := by
      ext x
      change (∃ i : ℕ, (T N)^[i] (g N) = x) ↔ x = A ∨ x = A + t
      rw [selected]
      split
      · constructor
        · rintro ⟨i, rfl⟩
          rw [allUpper]
          split <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, by simpa using upperMap⟩
          · exact ⟨0, rfl⟩
      · constructor
        · rintro ⟨i, rfl⟩
          rw [allLower]
          split <;> simp
        · rintro (rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, by simpa using lowerMap⟩
    have seam : G (A + t) = B + G t := by
      have hgt : Nat.greatestFib (A + t) = k - 1 := by
        apply Nat.le_antisymm
        · have hx : A + t < F k := by omega
          have hlt := Nat.greatestFib_lt.mpr hx
          omega
        · exact Nat.le_greatestFib.mpr (by dsimp [A]; omega)
      have he : displacementDecode (A + t) = F k + displacementDecode t := by
        unfold displacementDecode wdigits
        rw [Nat.zeckendorf_of_pos (by omega : 0 < A + t), hgt]
        simp only [show A + t - F (k - 1) = t by dsimp [A]; omega,
          List.map_cons, List.sum_cons, show k - 1 + 1 = k by omega]
      rw [shiftRead (A + t), shiftRead t] at he
      omega
    have defectLower : canonicalDefect A = 0 := by
      have ha := h.anchors (k - 1) (by omega)
      change U A = B ∧ C A = B ∧ G A = B at ha
      simp [canonicalDefect, ha.2.1, ha.2.2]
    have defectUpper : canonicalDefect (A + t) = widthDefect t := by
      rw [canonicalDefect, profile t (by omega), seam]
      unfold widthDefect
      omega
    have amplitude : selectedPairAmplitude N = widthDefect t := by
      unfold selectedPairAmplitude
      rw [selected]
      split
      · rw [upperMap, defectLower, defectUpper]
        simp
      · rw [lowerMap, defectLower, defectUpper]
        simp
    change EndpointPhase t k
    exact ⟨μ, hμI, beforeI, μphase.1, μphase.2, hpμ, hbefore, hμd,
      phase, depthValue, selected, minPeriod, support, defectLower, defectUpper, amplitude⟩
  have widthOne : widthDefect 1 = 0 := by
    have ha := (h.anchors 2 (by omega)).2.2
    norm_num [Nat.fib] at ha
    simp [widthDefect, ha]
  have widthPositive : ∀ t : ℕ, 2 ≤ t → 0 < widthDefect t := by
    intro t ht
    have hf := Nat.floor_le (show 0 ≤ ((t : ℝ) + 1) * α by positivity)
    change (G t : ℝ) ≤ ((t : ℝ) + 1) * α at hf
    have hr : ((t : ℝ) + 1) * α < t := by
      have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    have hlt : G t < t := by exact_mod_cast (lt_of_le_of_lt hf hr)
    unfold widthDefect
    omega
  have uniform : ∀ M t k : ℕ, 3 * M + 2 ≤ t → 12 * t + 7 ≤ k →
      M < selectedPairAmplitude (F k + t) ∧
      Function.minimalPeriod (T (F k + t)) (g (F k + t)) = 2 := by
    intro M t k hMt hk
    obtain ⟨μ, _, _, _, _, _, _, _, _, _, _, hp, _, _, _, ham⟩ :=
      positive t k (by omega) hk
    rw [ham]
    refine ⟨?_, hp⟩
    have hf := Nat.floor_le (show 0 ≤ ((t : ℝ) + 1) * α by positivity)
    change (G t : ℝ) ≤ ((t : ℝ) + 1) * α at hf
    have hMt' : (3 : ℝ) * M + 2 ≤ t := by exact_mod_cast hMt
    have hr : (G t : ℝ) + M < t := by
      nlinarith [show (0 : ℝ) ≤ M by positivity]
    have hn : G t + M < t := by exact_mod_cast hr
    unfold widthDefect
    omega
  have zero : ∀ k : ℕ, 6 ≤ k → ZeroPhase k := by
    intro k hk
    let A := F (k - 1)
    let B := F (k - 2)
    let N := F k
    have hA : 1 ≤ A := by have := Nat.le_fib_add_one (k - 1); dsimp [A]; omega
    have hB : 1 ≤ B := by have := Nat.le_fib_add_one (k - 2); dsimp [B]; omega
    have fAB : N = A + B := by
      have hf := Nat.fib_add_two (n := k - 2)
      rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at hf
      dsimp [N, A, B]
      omega
    have hN : 3 ≤ N := by have := Nat.le_fib_add_one k; dsimp [N]; omega
    have anchors := h.anchors (k - 1) (by omega)
    change U A = B ∧ C A = B ∧ G A = B at anchors
    have fixed : Function.IsFixedPt (T N) A := by
      change N - C A = A
      rw [anchors.2.1]
      omega
    obtain ⟨μ, hp, hbefore, hμd⟩ := h.depthEntry N hN
    have hc := h.cyclesInside k 0 (X N μ) hk
      (by simpa [N] using orbitDomain N μ hN) (by simpa [N] using hp)
    have hentry : X N μ = A := by
      change A ≤ X N μ ∧ X N μ ≤ A + 0 at hc
      omega
    have beforeA : ∀ i : ℕ, i < μ → X N i ≠ A := by
      intro i hi he
      apply hbefore i hi
      rw [he]
      exact ⟨1, by omega, fixed⟩
    have phase : ∀ i : ℕ, μ ≤ i → X N i = A := by
      intro i hi
      have he : X N i = (T N)^[i - μ] (X N μ) := by
        unfold X
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rw [he, hentry]
      exact fixed.iterate (i - μ)
    have selected : g N = A := phase (d N) hμd
    have minPeriod : Function.minimalPeriod (T N) (g N) = 1 := by
      rw [selected]
      exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr fixed
    have support : selectedOrbit N = {A} := by
      ext x
      change (∃ i : ℕ, (T N)^[i] (g N) = x) ↔ x = A
      rw [selected]
      constructor
      · rintro ⟨i, rfl⟩
        exact fixed.iterate i
      · rintro rfl
        exact ⟨0, rfl⟩
    have defect : canonicalDefect A = 0 := by
      simp [canonicalDefect, anchors.2.1, anchors.2.2]
    have amplitude : selectedPairAmplitude N = 0 := by
      simp [selectedPairAmplitude, selected, fixed.eq, defect]
    exact ⟨μ, hentry, beforeA, hp, hbefore, hμd, phase, selected,
      minPeriod, support, defect, amplitude⟩
  exact ⟨positive, widthOne, widthPositive, uniform, zero⟩

end D5.S1.Recurrence.Invariants.CloitreActualEndpointPhase
