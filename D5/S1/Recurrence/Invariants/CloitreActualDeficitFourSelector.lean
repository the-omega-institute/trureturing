/- GID: D5/S1/Recurrence/Invariants/CloitreActualDeficitFourSelector
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualDeficitFourSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional actual deficit-four selection, legal profiles and first-hit period. -/

import D5.S1.Recurrence.Invariants.CloitreActualWeightedCone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.CloitreActualDeficitFourSelector
open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
open D5.S1.Recurrence.Invariants.CloitreActualWeightedCone
local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
-- Simultaneous actual orbit induction and divided quadratic budgets need these elaboration bounds.
/-- Exact conditional actual selector, including both lower natural blocks,
the signed jump, the quadratic budget, and the first deficit-four hit.
The qualification and the finite full-block seeds remain premises. -/
theorem full30_3 (U : ℕ → ℕ) (h24 : Hyp24_1 U)
    (seed20 : ∀ v : ℕ, v ≤ F 18 →
      (heightDeficit 20 v ≤ 2 ↔ v ≤ 35) ∧
      (35 < v → 3 ≤ heightDeficit 20 v ∧
        heightDeficit 20 v ≤ max 3 (v - 36)))
    (seed21 : ∀ v : ℕ, v ≤ F 19 →
      (heightDeficit 21 v ≤ 3 ↔ v ≤ 45) ∧
      (45 < v → 4 ≤ heightDeficit 21 v ∧
        heightDeficit 21 v ≤ max 4 (v - 46))) :
    ∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → heightDeficit m b = 4 →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      let P := ((m - 2) ^ 2 / 3 + 30) - 3 * m
      let Ω := fun r : ℕ => b - heightDeficit (m - 1) r
      let r₀ := b - 4
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      heightDeficit (m - 1) z = 4 ∧ heightDeficit (m - 2) w = 0 ∧
      w ≤ platformWidth (m - 2) ∧
      ((g N : ℤ) - (T N (g N) : ℤ)) = (w : ℤ) - 4 ∧
      b ≤ 4 * P ∧ 4 * P ≤ F (m - 4) ∧
      (∀ r : ℕ, r ≤ b →
        r ≤ F (m - 3) ∧ r ≤ F (m - 4) ∧
        1 ≤ F (m - 1) - r ∧ F (m - 1) - r ≤ N - 1 ∧
        heightDeficit (m - 1) r ≤ (2 * r) / 3 ∧ (2 * r) / 3 ≤ b ∧
        Ω r ≤ b ∧ T N (F (m - 1) - r) = F (m - 1) - Ω r) ∧
      ∃ τ : ℕ, τ ≤ b ∧ heightDeficit (m - 1) (Ω^[τ] r₀) = 4 ∧
        (∀ i : ℕ, i < τ → heightDeficit (m - 1) (Ω^[i] r₀) ≠ 4) ∧
        z = Ω^[τ] r₀ ∧ g N = F (m - 1) - Ω^[τ] r₀ ∧
        Function.minimalPeriod (T N) (g N) = τ + 1 ∧
        (∀ r : ℕ, r ≤ b → r ∈ Function.periodicPts Ω →
          heightDeficit (m - 1) r = 4 → r = Ω^[τ] r₀) := by
  classical
  let h := h24.toHyp21_1
  obtain ⟨orbitDomain, recurrence⟩ := actual_foundations
  obtain ⟨profiles, _, routes, _⟩ := full24_3 U h24
  have fibStep : ∀ m : ℕ, 2 ≤ m → F m = F (m - 1) + F (m - 2) := by
    intro m hm
    have hf := Nat.fib_add_two (n := m - 2)
    rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hf
    omega
  have cap : ∀ m t : ℕ, 8 ≤ m → t ≤ F (m - 2) → C (F m - t) ≤ F (m - 1) := by
    intro m t hm ht
    exact (profiles m t hm ht).1
  have width : ∀ m : ℕ, 20 ≤ m → 10 ≤ platformWidth m := by
    intro m hm
    unfold platformWidth
    omega
  have slack : ∀ m q : ℕ, 20 ≤ m → q ≤ F (m - 2) →
      heightDeficit m q ≤ q - 8 := by
    intro m q hm hq
    have hp := width m hm
    have rr := (profiles m q (by omega) hq).2
    by_cases hz : q ≤ platformWidth m
    · have he := rr.1.mpr hz; omega
    · have he := (rr.2 (by omega)).2
      have hh : max 1 (q - platformWidth m - 1) ≤ q - 8 := by
        apply max_le <;> omega
      omega
  have selected : ∀ N : ℕ, 3 ≤ N → g N ∈ Function.periodicPts (T N) := by
    intro N hN
    obtain ⟨μ, ⟨r, hr, hp⟩, _, hμ⟩ := h.depthEntry N hN
    refine ⟨r, hr, ?_⟩
    have hs := hp.apply_iterate (d N - μ)
    have he : (T N)^[d N - μ] (X N μ) = g N := by
      unfold X g
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rwa [he] at hs
  have inv : ∀ N : ℕ, 3 ≤ N → Set.MapsTo (T N) (D N) (D N) := by
    intro N hN x hx
    have hb := h.bounds x hx.1
    change 1 ≤ x ∧ x ≤ N - 1 at hx
    change 1 ≤ N - C x ∧ N - C x ≤ N - 1
    omega
  have pred : ∀ N x : ℕ, 3 ≤ N → x ∈ D N → x ∈ Function.periodicPts (T N) →
      ∃ y : ℕ, y ∈ D N ∧ y ∈ Function.periodicPts (T N) ∧ T N y = x := by
    intro N x hN hx ⟨r, hr, hp⟩
    refine ⟨(T N)^[r - 1] x, (inv N hN).iterate (r - 1) hx,
      ⟨r, hr, hp.apply_iterate (r - 1)⟩, ?_⟩
    rw [← Function.iterate_succ_apply' (T N) (r - 1) x, show (r - 1).succ = r by omega]
    exact hp.eq
  have coord : ∀ j b x : ℕ, 9 ≤ j → b ≤ F (j - 1) →
      x ∈ D (F (j + 1) - b) → x ∈ Function.periodicPts (T (F (j + 1) - b)) →
      let z := F j - x
      z ≤ b ∧ z ≤ F (j - 2) ∧ b - z ≤ F (j - 3) ∧
      x = F j - z ∧ F (j + 1) - b - x = F (j - 1) - (b - z) := by
    intro j b x hj hb hx hp
    have hi := h24.intersection j b x (by omega) hb hx hp
    have hl1 := le_of_max_le_left hi.1
    have hl2 := le_of_max_le_right hi.1
    have hu1 := le_trans hi.2 (min_le_left _ _)
    have hu2 := le_trans hi.2 (min_le_right _ _)
    have ff := fibStep (j + 1) (by omega)
    have fg := fibStep j (by omega)
    rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at ff
    dsimp only
    omega
  have map : ∀ j b z : ℕ, 9 ≤ j → b ≤ F (j - 1) → z ≤ F (j - 2) → z ≤ b →
      T (F (j + 1) - b) (F j - z) = F j - (b - heightDeficit j z) := by
    intro j b z hj hb hz hzb
    have hc := cap j z (by omega) hz
    have rr := (profiles j z (by omega) hz).2
    have wp : 2 ≤ platformWidth j := by unfold platformWidth; omega
    have he : heightDeficit j z ≤ z := by
      by_cases hh : z ≤ platformWidth j
      · have hh := rr.1.mpr hh; omega
      · have hh := (rr.2 (by omega)).2
        have mm : max 1 (z - platformWidth j - 1) ≤ z := by apply max_le <;> omega
        omega
    have ff := fibStep (j + 1) (by omega)
    have fg := fibStep j (by omega)
    rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at ff
    unfold T heightDeficit at *
    omega
  have split : ∀ j b : ℕ, 9 ≤ j → b ≤ F (j - 1) →
      let N := F (j + 1) - b
      let z := F j - g N
      let w := b - z
      heightDeficit (j + 1) b = heightDeficit j z + heightDeficit (j - 1) w := by
    intro j b hj hb
    let N := F (j + 1) - b
    have ff := fibStep (j + 1) (by omega)
    have fg := fibStep j (by omega)
    have hn : 3 ≤ N := by
      have hp := Nat.le_fib_add_one j
      dsimp [N]; rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at ff; omega
    have cc := coord j b (g N) hj hb (orbitDomain N (d N) hn) (selected N hn)
    have hs := recurrence N hn
    dsimp only at cc
    have hc1 := cap j (F j - g N) (by omega) cc.2.1
    have hc2 := cap (j - 1) (b - (F j - g N)) (by omega)
      (by simpa only [Nat.sub_sub] using cc.2.2.1)
    change C N = C (g N) + C (N - g N) at hs
    have e1 := congrArg C cc.2.2.2.1
    have e2 := congrArg C cc.2.2.2.2
    change C (N - g N) = _ at e2
    rw [e1, e2] at hs
    dsimp only
    unfold heightDeficit at *
    simp only [Nat.add_sub_cancel, Nat.sub_sub] at *
    change F j - C N = (F (j - 1) - C (F j - (F j - g N))) +
      (F (j - 2) - C (F (j - 1) - (b - (F j - g N))))
    simp only [Nat.reduceAdd] at hc2 fg
    omega
  let Z := fun k : ℕ => 3 * k + (k - 1) / 3 - 24
  let Row := fun k : ℕ =>
    (∀ v : ℕ, v ≤ F (k - 2) →
      (heightDeficit k v ≤ 3 ↔ v ≤ Z k) ∧
      (Z k < v → 4 ≤ heightDeficit k v ∧
        heightDeficit k v ≤ max 4 (v - Z k - 1))) ∧
    (∀ v : ℕ, Z k - 3 ≤ v → v ≤ Z k → heightDeficit k v = 3)
  have zNext : ∀ j : ℕ, 21 ≤ j → Z (j + 1) = Z j + 3 + if Even (F j) then 1 else 0 := by
    intro j hj
    have hd := D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 3 j (by omega)
    norm_num at hd
    have he : Even (F j) ↔ j % 3 = 0 := by
      rw [even_iff_two_dvd, hd, Nat.dvd_iff_mod_eq_zero]
    by_cases hp : Even (F j)
    · rw [if_pos hp]
      have hh := he.mp hp
      dsimp [Z]
      omega
    · rw [if_neg hp]
      have hh : j % 3 ≠ 0 := by intro heq; exact hp (he.mpr heq)
      dsimp [Z]
      omega
  have sizes : ∀ j : ℕ, 21 ≤ j → 45 ≤ Z j ∧ Z j + 5 < F (j - 2) := by
    intro j hj
    have grow : ∀ k : ℕ, 21 ≤ k → Z k + 6 ≤ F (k - 2) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        by_cases he : k = 21
        · subst k; norm_num [Z]
        have hk1 : 21 ≤ k - 1 := by omega
        have hp := ih (k - 1) (by omega) hk1
        have hn := zNext (k - 1) hk1
        rw [show k - 1 + 1 = k by omega] at hn
        have hf := fibStep (k - 2) (by omega)
        have hh : 4 ≤ F (k - 4) := by
          have hm := Nat.fib_mono (show 6 ≤ k - 4 by omega)
          norm_num at hm
          omega
        simp only [Nat.sub_sub, Nat.reduceAdd] at hp hf
        split at hn <;> omega
    constructor
    · dsimp [Z]; omega
    · have := grow j hj; omega
  have base : Row 21 := by
    constructor
    · intro v hv
      have rr := seed21 v hv
      norm_num only [Z, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at *
      simpa only [Nat.sub_sub, Nat.reduceAdd] using rr
    · intro v hlo hhi
      have vr : 42 ≤ v ∧ v ≤ 45 := by norm_num [Z] at hlo hhi; omega
      have hb : v ≤ F 19 := by norm_num; omega
      let N := F 21 - v
      have hn : 3 ≤ N := by dsimp [N]; norm_num; omega
      have cycleLow : ∀ x : ℕ, x ∈ D N → x ∈ Function.periodicPts (T N) →
          35 < F 20 - x := by
        intro x hx hp
        obtain ⟨y, hy, hyp, hyx⟩ := pred N x hn hx hp
        have cy := coord 20 v y (by omega) hb hy hyp
        have cx := coord 20 v x (by omega) hb hx hp
        dsimp only at cy cx
        have rr := seed20 (F 20 - y) cy.2.1
        have eb : heightDeficit 20 (F 20 - y) ≤ v - 36 := by
          by_cases hz : F 20 - y ≤ 35
          · have hh := rr.1.mpr hz; omega
          · have hh := (rr.2 (by omega)).2
            have mm : max 3 (F 20 - y - 36) ≤ v - 36 := by apply max_le <;> omega
            omega
        have my := map 20 v (F 20 - y) (by omega) hb cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        have ff : F 20 = 6765 := by norm_num
        omega
      have cc := coord 20 v (g N) (by omega) hb (orbitDomain N (d N) hn) (selected N hn)
      have low := cycleLow (g N) (orbitDomain N (d N) hn) (selected N hn)
      have e1 := (seed20 (F 20 - g N) cc.2.1).2 low |>.1
      have ss := split 20 v (by omega) hb
      have hi := (seed21 v hb).1.mpr vr.2
      change heightDeficit 21 v = heightDeficit 20 (F 20 - g N) +
        heightDeficit 19 (v - (F 20 - g N)) at ss
      omega
  have step : ∀ j : ℕ, 21 ≤ j → Row j →
      Row (j + 1) ∧ (∀ b : ℕ, b ≤ F (j - 1) → heightDeficit (j + 1) b = 4 →
        heightDeficit j (F j - g (F (j + 1) - b)) = 4) := by
    intro j hj row
    let A := F j
    let B := F (j - 1)
    let E := F (j - 2)
    let W := Z j
    have ff : F (j + 1) = A + B := by simpa [A, B] using fibStep (j + 1) (by omega)
    have fg : A = B + E := fibStep j (by omega)
    have eb : E ≤ B := Nat.fib_mono (by omega)
    have hh : 10 ≤ B := by have := Nat.le_fib_add_one (j - 1); dsimp [B]; omega
    have sz := sizes j hj
    have smallW : 45 ≤ W ∧ W + 5 < E := sz
    have zeroSmall : ∀ q : ℕ, q ≤ 4 → heightDeficit (j - 1) q = 0 := by
      intro q hq
      have hd : q ≤ F (j - 1 - 2) := by
        have hh := Nat.le_fib_add_one (j - 3)
        simp only [Nat.sub_sub, Nat.reduceAdd]; omega
      have hp := width (j - 1) (by omega)
      exact (profiles (j - 1) q (by omega) hd).2.1.mpr (by omega)
    have image : ∀ b x : ℕ, b ≤ B → x ∈ D (F (j + 1) - b) →
        x ∈ Function.periodicPts (T (F (j + 1) - b)) →
        ∃ r : ℕ, r ≤ b ∧ r ≤ E ∧ A - x = b - heightDeficit j r := by
      intro b x hb hx hp
      have hn : 3 ≤ F (j + 1) - b := by omega
      obtain ⟨y, hy, hyp, hyx⟩ := pred _ x hn hx hp
      have cy := coord j b y (by omega) hb hy hyp
      have cx := coord j b x (by omega) hb hx hp
      dsimp only at cy cx
      have my := map j b (A - y) (by omega) hb cy.2.1 cy.1
      rw [← cy.2.2.2.1, hyx] at my
      have ey := slack j (A - y) (by omega) cy.2.1
      refine ⟨A - y, cy.1, cy.2.1, ?_⟩
      change x = A - (b - heightDeficit j (A - y)) at my
      omega
    have tailCycles : ∀ b x : ℕ, b ≤ B → W + 5 ≤ b →
        x ∈ D (F (j + 1) - b) → x ∈ Function.periodicPts (T (F (j + 1) - b)) →
        W + 1 ≤ A - x ∧ A - x ≤ b - 4 := by
      intro b x hb hwb hx hp
      have lower : ∀ y : ℕ, y ∈ D (F (j + 1) - b) →
          y ∈ Function.periodicPts (T (F (j + 1) - b)) → W + 1 ≤ A - y := by
        intro y hy hyp
        obtain ⟨r, hrb, hre, hr⟩ := image b y hb hy hyp
        have er : heightDeficit j r ≤ b - W - 1 := by
          by_cases hrw : r ≤ W
          · have he := (row.1 r hre).1.mpr hrw; omega
          · have he := (row.1 r hre).2 (by omega) |>.2
            have hm : max 4 (r - Z j - 1) ≤ b - W - 1 := by
              apply max_le <;> omega
            omega
        omega
      have lx := lower x hx hp
      have hn : 3 ≤ F (j + 1) - b := by omega
      obtain ⟨y, hy, hyp, hyx⟩ := pred _ x hn hx hp
      have ly := lower y hy hyp
      have cy := coord j b y (by omega) hb hy hyp
      have cx := coord j b x (by omega) hb hx hp
      dsimp only at cy cx
      have ey := (row.1 (A - y) cy.2.1).2 (by omega) |>.1
      have eyb := slack j (A - y) (by omega) cy.2.1
      have my := map j b (A - y) (by omega) hb cy.2.1 cy.1
      rw [← cy.2.2.2.1, hyx] at my
      change x = A - (b - heightDeficit j (A - y)) at my
      exact ⟨lx, by omega⟩
    have tail : ∀ b : ℕ, b ≤ B → W + 5 ≤ b →
        4 ≤ heightDeficit (j + 1) b ∧
        heightDeficit (j + 1) b ≤ max 4 (b - W - 5) := by
      intro b hb hwb
      let N := F (j + 1) - b
      let z := A - g N
      let w := b - z
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cc := coord j b (g N) (by omega) hb (orbitDomain N (d N) hn) (selected N hn)
      have cb := tailCycles b (g N) hb hwb (orbitDomain N (d N) hn) (selected N hn)
      change z ≤ b ∧ z ≤ E ∧ w ≤ F (j - 3) ∧ _ at cc
      change W + 1 ≤ z ∧ z ≤ b - 4 at cb
      have zw : z + w = b := by dsimp [w]; omega
      have ss := split j b (by omega) hb
      change heightDeficit (j + 1) b = heightDeficit j z + heightDeficit (j - 1) w at ss
      have ez := (row.1 z cc.2.1).2 (by omega)
      have ew := slack (j - 1) w (by omega) (by simpa only [Nat.sub_sub] using cc.2.2.1)
      have w4 : 4 ≤ w := by omega
      have bound : heightDeficit (j + 1) b ≤ max 4 (b - W - 5) := by
        by_cases hz : W + 5 ≤ z
        · have mz : max 4 (z - Z j - 1) = z - W - 1 := by omega
          rw [mz] at ez
          have mm := le_max_right 4 (b - W - 5)
          omega
        · have mz : max 4 (z - Z j - 1) = 4 := by omega
          have ez4 : heightDeficit j z = 4 := by omega
          have mm1 := le_max_left 4 (b - W - 5)
          have mm2 := le_max_right 4 (b - W - 5)
          omega
      exact ⟨by omega, bound⟩
    have adjacent : heightDeficit (j + 1) (W + 5) = 4 := by
      have hv : W + 5 ≤ B := by omega
      have rr := tail (W + 5) hv le_rfl
      have mm : max 4 (W + 5 - W - 5) = 4 := by omega
      omega
    have low : ∀ b : ℕ, b ≤ W → heightDeficit (j + 1) b ≤ 3 := by
      intro b hb
      let N := F (j + 1) - b
      have hbB : b ≤ B := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cc := coord j b (g N) (by omega) hbB (orbitDomain N (d N) hn) (selected N hn)
      obtain ⟨r, hrb, hre, hr⟩ := image b (g N) hbB (orbitDomain N (d N) hn) (selected N hn)
      have er := (row.1 r hre).1.mpr (by omega)
      have ez := (row.1 (A - g N) cc.2.1).1.mpr (by omega)
      have ew := zeroSmall (b - (A - g N)) (by omega)
      have ss := split j b (by omega) hbB
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at ss
      omega
    have band : ∀ b : ℕ, W ≤ b → b ≤ W + 3 → heightDeficit (j + 1) b = 3 := by
      intro b hw hb
      let N := F (j + 1) - b
      have hbB : b ≤ B := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cycleBand : ∀ x : ℕ, x ∈ D N → x ∈ Function.periodicPts (T N) →
          W - 3 ≤ A - x ∧ A - x ≤ W := by
        intro x hx hp
        have lower : ∀ y : ℕ, y ∈ D N → y ∈ Function.periodicPts (T N) → W - 3 ≤ A - y := by
          intro y hy hyp
          obtain ⟨r, hrb, hre, hr⟩ := image b y hbB hy hyp
          by_cases he : b = W
          · have er := (row.1 r hre).1.mpr (by omega); omega
          · have er : heightDeficit j r ≤ 4 := by
              by_cases hrw : r ≤ W
              · have hh := (row.1 r hre).1.mpr hrw; omega
              · have hh := (row.1 r hre).2 (by omega) |>.2
                have mm : max 4 (r - Z j - 1) = 4 := by omega
                omega
            omega
        have lx := lower x hx hp
        have cx := coord j b x (by omega) hbB hx hp
        obtain ⟨y, hy, hyp, hyx⟩ := pred N x hn hx hp
        have ly := lower y hy hyp
        have cy := coord j b y (by omega) hbB hy hyp
        have er : 3 ≤ heightDeficit j (A - y) := by
          by_cases hrw : A - y ≤ W
          · have hh := row.2 (A - y) ly hrw; omega
          · have hh := (row.1 (A - y) cy.2.1).2 (by omega) |>.1; omega
        have eb := slack j (A - y) (by omega) cy.2.1
        have my := map j b (A - y) (by omega) hbB cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        change x = A - (b - heightDeficit j (A - y)) at my
        exact ⟨lx, by omega⟩
      have cb := cycleBand (g N) (orbitDomain N (d N) hn) (selected N hn)
      have ez := row.2 (A - g N) cb.1 cb.2
      obtain ⟨r, hrb, hre, hr⟩ := image b (g N) hbB (orbitDomain N (d N) hn) (selected N hn)
      have er := (row.1 r hre)
      have w4 : b - (A - g N) ≤ 4 := by
        by_cases hrw : r ≤ W
        · have hh := er.1.mpr hrw; omega
        · have hh := (er.2 (by omega)).2
          have mm : max 4 (r - Z j - 1) = 4 := by omega
          omega
      have ew := zeroSmall (b - (A - g N)) w4
      have ss := split j b (by omega) hbB
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at ss
      omega
    have critical : (heightDeficit (j + 1) (W + 4) = if Even A then 3 else 4) ∧
        g (F (j + 1) - (W + 4)) = if Even A then A - W else A - W - 1 := by
      let N := F (j + 1) - (W + 4)
      let L := A - W - 1
      have hb : W + 4 ≤ B := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have hL : 1 ≤ L := by dsimp [L]; omega
      have eLow : heightDeficit j (W + 1) = 4 := by
        have rr := (row.1 (W + 1) (by omega)).2 (by omega)
        have mm : max 4 (W + 1 - Z j - 1) = 4 := by omega
        omega
      have eHigh := row.2 W (by omega) le_rfl
      have lowEdge : T N L = L + 1 := by
        have mm := map j (W + 4) (W + 1) (by omega) hb (by omega) (by omega)
        rw [eLow] at mm
        change T N (A - (W + 1)) = A - (W + 4 - 4) at mm
        rw [show A - (W + 1) = L by dsimp [L]; omega] at mm
        rw [mm]
        dsimp only [L]; omega
      have highEdge : T N (L + 1) = L := by
        have mm := map j (W + 4) W (by omega) hb (by omega) (by omega)
        rw [eHigh] at mm
        have eq : A - W = L + 1 := by dsimp [L]; omega
        rw [eq] at mm
        dsimp [N, L] at *; omega
      have pair : ∀ x : ℕ, x ∈ D N → x ∈ Function.periodicPts (T N) → x = L ∨ x = L + 1 := by
        intro x hx hp
        have lower : ∀ y : ℕ, y ∈ D N → y ∈ Function.periodicPts (T N) → W ≤ A - y := by
          intro y hy hyp
          obtain ⟨r, hrb, hre, hr⟩ := image (W + 4) y hb hy hyp
          have er : heightDeficit j r ≤ 4 := by
            by_cases hrw : r ≤ W
            · have hh := (row.1 r hre).1.mpr hrw; omega
            · have hh := (row.1 r hre).2 (by omega) |>.2
              have mm : max 4 (r - Z j - 1) = 4 := by omega
              omega
          omega
        have lx := lower x hx hp
        have cx := coord j (W + 4) x (by omega) hb hx hp
        obtain ⟨y, hy, hyp, hyx⟩ := pred N x hn hx hp
        have ly := lower y hy hyp
        have cy := coord j (W + 4) y (by omega) hb hy hyp
        have er : 3 ≤ heightDeficit j (A - y) := by
          by_cases hrw : A - y ≤ W
          · have hh := row.2 (A - y) (by omega) hrw; omega
          · have hh := (row.1 (A - y) cy.2.1).2 (by omega) |>.1; omega
        have eb := slack j (A - y) (by omega) cy.2.1
        have my := map j (W + 4) (A - y) (by omega) hb cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        change x = A - (W + 4 - heightDeficit j (A - y)) at my
        dsimp [L]; omega
      have hd : d N = A - 4 := by
        have hc := cap (j + 1) (W + 5) (by omega) (by
          simpa only [show j + 1 - 2 = j - 1 by omega]
            using (show W + 5 ≤ B by omega))
        have eq : N - 1 = F (j + 1) - (W + 5) := by dsimp [N]; omega
        unfold d
        rw [eq]
        unfold heightDeficit at adjacent
        simp only [show j + 1 - 1 = j by omega] at adjacent hc
        change A - C (F (j + 1) - (W + 5)) = 4 at adjacent
        omega
      have goldenMono : Monotone G := by
        intro a b hab
        unfold D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
        apply Nat.floor_mono
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Nat.add_le_add_right hab 1
        · exact le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
      have lowMap : ∀ x : ℕ, x ∈ D N → x ≤ L → L + 1 ≤ T N x := by
        intro x hx hxl
        by_cases he : x = L
        · rw [he, lowEdge]
        have cb : C x ≤ B - 4 := by
          by_cases hxb : x < B
          · have hu := h.uMono x B hx.1 (by omega)
            have ua := (h.anchors (j - 1) (by omega)).1
            change U B = E at ua
            rw [ua] at hu
            have hb := (h.bounds x hx.1).2.2.1
            have eh : 4 ≤ F (j - 3) := by have := Nat.le_fib_add_one (j - 3); omega
            have fb := fibStep (j - 1) (by omega)
            simp only [Nat.sub_sub] at fb
            change B = E + F (j - 3) at fb
            omega
          · have hz : A - x ≤ E := by omega
            have rz := (row.1 (A - x) hz).2 (by dsimp [L] at *; omega) |>.1
            have cc := cap j (A - x) (by omega) hz
            have ex : A - (A - x) = x := by dsimp [L] at *; omega
            unfold heightDeficit at rz
            change 4 ≤ B - C (A - (A - x)) at rz
            rw [ex] at rz
            change C (A - (A - x)) ≤ B at cc
            rw [ex] at cc
            omega
        unfold T
        dsimp [N, L]; omega
      have highMap : ∀ x : ℕ, x ∈ D N → L + 1 ≤ x → T N x ≤ L := by
        intro x hx hxl
        by_cases he : x = L + 1
        · rw [he, highEdge]
        have cb : B - 3 ≤ C x := by
          by_cases hxa : x ≤ A
          · have hz : A - x ≤ W := by dsimp [L] at *; omega
            have rr := (row.1 (A - x) (by omega)).1.mpr hz
            have ex : A - (A - x) = x := by omega
            unfold heightDeficit at rr
            change B - C (A - (A - x)) ≤ 3 at rr
            rw [ex] at rr
            omega
          · have gm := goldenMono (show A + 1 ≤ x by omega)
            have ga := (h.plusOne j (by omega)).1
            change G (A + 1) = B + 1 at ga
            rw [ga] at gm
            have hb := (h.bounds x hx.1).2.1
            omega
        unfold T
        dsimp [N, L]; omega
      have parity : ∀ i : ℕ, (i % 2 = 0 → L + 1 ≤ X N i) ∧ (i % 2 = 1 → X N i ≤ L) := by
        intro i
        induction i with
        | zero =>
          change (0 % 2 = 0 → L + 1 ≤ N - 1) ∧ (0 % 2 = 1 → N - 1 ≤ L)
          dsimp [N, L]; omega
        | succ i ih =>
          have hx := orbitDomain N i hn
          have xe : X N (i + 1) = T N (X N i) := Function.iterate_succ_apply' (T N) i (N - 1)
          constructor
          · intro hi; rw [xe]; exact lowMap _ hx (ih.2 (by omega))
          · intro hi; rw [xe]; exact highMap _ hx (ih.1 (by omega))
      have gp := pair (g N) (orbitDomain N (d N) hn) (selected N hn)
      have hp := parity (d N)
      have phase : g N = if Even A then L + 1 else L := by
        by_cases he : Even A
        · rw [if_pos he]
          have heD : d N % 2 = 0 := by rw [Nat.even_iff] at he; omega
          have hh := hp.1 heD
          change L + 1 ≤ g N at hh
          omega
        · rw [if_neg he]
          have heD : d N % 2 = 1 := by
            have ho : Odd A := Nat.not_even_iff_odd.mp he
            rw [Nat.odd_iff] at ho; omega
          have hh := hp.2 heD
          change g N ≤ L at hh
          omega
      have ss := split j (W + 4) (by omega) hb
      change heightDeficit (j + 1) (W + 4) = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (W + 4 - (A - g N)) at ss
      constructor
      · by_cases he : Even A
        · rw [if_pos he] at phase ⊢
          have zz : A - g N = W := by dsimp [L] at *; omega
          have ew := zeroSmall 4 le_rfl
          rw [zz, show W + 4 - W = 4 by omega, eHigh, ew] at ss
          exact ss
        · rw [if_neg he] at phase ⊢
          have zz : A - g N = W + 1 := by dsimp [L] at *; omega
          have ew := zeroSmall 3 (by omega)
          rw [zz, show W + 4 - (W + 1) = 3 by omega, eLow, ew] at ss
          exact ss
      · change g N = _
        rw [phase]
        split <;> (dsimp [L]; all_goals omega)
    have criticalValue := critical.1
    have next := zNext j hj
    change Z (j + 1) = W + 3 + if Even A then 1 else 0 at next
    have nb : W + 3 ≤ Z (j + 1) ∧ Z (j + 1) ≤ W + 4 := by split at next <;> omega
    have newRow : Row (j + 1) := by
      constructor
      · intro b hb
        have hbB : b ≤ B := by simpa only [show j + 1 - 2 = j - 1 by omega] using hb
        by_cases hw : b ≤ W
        · have ee := low b hw
          refine ⟨⟨fun _ => by omega, fun _ => ee⟩, ?_⟩
          intro hn; omega
        by_cases hi : b ≤ W + 3
        · have ee := band b (by omega) hi
          refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
          intro hn; omega
        by_cases hc : b = W + 4
        · rw [hc]
          by_cases he : Even A
          · rw [if_pos he] at next criticalValue
            refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
            intro hn; omega
          · rw [if_neg he] at next criticalValue
            refine ⟨⟨fun hh => by omega, fun hh => by omega⟩, ?_⟩
            intro hn
            have mm := le_max_left 4 (W + 4 - Z (j + 1) - 1)
            exact ⟨by omega, by omega⟩
        · have rr := tail b hbB (by omega)
          refine ⟨⟨fun hh => by omega, fun hh => by omega⟩, ?_⟩
          intro hn
          refine ⟨rr.1, le_trans rr.2 ?_⟩
          apply max_le_max le_rfl
          omega
      · intro b hlo hhi
        by_cases hi : b ≤ W + 3
        · exact band b (by omega) hi
        · have be : b = W + 4 := by omega
          have he : Even A := by
            by_contra hn
            rw [if_neg hn] at next; omega
          rw [be, criticalValue, if_pos he]
    refine ⟨newRow, ?_⟩
    intro b hb he
    have largeOrCritical : W + 5 ≤ b ∨ b = W + 4 := by
      by_contra hn
      by_cases hw : b ≤ W
      · have ee := low b hw; omega
      have ee := band b (by omega) (by omega)
      omega
    rcases largeOrCritical with large | be
    · have hn : 3 ≤ F (j + 1) - b := by omega
      have cb := tailCycles b (g (F (j + 1) - b)) hb large
        (orbitDomain _ (d _) hn) (selected _ hn)
      have cc := coord j b (g (F (j + 1) - b)) (by omega) hb
        (orbitDomain _ (d _) hn) (selected _ hn)
      have ee := (row.1 (F j - g (F (j + 1) - b)) cc.2.1).2 (by omega) |>.1
      have ss := split j b (by omega) hb
      dsimp only at ss
      omega
    · have notEven : ¬ Even A := by
        intro hh
        have cv := criticalValue
        rw [if_pos hh] at cv
        rw [be] at he
        omega
      have ph := critical.2
      rw [if_neg notEven] at ph
      have zz : F j - g (F (j + 1) - b) = W + 1 := by rw [be]; dsimp [A] at ph; omega
      rw [zz]
      have rr := (row.1 (W + 1) (by omega)).2 (by omega)
      have mm : max 4 (W + 1 - Z j - 1) = 4 := by dsimp [W]; omega
      omega
  have rows : ∀ m : ℕ, 21 ≤ m → Row m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases he : m = 21
      · subst m; exact base
      have rr := step (m - 1) (by omega) (ih (m - 1) (by omega) (by omega))
      simpa only [show m - 1 + 1 = m by omega] using rr.1
  let P := fun k : ℕ => if k = 9 then 13 else ((k - 2) ^ 2 / 3 + 30) - 3 * k
  have pArithmetic : ∀ k : ℕ, 10 ≤ k →
      3 * k ≤ (k - 2) ^ 2 / 3 + 30 ∧
      P (k + 1) = P k + platformWidth (k - 1) := by
    intro k hk
    have ks : k - 2 + 2 = k := by omega
    have kt : k - 10 + 10 = k := by omega
    have d0 := Nat.mod_add_div ((k - 2) ^ 2) 3
    have d1 := Nat.mod_add_div ((k - 1) ^ 2) 3
    have r0 := Nat.mod_lt ((k - 2) ^ 2) (by omega : 0 < 3)
    have nonneg := Nat.zero_le ((k - 10) ^ 2)
    have pos : 3 * k ≤ (k - 2) ^ 2 / 3 + 30 := by nlinarith only [ks, kt, d0, r0, nonneg]
    refine ⟨pos, ?_⟩
    have kp : k + 1 - 2 = k - 1 := by omega
    have r : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have sq0 : (k - 2) ^ 2 % 3 = ((k - 2) % 3) ^ 2 % 3 := Nat.pow_mod _ _ _
    have sq1 : (k - 1) ^ 2 % 3 = ((k - 1) % 3) ^ 2 % 3 := Nat.pow_mod _ _ _
    have dk := Nat.mod_add_div k 3
    have dn := Nat.mod_add_div (2 * (k - 1) - 9) 3
    have rn := Nat.mod_lt (2 * (k - 1) - 9) (by omega : 0 < 3)
    have km : k - 1 + 1 = k := by omega
    have kn : 2 * (k - 1) - 9 + 9 = 2 * (k - 1) := by omega
    have result : (k - 1) ^ 2 / 3 + 30 - 3 * (k + 1) =
        (k - 2) ^ 2 / 3 + 30 - 3 * k + (2 * (k - 1) - 9) / 3 := by
      rcases r with hr | hr | hr
      all_goals
        have rr0 : (k - 2) % 3 = (k % 3 + 1) % 3 := by omega
        have rr1 : (k - 1) % 3 = (k % 3 + 2) % 3 := by omega
        rw [rr0, hr] at sq0
        rw [rr1, hr] at sq1
        norm_num at sq0 sq1
        have pos1 : 3 * (k + 1) ≤ (k - 1) ^ 2 / 3 + 30 := by
          nlinarith only [ks, km, d0, d1, sq0, sq1, pos]
        have s0 : (k - 2) ^ 2 / 3 + 30 - 3 * k + 3 * k =
            (k - 2) ^ 2 / 3 + 30 := by omega
        have s1 : (k - 1) ^ 2 / 3 + 30 - 3 * (k + 1) + 3 * (k + 1) =
            (k - 1) ^ 2 / 3 + 30 := by omega
        have rem : (2 * (k - 1) - 9) % 3 =
            (2 * ((k % 3 + 2) % 3)) % 3 := by omega
        rw [hr] at rem
        norm_num at rem
        nlinarith only [d0, d1, dn, sq0, sq1, ks, km, kn, s0, s1, rem]
    simpa only [P, if_neg (by omega : k + 1 ≠ 9), if_neg (by omega : k ≠ 9),
      kp, platformWidth] using result
  have pBounds : ∀ k : ℕ, 10 ≤ k →
      platformWidth k ≤ P k ∧ 2 * platformWidth (k - 1) ≤ P k ∧
      P (k - 1) + platformWidth (k - 2) ≤ P k ∧
      P (k - 2) + platformWidth (k - 1) ≤ P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases h10 : k = 10
      · subst k; norm_num [P, platformWidth]
      by_cases h11 : k = 11
      · subst k; norm_num [P, platformWidth]
      have prev := ih (k - 1) (by omega) (by omega)
      have prev2 := ih (k - 2) (by omega) (by omega)
      have stepP := (pArithmetic (k - 1) (by omega)).2
      have stepP2 := (pArithmetic (k - 2) (by omega)).2
      rw [show k - 1 + 1 = k by omega] at stepP
      rw [show k - 2 + 1 = k - 1 by omega] at stepP2
      have widths : 3 ≤ platformWidth (k - 2) ∧
          platformWidth k ≤ platformWidth (k - 1) + 1 ∧
          platformWidth (k - 1) ≤ platformWidth (k - 2) + 1 := by
        unfold platformWidth; omega
      have previousWidth : 3 ≤ platformWidth (k - 3) := by unfold platformWidth; omega
      simp only [Nat.sub_sub, Nat.reduceAdd] at prev prev2 stepP stepP2
      omega
  have budget : ∀ k v : ℕ, 9 ≤ k → v ≤ F (k - 2) →
      0 < heightDeficit k v → v ≤ heightDeficit k v * P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hk hv he
      by_cases h9 : k = 9
      · subst k
        norm_num [P] at hv ⊢
        nlinarith only [hv, he]
      by_cases h10 : k = 10
      · subst k
        norm_num [P] at hv ⊢
        nlinarith only [hv, he]
      let j := k - 1
      let N := F k - v
      let z := F j - g N
      let w := v - z
      have hj : 10 ≤ j := by dsimp [j]; omega
      have jk : j + 1 = k := by dsimp [j]; omega
      have vv : v ≤ F (j - 1) := by simpa only [j, Nat.sub_sub] using hv
      have rt := routes j v (by omega) vv
      have ss := split j v (by omega) vv
      rw [jk] at rt ss
      change heightDeficit k v = heightDeficit j z + heightDeficit (j - 1) w at ss
      have zdom : z ≤ F (j - 2) := rt.2.2.2.1
      have zw : z + w = v := by dsimp [w, z, N] at *; omega
      have wdom : w ≤ F (j - 1 - 2) := by
        have := rt.2.2.2.2.1
        dsimp [w, z, N, j] at *
        simp only [Nat.sub_sub, Nat.reduceAdd] at *
        omega
      have pb := pBounds k (by omega)
      have p1 : P j ≤ P k := by dsimp [j]; omega
      have p2 : P (j - 1) ≤ P k := by dsimp [j]; simp only [Nat.sub_sub, Nat.reduceAdd]; omega
      by_cases e1 : heightDeficit j z = 0
      · have zero := (profiles j z (by omega) zdom).2.1.mp e1
        have e2 : 0 < heightDeficit (j - 1) w := by omega
        have bound := ih (j - 1) (by dsimp [j]; omega) w (by dsimp [j]; omega) wdom e2
        have monotone := Nat.mul_le_mul_left (heightDeficit (j - 1) w)
          (show P (j - 1) + platformWidth j ≤ P k by
            dsimp [j]; simp only [Nat.sub_sub]; exact pb.2.2.2)
        nlinarith only [zero, bound, monotone, ss, zw, e2]
      by_cases e2 : heightDeficit (j - 1) w = 0
      · have zero := (profiles (j - 1) w (by omega) wdom).2.1.mp e2
        have e1p : 0 < heightDeficit j z := by omega
        have bound := ih j (by dsimp [j]; omega) z (by omega) zdom e1p
        have monotone := Nat.mul_le_mul_left (heightDeficit j z)
          (show P j + platformWidth (j - 1) ≤ P k by
            dsimp [j]; simp only [Nat.sub_sub]; exact pb.2.2.1)
        nlinarith only [zero, bound, monotone, ss, zw, e1p]
      · have iz := ih j (by dsimp [j]; omega) z (by omega) zdom (by omega)
        have iw := ih (j - 1) (by dsimp [j]; omega) w (by dsimp [j]; omega) wdom (by omega)
        have mz := Nat.mul_le_mul_left (heightDeficit j z) p1
        have mw := Nat.mul_le_mul_left (heightDeficit (j - 1) w) p2
        nlinarith only [iz, iw, mz, mw, ss, zw]
  have domination : ∀ k : ℕ, 22 ≤ k → 4 * P k ≤ F (k - 4) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases h22 : k = 22
      · subst k; norm_num [P]
      have prev := ih (k - 1) (by omega) (by omega)
      have ps := (pArithmetic (k - 1) (by omega)).2
      rw [show k - 1 + 1 = k by omega] at ps
      have pb := (pBounds (k - 1) (by omega)).2.1
      have growth : 4 * platformWidth (k - 2) ≤ F (k - 6) := by
        have linear : ∀ n : ℕ, 17 ≤ n → 4 * (n + 4) ≤ F n := by
          intro n
          induction n using Nat.strong_induction_on with
          | h n ih =>
            intro hn
            by_cases h17 : n = 17
            · subst n; norm_num
            have prev := ih (n - 1) (by omega) (by omega)
            have fs := fibStep n (by omega)
            have lower : 4 ≤ F (n - 2) := by
              have hh := Nat.fib_mono (show 6 ≤ n - 2 by omega)
              norm_num at hh; omega
            omega
        have low := linear (k - 6) (by omega)
        unfold platformWidth
        omega
      have f1 := fibStep (k - 4) (by omega)
      simp only [Nat.sub_sub, Nat.reduceAdd] at *
      omega
  intro m b hm hb parent4
  let N := F m - b
  let z := F (m - 1) - g N
  let w := F (m - 2) - (N - g N)
  let Ω := fun r : ℕ => b - heightDeficit (m - 1) r
  let r₀ := b - 4
  have fm := fibStep m (by omega)
  have fprev := fibStep (m - 1) (by omega)
  simp only [Nat.sub_sub, Nat.reduceAdd] at fprev
  have low := Nat.le_fib_add_one (m - 1)
  have hn : 3 ≤ N := by dsimp [N]; omega
  have jEq : m - 1 + 1 = m := by omega
  have rt := routes (m - 1) b (by omega) (by simpa only [Nat.sub_sub] using hb)
  rw [jEq] at rt
  change g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
    z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧ _ at rt
  have ez := (step (m - 1) (by omega) (rows (m - 1) (by omega))).2 b
    (by simpa only [Nat.sub_sub] using hb)
  rw [jEq] at ez
  have first4 : heightDeficit (m - 1) z = 4 := ez parent4
  have ss := split (m - 1) b (by omega) (by simpa only [Nat.sub_sub] using hb)
  rw [jEq] at ss
  have bw : b - z = w := by omega
  change heightDeficit m b = heightDeficit (m - 1) z + heightDeficit (m - 2) (b - z) at ss
  rw [bw] at ss
  have second0 : heightDeficit (m - 2) w = 0 := by omega
  have flat := (profiles (m - 2) w (by omega)
    (by simpa only [Nat.sub_sub] using rt.2.2.2.2.1)).2.1.mp second0
  have bc := budget m b (by omega) hb (by omega)
  rw [parent4] at bc
  have pc : P m = ((m - 2) ^ 2 / 3 + 30) - 3 * m := by dsimp [P]; rw [if_neg (by omega)]
  have enclosure := domination m hm
  have ba : b ≤ F (m - 4) := by omega
  have bprev : b ≤ F (m - 3) := le_trans ba (Nat.fib_mono (by omega))
  have cg : C (g N) + 4 = F (m - 2) := by
    have capg := cap (m - 1) z (by omega) (by simpa only [Nat.sub_sub] using rt.2.2.2.1)
    unfold heightDeficit at first4 capg
    simp only [Nat.sub_sub, Nat.reduceAdd] at first4 capg
    rw [← rt.1] at first4 capg
    omega
  have edge : T N (g N) + w = g N + 4 := by
    unfold T
    dsimp [N] at *
    omega
  have signed : ((g N : ℤ) - (T N (g N) : ℤ)) = (w : ℤ) - 4 := by
    have edgeZ : (T N (g N) : ℤ) + w = (g N : ℤ) + 4 := by exact_mod_cast edge
    omega
  have all : ∀ r : ℕ, r ≤ b →
      r ≤ F (m - 3) ∧ r ≤ F (m - 4) ∧
      1 ≤ F (m - 1) - r ∧ F (m - 1) - r ≤ N - 1 ∧
      heightDeficit (m - 1) r ≤ (2 * r) / 3 ∧ (2 * r) / 3 ≤ b ∧
      Ω r ≤ b ∧ T N (F (m - 1) - r) = F (m - 1) - Ω r := by
    intro r hr
    have rd : r ≤ F (m - 1 - 2) := by simpa only [Nat.sub_sub] using le_trans hr bprev
    have widthR : 10 ≤ platformWidth (m - 1) := by unfold platformWidth; omega
    have bound : heightDeficit (m - 1) r ≤ (2 * r) / 3 := by
      by_cases high : 5 ≤ heightDeficit (m - 1) r
      · have weighted := full30_6 U h24 seed20 seed21 (m - 1) r (by omega) rd high
        have orderQ : (21 : ℚ) ≤ (m - 1 : ℕ) := by exact_mod_cast (show 21 ≤ m - 1 by omega)
        have q : (3 : ℚ) * heightDeficit (m - 1) r ≤ 2 * r := by
          linarith only [weighted, orderQ]
        have qNat : 3 * heightDeficit (m - 1) r ≤ 2 * r := by exact_mod_cast q
        omega
      · by_cases small : r ≤ platformWidth (m - 1)
        · have zero := (profiles (m - 1) r (by omega) rd).2.1.mpr small
          omega
        · omega
    have mapped := map (m - 1) b r (by omega)
      (by simpa only [Nat.sub_sub] using hb) rd hr
    rw [jEq] at mapped
    change T N (F (m - 1) - r) = F (m - 1) - Ω r at mapped
    refine ⟨by omega, by omega, ?_, ?_, bound, by omega, Nat.sub_le _ _, mapped⟩
    · have ff := Nat.le_fib_add_one (m - 2)
      omega
    · dsimp [N]
      have ff := fibStep (m - 2) (by omega)
      simp only [Nat.sub_sub, Nat.reduceAdd] at ff
      have ll := Nat.le_fib_add_one (m - 3)
      omega
  have iterateBound : ∀ i r : ℕ, r ≤ b → Ω^[i] r ≤ b := by
    intro i
    induction i with
    | zero => intro r hr; exact hr
    | succ i ih =>
      intro r hr
      rw [Function.iterate_succ_apply']
      exact (all _ (ih r hr)).2.2.2.2.2.2.1
  have conjugacy : ∀ i r : ℕ, r ≤ b →
      (T N)^[i] (F (m - 1) - r) = F (m - 1) - Ω^[i] r := by
    intro i
    induction i with
    | zero => intro r hr; rfl
    | succ i ih =>
      intro r hr
      rw [Function.iterate_succ_apply', ih r hr, Function.iterate_succ_apply']
      exact (all _ (iterateBound i r hr)).2.2.2.2.2.2.2
  have zb : z ≤ b := by omega
  have periods : ∀ k : ℕ, Function.IsPeriodicPt (T N) k (g N) ↔
      Function.IsPeriodicPt Ω k z := by
    intro k
    change (T N)^[k] (g N) = g N ↔ Ω^[k] z = z
    rw [rt.1, conjugacy k z zb]
    have ib := iterateBound k z zb
    have legal := (all z zb).2.2.1
    omega
  have zp : z ∈ Function.periodicPts Ω := by
    obtain ⟨k, hk, hp⟩ := selected N hn
    exact ⟨k, hk, (periods k).mp hp⟩
  have oz : Ω z = r₀ := by dsimp [Ω, r₀]; rw [first4]
  have rp : r₀ ∈ Function.periodicPts Ω := by
    obtain ⟨k, hk, hp⟩ := zp
    exact ⟨k, hk, oz ▸ hp.apply⟩
  have unique : ∀ r : ℕ, r ≤ b → r ∈ Function.periodicPts Ω →
      heightDeficit (m - 1) r = 4 → r = z := by
    intro r hr hp he
    apply (Function.bijOn_periodicPts Ω).injOn hp zp
    dsimp [Ω]
    rw [he, first4]
  let p := Function.minimalPeriod Ω z
  have ppos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts zp
  have pphys : Function.minimalPeriod (T N) (g N) = p :=
    Function.minimalPeriod_eq_minimalPeriod_iff.mpr periods
  have pr : Function.minimalPeriod Ω r₀ = p := by
    rw [← oz]
    exact Function.minimalPeriod_apply zp
  let f : Fin (b + 1) → Fin (b + 1) := fun r => ⟨Ω r, by
    have hh := (all r (by omega)).2.2.2.2.2.2.1; omega⟩
  let a : Fin (b + 1) := ⟨r₀, by dsimp [r₀]; omega⟩
  have sem : Function.Semiconj (fun r : Fin (b + 1) => (r : ℕ)) f Ω := fun r => rfl
  have pf : Function.minimalPeriod f a = p := by
    rw [← pr]
    apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro k
    change f^[k] a = a ↔ Ω^[k] r₀ = r₀
    have vi : ((f^[k] a : Fin (b + 1)) : ℕ) = Ω^[k] r₀ := (sem.iterate_right k) a
    constructor
    · intro hh
      have hv := congrArg (fun r : Fin (b + 1) => (r : ℕ)) hh
      rw [vi] at hv
      exact hv
    · intro hh
      apply Fin.ext
      rw [vi]
      exact hh
  have pbound : p ≤ b + 1 := by
    have hh : Function.minimalPeriod f a ≤ Fintype.card (Fin (b + 1)) :=
      Function.minimalPeriod_le_card
    simpa only [Fintype.card_fin, pf] using hh
  have last : Ω^[p - 1] r₀ = z := by
    rw [← oz, ← Function.iterate_succ_apply, show (p - 1).succ = p by omega]
    exact Function.isPeriodicPt_minimalPeriod Ω z
  have firstHit : ∀ i : ℕ, i < p - 1 → heightDeficit (m - 1) (Ω^[i] r₀) ≠ 4 := by
    intro i hi he
    have ip : Ω^[i] r₀ ∈ Function.periodicPts Ω := by
      obtain ⟨k, hk, hp⟩ := rp
      exact ⟨k, hk, hp.apply_iterate i⟩
    have iz := unique _ (iterateBound i r₀ (by dsimp [r₀]; omega)) ip he
    have eq : Ω^[i] r₀ = Ω^[p - 1] r₀ := iz.trans last.symm
    have indices := Function.iterate_injOn_Iio_minimalPeriod
      (f := Ω) (x := r₀) (show i < Function.minimalPeriod Ω r₀ by rw [pr]; omega)
      (show p - 1 < Function.minimalPeriod Ω r₀ by rw [pr]; omega) eq
    omega
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨rt.1, rt.2.1, rt.2.2.1, rt.2.2.2.1, rt.2.2.2.2.1,
    first4, second0, flat, signed, ?_, ?_, all, p - 1, by omega, ?_, firstHit,
    last.symm, ?_, pphys.trans (show p = p - 1 + 1 by omega), ?_⟩
  · simpa only [pc] using bc
  · simpa only [pc] using enclosure
  · rw [last]; exact first4
  · rw [last]; exact rt.1
  · intro r hr hp he
    exact (unique r hr hp he).trans last.symm

end D5.S1.Recurrence.Invariants.CloitreActualDeficitFourSelector
