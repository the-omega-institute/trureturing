/- GID: D5/S1/Recurrence/Invariants/CloitreActualDeficitFourFees
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualDeficitFourFees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional complete actual deficit-four positive fees and finite spine settlement. -/

import D5.S1.Recurrence.Invariants.CloitreActualDeficitFourBand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.CloitreActualDeficitFourFees
open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
open D5.S1.Recurrence.Invariants.CloitreActualUnweightedCone
open D5.S1.Recurrence.Invariants.CloitreActualDeficitFourSelector
open D5.S1.Recurrence.Invariants.CloitreActualDeficitFourBand
local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
-- The simultaneous cap-level orbit induction and finite budget induction need these limits.
/-- Complete full-support positive-fee partition and finite actual first-child
spine settlement under the original conditional foundations and block seeds. -/
theorem full30_5 (U : ℕ → ℕ) (h24 : Hyp24_1 U)
    (seed20 : ∀ v : ℕ, v ≤ F 18 →
      (heightDeficit 20 v ≤ 2 ↔ v ≤ 35) ∧
      (35 < v → 3 ≤ heightDeficit 20 v ∧
        heightDeficit 20 v ≤ max 3 (v - 36)))
    (seed21 : ∀ v : ℕ, v ≤ F 19 →
      (heightDeficit 21 v ≤ 3 ↔ v ≤ 45) ∧
      (45 < v → 4 ≤ heightDeficit 21 v ∧
        heightDeficit 21 v ≤ max 4 (v - 46))) :
    let Z := fun m : ℕ => 3 * m + (m - 1) / 3 - 24
    let B := fun m : ℕ => 4 * m - 34
    let Φ := fun m t : ℕ => max ((t : ℤ) - (B m : ℤ)) 0
    let K := fun N : ℕ => (g N : ℤ) - (T N (g N) : ℤ)
    let ε := fun m b : ℕ => if b = Z m + 1 ∧ m % 3 ≠ 1 then 1 else 0
    (∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → heightDeficit m b = 4 →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      heightDeficit (m - 1) z = 4 ∧ heightDeficit (m - 2) w = 0 ∧
      K N = (w : ℤ) - 4 ∧
      (b : ℤ) - (B m : ℤ) = ((z : ℤ) - (B (m - 1) : ℤ)) + K N ∧
      max (K N) 0 = Φ m b - Φ (m - 1) z ∧
      (b ≤ B m → Z m < b ∧ z ≤ B (m - 1) ∧ K N ≤ 0 ∧
        Φ m b = 0 ∧ Φ (m - 1) z = 0 ∧ max (K N) 0 = 0 ∧
        (b < B m → z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
          K N = -(ε m b : ℤ) ∧ z < B (m - 1)) ∧
        (b = B m → z = B (m - 1) ∧ w = 4 ∧ K N = 0)) ∧
      (B m < b → B (m - 1) ≤ z ∧ 0 ≤ K N ∧ 4 ≤ w ∧
        (K N = 0 → z = b - 4 ∧ B (m - 1) < z) ∧
        (0 < K N → ∃ p : ℕ, 0 < p ∧ (T N)^[p] (g N) = g N ∧
          let y := (T N)^[p - 1] (g N)
          let u := F (m - 1) - y
          T N y = g N ∧ y ∈ D N ∧ y = F (m - 1) - u ∧
          u ≤ F (m - 3) ∧ u ≤ b - 4 ∧
          z = b - heightDeficit (m - 1) u ∧
          heightDeficit (m - 1) u = w ∧ 5 ≤ w ∧
          4 * m - 42 ≤ u - w ∧ B (m - 1) ≤ z))) ∧
    (∀ M b₀ : ℕ, 22 ≤ M → b₀ ≤ F (M - 2) → heightDeficit M b₀ = 4 →
      let Ns := fun s : ℕ => g^[s] (F M - b₀)
      let ms := fun s : ℕ => M - s
      let bs := fun s : ℕ => F (ms s) - Ns s
      let S : ℤ := ∑ s ∈ Finset.range (M - 21), max (K (Ns s)) 0
      bs 0 = b₀ ∧
      (∀ s : ℕ, s ≤ M - 21 → 21 ≤ ms s ∧ Ns s = F (ms s) - bs s ∧
        bs s ≤ F (ms s - 2) ∧ heightDeficit (ms s) (bs s) = 4) ∧
      (∀ s : ℕ, s < M - 21 → 22 ≤ ms s ∧ Ns (s + 1) = g (Ns s) ∧
        ms (s + 1) = ms s - 1 ∧ bs (s + 1) = F (ms s - 1) - g (Ns s) ∧
        max (K (Ns s)) 0 = Φ (ms s) (bs s) - Φ (ms (s + 1)) (bs (s + 1))) ∧
      ms (M - 21) = 21 ∧
      ((21 - 2) ^ 2 / 3 + 30) - 3 * 21 = (87 : ℕ) ∧
      bs (M - 21) ≤ 4 * 87 ∧ B 21 = 50 ∧
      S = Φ M b₀ - Φ 21 (bs (M - 21)) ∧
      0 ≤ Φ 21 (bs (M - 21)) ∧ Φ 21 (bs (M - 21)) ≤ 298 ∧
      0 ≤ S ∧ S ≤ Φ M b₀ ∧ Φ M b₀ ≤ S + 298 ∧
      (b₀ : ℤ) ≤ (B M : ℤ) + Φ M b₀ ∧
      (B M : ℤ) + Φ M b₀ ≤ 4 * (M : ℤ) + S + 264) ∧
    ((∃ a c : ℝ, 0 ≤ a ∧ 0 ≤ c ∧
        ∀ m b : ℕ, 21 ≤ m → b ≤ F (m - 2) → heightDeficit m b = 4 →
          (b : ℝ) ≤ a * (m : ℝ) + c) ↔
      (∃ a' c' : ℝ, 0 ≤ a' ∧ 0 ≤ c' ∧
        ∀ M b₀ : ℕ, 22 ≤ M → b₀ ≤ F (M - 2) → heightDeficit M b₀ = 4 →
          let Ns := fun s : ℕ => g^[s] (F M - b₀)
          let S : ℤ := ∑ s ∈ Finset.range (M - 21), max (K (Ns s)) 0
          (S : ℝ) ≤ a' * (M : ℝ) + c'))
 := by
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
    intro m hm; unfold platformWidth; omega
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
      rw [← Function.iterate_add_apply, show d N - μ + μ = d N by omega]
      rfl
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
    simp only [max_le_iff, le_min_iff] at hi
    have ff := fibStep (j + 1) (by omega)
    have fg := fibStep j (by omega)
    rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at ff
    dsimp only
    omega
  have map : ∀ j b z : ℕ, 20 ≤ j → b ≤ F (j - 1) → z ≤ F (j - 2) → z ≤ b →
      T (F (j + 1) - b) (F j - z) = F j - (b - heightDeficit j z) := by
    intro j b z hj hb hz hzb
    have hc := cap j z (by omega) hz
    have he := slack j z hj hz
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
  dsimp only
  let Z := fun k : ℕ => 3 * k + (k - 1) / 3 - 24
  let B := fun k : ℕ => 4 * k - 34
  let Φ := fun m t : ℕ => max ((t : ℤ) - (B m : ℤ)) 0
  let K := fun N : ℕ => (g N : ℤ) - (T N (g N) : ℤ)
  let ε := fun m b : ℕ => if b = Z m + 1 ∧ m % 3 ≠ 1 then 1 else 0
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
    have bb := (full30_4 U h24 seed20 seed21).1 j hj
    dsimp [Z] at *
    constructor <;> omega
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
      Row (j + 1) := by
    intro j hj row
    let A := F j
    let B := F (j - 1)
    let E := F (j - 2)
    let W := Z j
    have ff : F (j + 1) = A + B := by simpa [A, B] using fibStep (j + 1) (by omega)
    have fg : A = B + E := fibStep j (by omega)
    have eb : E ≤ B := Nat.fib_mono (by omega)
    have hh : 10 ≤ B := by have := Nat.le_fib_add_one (j - 1); dsimp [B]; omega
    have smallW : 45 ≤ W ∧ W + 5 < E := sizes j hj
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
      have ss := split j b (by omega) hb
      change heightDeficit (j + 1) b = heightDeficit j z + heightDeficit (j - 1) w at ss
      have ez := (row.1 z cc.2.1).2 (by omega)
      have bound : heightDeficit (j + 1) b ≤ max 4 (b - W - 5) := by
        by_cases h5 : 5 ≤ heightDeficit (j + 1) b
        · have hh := full30_2 U h24 seed20 seed21 (j + 1) b (by omega)
            (by simpa only [show j + 1 - 2 = j - 1 by omega] using hb) h5
          have mm := le_max_right 4 (b - W - 5)
          dsimp [W, Z] at *; omega
        · have mm := le_max_left 4 (b - W - 5); omega
      exact ⟨by omega, bound⟩
    have adjacent : heightDeficit (j + 1) (W + 5) = 4 := by
      have rr := tail (W + 5) (by omega) le_rfl
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
    have critical : heightDeficit (j + 1) (W + 4) = if Even A then 3 else 4 := by
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
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.add_le_add_right hab 1)
          (le_of_lt (inv_pos.mpr Real.goldenRatio_pos)))
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
      by_cases he : Even A
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
          · rw [if_pos he] at next critical
            refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
            intro hn; omega
          · rw [if_neg he] at next critical
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
          rw [be, critical, if_pos he]
    exact newRow
  have rows : ∀ m : ℕ, 21 ≤ m → Row m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases he : m = 21
      · subst m; exact base
      have rr := step (m - 1) (by omega) (ih (m - 1) (by omega) (by omega))
      simpa only [show m - 1 + 1 = m by omega] using rr
  let P := fun k : ℕ => if k = 9 then 13 else ((k - 2) ^ 2 / 3 + 30) - 3 * k
  have pBounds : ∀ k : ℕ, 10 ≤ k → k ≤ 21 →
      P (k - 1) + platformWidth (k - 2) ≤ P k ∧
      P (k - 2) + platformWidth (k - 1) ≤ P k := by
    intro k hk h21
    interval_cases k <;> norm_num [P, platformWidth]
  have budget : ∀ k v : ℕ, 9 ≤ k → k ≤ 21 → v ≤ F (k - 2) →
      0 < heightDeficit k v → v ≤ heightDeficit k v * P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hk hk21 hv he
      by_cases hsmall : k ≤ 10
      · interval_cases k <;> norm_num [P] at hv ⊢ <;> nlinarith only [hv, he]
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
      have pb := pBounds k (by omega) hk21
      have p1 : P j ≤ P k := by dsimp [j]; omega
      have p2 : P (j - 1) ≤ P k := by dsimp [j]; simp only [Nat.sub_sub, Nat.reduceAdd]; omega
      by_cases e1 : heightDeficit j z = 0
      · have zero := (profiles j z (by omega) zdom).2.1.mp e1
        have e2 : 0 < heightDeficit (j - 1) w := by omega
        have bound := ih (j - 1) (by dsimp [j]; omega) w (by dsimp [j]; omega) (by dsimp [j]; omega) wdom e2
        have monotone := Nat.mul_le_mul_left (heightDeficit (j - 1) w)
          (show P (j - 1) + platformWidth j ≤ P k by
            dsimp [j]; simp only [Nat.sub_sub]; exact pb.2)
        nlinarith only [zero, bound, monotone, ss, zw, e2]
      by_cases e2 : heightDeficit (j - 1) w = 0
      · have zero := (profiles (j - 1) w (by omega) wdom).2.1.mp e2
        have e1p : 0 < heightDeficit j z := by omega
        have bound := ih j (by dsimp [j]; omega) z (by omega) (by dsimp [j]; omega) zdom e1p
        have monotone := Nat.mul_le_mul_left (heightDeficit j z)
          (show P j + platformWidth (j - 1) ≤ P k by
            dsimp [j]; simp only [Nat.sub_sub]; exact pb.1)
        nlinarith only [zero, bound, monotone, ss, zw, e1p]
      · have iz := ih j (by dsimp [j]; omega) z (by omega) (by dsimp [j]; omega) zdom (by omega)
        have iw := ih (j - 1) (by dsimp [j]; omega) w (by dsimp [j]; omega) (by dsimp [j]; omega) wdom (by omega)
        have mz := Nat.mul_le_mul_left (heightDeficit j z) p1
        have mw := Nat.mul_le_mul_left (heightDeficit (j - 1) w) p2
        nlinarith only [iz, iw, mz, mw, ss, zw]
  have terminal : ∀ b : ℕ, b ≤ F 19 → heightDeficit 21 b = 4 → b ≤ 348 := by
    intro b hb he
    have hh := budget 21 b (by omega) le_rfl hb (by omega)
    norm_num [P, he] at hh
    exact hh
  have tailControl : ∀ m b x : ℕ, 22 ≤ m → b ≤ F (m - 2) → B m < b →
      x ∈ D (F m - b) → x ∈ Function.periodicPts (T (F m - b)) →
      Z (m - 1) < F (m - 1) - x ∧ F (m - 1) - x ≤ b - 4 := by
    intro m b x hm hb hlarge hx hp
    have me : m - 1 + 1 = m := by omega
    have bF : b ≤ F (m - 1) := hb.trans (Nat.fib_mono (by omega))
    have hm1 : 21 ≤ m - 1 := by omega
    have big : Z (m - 1) + 5 ≤ b := by dsimp [B, Z] at *; omega
    have hn : 3 ≤ F m - b := by
      have ff := fibStep m (by omega)
      have fl := Nat.le_fib_add_one (m - 1)
      omega
    have lower : ∀ y : ℕ, y ∈ D (F m - b) →
        y ∈ Function.periodicPts (T (F m - b)) → Z (m - 1) < F (m - 1) - y := by
      intro y hy hyp
      obtain ⟨r, hr, hrp, hry⟩ := pred _ y hn hy hyp
      have cr := coord (m - 1) b r (by omega) (by simpa only [Nat.sub_sub] using hb)
        (by simpa only [me] using hr) (by simpa only [me] using hrp)
      have cy := coord (m - 1) b y (by omega) (by simpa only [Nat.sub_sub] using hb)
        (by simpa only [me] using hy) (by simpa only [me] using hyp)
      have er : heightDeficit (m - 1) (F (m - 1) - r) ≤ b - Z (m - 1) - 1 := by
        have rr := (rows (m - 1) hm1).1 _ cr.2.1
        by_cases hi : F (m - 1) - r ≤ Z (m - 1)
        · have ee := rr.1.mpr hi; omega
        · have ee := (rr.2 (by omega)).2
          have mm : max 4 (F (m - 1) - r - Z (m - 1) - 1) ≤ b - Z (m - 1) - 1 := by
            apply max_le <;> omega
          omega
      have mr := map (m - 1) b (F (m - 1) - r) (by omega)
        (by simpa only [Nat.sub_sub] using hb) cr.2.1 cr.1
      rw [me, ← cr.2.2.2.1, hry] at mr
      change y = F (m - 1) - (b - heightDeficit (m - 1) (F (m - 1) - r)) at mr
      have yr := cy.2.2.2.1
      omega
    have lx := lower x hx hp
    obtain ⟨y, hy, hyp, hyx⟩ := pred _ x hn hx hp
    have ly := lower y hy hyp
    have cy := coord (m - 1) b y (by omega) (by simpa only [Nat.sub_sub] using hb)
      (by simpa only [me] using hy) (by simpa only [me] using hyp)
    have ey := ((rows (m - 1) hm1).1 _ cy.2.1).2 ly |>.1
    have eyb := slack (m - 1) _ (by omega) cy.2.1
    have my := map (m - 1) b (F (m - 1) - y) (by omega)
      (by simpa only [Nat.sub_sub] using hb) cy.2.1 cy.1
    rw [me, ← cy.2.2.2.1, hyx] at my
    exact ⟨lx, by omega⟩
  have roots : ∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → heightDeficit m b = 4 →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      heightDeficit (m - 1) z = 4 ∧ heightDeficit (m - 2) w = 0 ∧
      K N = (w : ℤ) - 4 ∧
      (b : ℤ) - (B m : ℤ) = ((z : ℤ) - (B (m - 1) : ℤ)) + K N ∧
      max (K N) 0 = Φ m b - Φ (m - 1) z ∧
      (b ≤ B m → Z m < b ∧ z ≤ B (m - 1) ∧ K N ≤ 0 ∧
        Φ m b = 0 ∧ Φ (m - 1) z = 0 ∧ max (K N) 0 = 0 ∧
        (b < B m → z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
          K N = -(ε m b : ℤ) ∧ z < B (m - 1)) ∧
        (b = B m → z = B (m - 1) ∧ w = 4 ∧ K N = 0)) ∧
      (B m < b → B (m - 1) ≤ z ∧ 0 ≤ K N ∧ 4 ≤ w ∧
        (K N = 0 → z = b - 4 ∧ B (m - 1) < z) ∧
        (0 < K N → ∃ p : ℕ, 0 < p ∧ (T N)^[p] (g N) = g N ∧
          let y := (T N)^[p - 1] (g N)
          let u := F (m - 1) - y
          T N y = g N ∧ y ∈ D N ∧ y = F (m - 1) - u ∧
          u ≤ F (m - 3) ∧ u ≤ b - 4 ∧
          z = b - heightDeficit (m - 1) u ∧
          heightDeficit (m - 1) u = w ∧ 5 ≤ w ∧
          4 * m - 42 ≤ u - w ∧ B (m - 1) ≤ z)) := by
    intro m b hm hb he
    let N := F m - b
    let z := F (m - 1) - g N
    let w := F (m - 2) - (N - g N)
    obtain ⟨hg, hc, hzw, hzd, hwd, hz4, hw0, _, hk, _, _, box, periodData⟩ :=
      full30_3 U h24 seed20 seed21 m b hm hb he
    obtain ⟨τ, _, _, _, _, _, hperiod, _⟩ := periodData
    change K N = (w : ℤ) - 4 at hk
    change z + w = b at hzw
    change g N = F (m - 1) - z at hg
    have bF : b ≤ F (m - 1) := hb.trans (Nat.fib_mono (by omega))
    have outside : Z m < b := by
      by_contra hi
      have hh := ((rows m (by omega)).1 b hb).1.mpr (by omega)
      omega
    have threshold : (b : ℤ) - (B m : ℤ) = ((z : ℤ) - (B (m - 1) : ℤ)) + K N := by
      have bb : B m = B (m - 1) + 4 := by dsimp [B]; omega
      have zz : (z : ℤ) + w = b := by exact_mod_cast hzw
      have bz : (B m : ℤ) = (B (m - 1) : ℤ) + 4 := by exact_mod_cast bb
      omega
    have strict : b < B m → z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
        K N = -(ε m b : ℤ) ∧ z < B (m - 1) := by
      intro hi
      obtain ⟨_, _, _, _, _, _, hz, hw, _, _, _, _, _, _, hj, _, _, hzb⟩ :=
        (full30_4 U h24 seed20 seed21).2.2.1 m b hm hb outside hi
      exact ⟨hz, hw, hj, hzb⟩
    have endpoint : b = B m → z = B (m - 1) ∧ w = 4 ∧ K N = 0 := by
      intro hi
      obtain ⟨_, _, hz, hw, _, _, _, hj, _, _⟩ :=
        (full30_4 U h24 seed20 seed21).2.2.2.2.2.2 m hm
      refine ⟨?_, ?_, ?_⟩
      · simpa only [N, z, hi] using hz
      · simpa only [N, w, hi] using hw
      · simpa only [N, hi] using hj
    have low : b ≤ B m → Z m < b ∧ z ≤ B (m - 1) ∧ K N ≤ 0 ∧
        Φ m b = 0 ∧ Φ (m - 1) z = 0 ∧ max (K N) 0 = 0 ∧
        (b < B m → z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
          K N = -(ε m b : ℤ) ∧ z < B (m - 1)) ∧
        (b = B m → z = B (m - 1) ∧ w = 4 ∧ K N = 0) := by
      intro hi
      have bounds : z ≤ B (m - 1) ∧ K N ≤ 0 := by
        by_cases hs : b < B m
        · have rr := strict hs
          exact ⟨by omega, by omega⟩
        · have rr := endpoint (by omega); exact ⟨by omega, by omega⟩
      have p0 : Φ m b = 0 := by dsimp only [Φ]; apply max_eq_right; omega
      have p1 : Φ (m - 1) z = 0 := by dsimp only [Φ]; apply max_eq_right; omega
      exact ⟨outside, bounds.1, bounds.2, p0, p1, max_eq_right bounds.2, strict, endpoint⟩
    have high : B m < b → B (m - 1) ≤ z ∧ 0 ≤ K N ∧ 4 ≤ w ∧
        (K N = 0 → z = b - 4 ∧ B (m - 1) < z) ∧
        (0 < K N → ∃ p : ℕ, 0 < p ∧ (T N)^[p] (g N) = g N ∧
          let y := (T N)^[p - 1] (g N)
          let u := F (m - 1) - y
          T N y = g N ∧ y ∈ D N ∧ y = F (m - 1) - u ∧
          u ≤ F (m - 3) ∧ u ≤ b - 4 ∧
          z = b - heightDeficit (m - 1) u ∧
          heightDeficit (m - 1) u = w ∧ 5 ≤ w ∧
          4 * m - 42 ≤ u - w ∧ B (m - 1) ≤ z) := by
      intro hi
      have hn : 3 ≤ N := by
        have ff := fibStep m (by omega)
        have fl := Nat.le_fib_add_one (m - 1)
        dsimp [N]; omega
      have gd := orbitDomain N (d N) hn
      change g N ∈ D N at gd
      have gp := Function.minimalPeriod_pos_iff_mem_periodicPts.mp
        (show 0 < Function.minimalPeriod (T N) (g N) by rw [hperiod]; omega)
      have tc := tailControl m b (g N) hm hb hi gd gp
      have w4 : 4 ≤ w := by change Z (m - 1) < z ∧ z ≤ b - 4 at tc; omega
      have nonneg : 0 ≤ K N := by omega
      have zero : K N = 0 → z = b - 4 ∧ B (m - 1) < z := by
        intro h0
        have wb : w = 4 := by omega
        dsimp [B] at *; omega
      have positive : 0 < K N → ∃ p : ℕ, 0 < p ∧ (T N)^[p] (g N) = g N ∧
          let y := (T N)^[p - 1] (g N)
          let u := F (m - 1) - y
          T N y = g N ∧ y ∈ D N ∧ y = F (m - 1) - u ∧
          u ≤ F (m - 3) ∧ u ≤ b - 4 ∧
          z = b - heightDeficit (m - 1) u ∧
          heightDeficit (m - 1) u = w ∧ 5 ≤ w ∧
          4 * m - 42 ≤ u - w ∧ B (m - 1) ≤ z := by
        intro hpos
        obtain ⟨p, hp, pp⟩ := gp
        let y := (T N)^[p - 1] (g N)
        let u := F (m - 1) - y
        have yd : y ∈ D N := (inv N hn).iterate (p - 1) gd
        have yp : y ∈ Function.periodicPts (T N) := ⟨p, hp, pp.apply_iterate (p - 1)⟩
        have yedge : T N y = g N := by
          dsimp [y]
          rw [← Function.iterate_succ_apply' (T N) (p - 1) (g N), show (p - 1).succ = p by omega]
          exact pp.eq
        have cy := coord (m - 1) b y (by omega) (by simpa only [Nat.sub_sub] using hb)
          (by simpa only [show m - 1 + 1 = m by omega] using yd)
          (by simpa only [show m - 1 + 1 = m by omega] using yp)
        have ty := tailControl m b y hm hb hi yd yp
        have my := (box u cy.1).2.2.2.2.2.2.2
        rw [← cy.2.2.2.1, yedge] at my
        have eu := slack (m - 1) u (by omega) cy.2.1
        have qeq : heightDeficit (m - 1) u = w := by
          change g N = F (m - 1) - (b - heightDeficit (m - 1) u) at my
          have hu := cy.1
          have hz := hzw
          change z + w = b at hz
          dsimp only [z] at hz
          omega
        have w5 : 5 ≤ w := by omega
        have cone := full30_2 U h24 seed20 seed21 (m - 1) u (by omega) cy.2.1 (by omega)
        have diff : 4 * m - 42 ≤ u - w := by rw [qeq] at cone; omega
        have eqz : z = b - heightDeficit (m - 1) u := by
          dsimp only [z]; have cg := hg; omega
        have zb : B (m - 1) ≤ z := by dsimp only [B]; rw [qeq] at eqz; omega
        refine ⟨p, hp, pp.eq, yedge, yd, cy.2.2.2.1, ?_, ty.2, ?_, qeq, w5, diff, zb⟩
        · simpa only [Nat.sub_sub] using cy.2.1
        · exact eqz
      have zb : B (m - 1) ≤ z := by
        by_cases h0 : K N = 0
        · have rr := zero h0; omega
        · obtain ⟨p, _, _, _, _, _, _, _, _, _, _, _, hh⟩ := positive (by omega)
          exact hh
      exact ⟨zb, nonneg, w4, zero, positive⟩
    have fee : max (K N) 0 = Φ m b - Φ (m - 1) z := by
      by_cases hi : b ≤ B m
      · have rr := low hi; rw [rr.2.2.2.1, rr.2.2.2.2.1, rr.2.2.2.2.2.1]; omega
      · have rr := high (by omega)
        have bp : (B m : ℤ) ≤ b := by exact_mod_cast (show B m ≤ b by omega)
        have zp : (B (m - 1) : ℤ) ≤ z := by exact_mod_cast rr.1
        dsimp [Φ]; rw [max_eq_left rr.2.1, max_eq_left (by omega), max_eq_left (by omega)]
        omega
    exact ⟨hg, hc, hzw, hzd, hwd, hz4, hw0, hk, threshold, fee, low, high⟩
  have spines : ∀ M b₀ : ℕ, 22 ≤ M → b₀ ≤ F (M - 2) → heightDeficit M b₀ = 4 →
      let Ns := fun s : ℕ => g^[s] (F M - b₀)
      let ms := fun s : ℕ => M - s
      let bs := fun s : ℕ => F (ms s) - Ns s
      let S : ℤ := ∑ s ∈ Finset.range (M - 21), max (K (Ns s)) 0
      bs 0 = b₀ ∧
      (∀ s : ℕ, s ≤ M - 21 → 21 ≤ ms s ∧ Ns s = F (ms s) - bs s ∧
        bs s ≤ F (ms s - 2) ∧ heightDeficit (ms s) (bs s) = 4) ∧
      (∀ s : ℕ, s < M - 21 → 22 ≤ ms s ∧ Ns (s + 1) = g (Ns s) ∧
        ms (s + 1) = ms s - 1 ∧ bs (s + 1) = F (ms s - 1) - g (Ns s) ∧
        max (K (Ns s)) 0 = Φ (ms s) (bs s) - Φ (ms (s + 1)) (bs (s + 1))) ∧
      ms (M - 21) = 21 ∧
      ((21 - 2) ^ 2 / 3 + 30) - 3 * 21 = (87 : ℕ) ∧
      bs (M - 21) ≤ 4 * 87 ∧ B 21 = 50 ∧
      S = Φ M b₀ - Φ 21 (bs (M - 21)) ∧
      0 ≤ Φ 21 (bs (M - 21)) ∧ Φ 21 (bs (M - 21)) ≤ 298 ∧
      0 ≤ S ∧ S ≤ Φ M b₀ ∧ Φ M b₀ ≤ S + 298 ∧
      (b₀ : ℤ) ≤ (B M : ℤ) + Φ M b₀ ∧
      (B M : ℤ) + Φ M b₀ ≤ 4 * (M : ℤ) + S + 264 := by
    intro M b₀ hM hb he
    let Ns := fun s : ℕ => g^[s] (F M - b₀)
    let ms := fun s : ℕ => M - s
    let bs := fun s : ℕ => F (ms s) - Ns s
    let S : ℤ := ∑ s ∈ Finset.range (M - 21), max (K (Ns s)) 0
    have bf : b₀ ≤ F M := hb.trans (Nat.fib_mono (by omega))
    have bzero : bs 0 = b₀ := by dsimp only [bs, ms, Ns]; simp only [Function.iterate_zero_apply, Nat.sub_zero]; omega
    have next : ∀ s : ℕ, Ns (s + 1) = g (Ns s) := fun s =>
      Function.iterate_succ_apply' g s (F M - b₀)
    have order : ∀ s : ℕ, ms (s + 1) = ms s - 1 := by intro s; dsimp [ms]; omega
    have gap : ∀ s : ℕ, bs (s + 1) = F (ms s - 1) - g (Ns s) := by
      intro s; dsimp only [bs]; rw [order, next]
    have nodes : ∀ s : ℕ, s ≤ M - 21 → 21 ≤ ms s ∧ Ns s = F (ms s) - bs s ∧
        bs s ≤ F (ms s - 2) ∧ heightDeficit (ms s) (bs s) = 4 := by
      intro s
      induction s with
      | zero =>
        intro hs
        simp only [bzero, ms, Ns, Function.iterate_zero_apply, Nat.sub_zero]
        exact ⟨by omega, True.intro, hb, he⟩
      | succ s ih =>
        intro hs
        obtain ⟨hm, hr, hd, h4⟩ := ih (by omega)
        have hm22 : 22 ≤ ms s := by dsimp [ms] at *; omega
        obtain ⟨hg, _, _, hz, _, hchild, _⟩ := full30_3 U h24 seed20 seed21 (ms s) (bs s) hm22 hd h4
        rw [← hr] at hg hz hchild
        refine ⟨by dsimp [ms] at *; omega, ?_, ?_, ?_⟩
        · simpa only [Nat.succ_eq_add_one, next, order, gap] using hg
        · simpa only [Nat.succ_eq_add_one, order, gap, Nat.sub_sub, Nat.reduceAdd] using hz
        · simpa only [Nat.succ_eq_add_one, order, gap] using hchild
    have edges : ∀ s : ℕ, s < M - 21 → 22 ≤ ms s ∧ Ns (s + 1) = g (Ns s) ∧
        ms (s + 1) = ms s - 1 ∧ bs (s + 1) = F (ms s - 1) - g (Ns s) ∧
        max (K (Ns s)) 0 = Φ (ms s) (bs s) - Φ (ms (s + 1)) (bs (s + 1)) := by
      intro s hs
      obtain ⟨hm, hr, hd, h4⟩ := nodes s (by omega)
      have hm22 : 22 ≤ ms s := by dsimp [ms] at *; omega
      obtain ⟨_, _, _, _, _, _, _, _, _, hf, _, _⟩ := roots (ms s) (bs s) hm22 hd h4
      rw [← hr] at hf
      exact ⟨hm22, next s, order s, gap s, by simpa only [order, gap] using hf⟩
    have endOrder : ms (M - 21) = 21 := by dsimp [ms]; omega
    have endNode := nodes (M - 21) le_rfl
    rw [endOrder] at endNode
    have endBound := terminal (bs (M - 21)) endNode.2.2.1 endNode.2.2.2
    have tel : S = Φ M b₀ - Φ 21 (bs (M - 21)) := by
      calc
        S = ∑ s ∈ Finset.range (M - 21),
            (Φ (ms s) (bs s) - Φ (ms (s + 1)) (bs (s + 1))) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (edges s (Finset.mem_range.mp hs)).2.2.2.2
        _ = Φ (ms 0) (bs 0) - Φ (ms (M - 21)) (bs (M - 21)) :=
          Finset.sum_range_sub' (fun s => Φ (ms s) (bs s)) (M - 21)
        _ = Φ M b₀ - Φ 21 (bs (M - 21)) := by rw [bzero, endOrder]; rfl
    have endPhi : 0 ≤ Φ 21 (bs (M - 21)) ∧ Φ 21 (bs (M - 21)) ≤ 298 := by
      change 0 ≤ max ((bs (M - 21) : ℤ) - 50) 0 ∧ max ((bs (M - 21) : ℤ) - 50) 0 ≤ 298
      constructor
      · exact le_max_right _ _
      · apply max_le <;> omega
    have sn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have rootLower : (b₀ : ℤ) ≤ (B M : ℤ) + Φ M b₀ := by
      have hh := le_max_left ((b₀ : ℤ) - (B M : ℤ)) 0
      dsimp only [Φ]; omega
    have bM : (B M : ℤ) = 4 * (M : ℤ) - 34 := by dsimp only [B]; omega
    have sUpper : S ≤ Φ M b₀ := by omega
    have pUpper : Φ M b₀ ≤ S + 298 := by omega
    have totalUpper : (B M : ℤ) + Φ M b₀ ≤ 4 * (M : ℤ) + S + 264 := by omega
    exact ⟨bzero, nodes, edges, endOrder, by norm_num, endBound, by norm_num [B],
      tel, endPhi.1, endPhi.2, sn, sUpper, pUpper, rootLower, totalUpper⟩
  refine ⟨roots, spines, ?_⟩
  constructor
  · rintro ⟨a, c, ha, hc, bound⟩
    refine ⟨a, c, ha, hc, ?_⟩
    intro M b₀ hM hb he
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sUpper, _, _, _⟩ := spines M b₀ hM hb he
    have pp : Φ M b₀ ≤ (b₀ : ℤ) := by
      dsimp only [Φ]; apply max_le <;> omega
    have rb := bound M b₀ (by omega) hb he
    have sr : ((∑ s ∈ Finset.range (M - 21), max (K (g^[s] (F M - b₀))) 0 : ℤ) : ℝ) ≤ b₀ := by
      exact_mod_cast sUpper.trans pp
    exact sr.trans rb
  · rintro ⟨a', c', ha, hc, bound⟩
    refine ⟨a' + 4, c' + 264, by linarith, by linarith, ?_⟩
    intro m b hm hb he
    by_cases h21 : m = 21
    · subst m
      have tb := terminal b hb he
      have tr : (b : ℝ) ≤ 348 := by exact_mod_cast tb
      norm_num; nlinarith
    · have hm22 : 22 ≤ m := by omega
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, lower, upper⟩ := spines m b hm22 hb he
      have bb := bound m b hm22 hb he
      have zz := lower.trans upper
      have zr : (b : ℝ) ≤ 4 * (m : ℝ) +
          ((∑ s ∈ Finset.range (m - 21), max (K (g^[s] (F m - b))) 0 : ℤ) : ℝ) + 264 := by
        exact_mod_cast zz
      nlinarith
end D5.S1.Recurrence.Invariants.CloitreActualDeficitFourFees
