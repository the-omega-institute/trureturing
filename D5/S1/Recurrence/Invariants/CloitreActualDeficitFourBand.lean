/- GID: D5/S1/Recurrence/Invariants/CloitreActualDeficitFourBand
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualDeficitFourBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional actual strict deficit-four band, adjacent rows and finite spines. -/

import D5.S1.Recurrence.Invariants.CloitreActualUnweightedCone
import D5.S1.Recurrence.Invariants.CloitreActualDeficitFourSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.CloitreActualDeficitFourBand
open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
open D5.S1.Recurrence.Invariants.CloitreActualUnweightedCone
open D5.S1.Recurrence.Invariants.CloitreActualDeficitFourSelector
local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
-- The legal-block induction and prescribed critical clocks need these elaboration bounds.
/-- The complete actual deficit-four band, inherited finite first-child spines,
critical signed jumps, adjacent depths and qualified non-strict endpoint.
The full source foundations and finite full-block seeds remain premises. -/
theorem full30_4 (U : ℕ → ℕ) (h24 : Hyp24_1 U)
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
    let ε := fun m b : ℕ => if b = Z m + 1 ∧ m % 3 ≠ 1 then 1 else 0
    (∀ m : ℕ, 21 ≤ m → B m + 2 < F (m - 2)) ∧
    (∀ m b : ℕ, 21 ≤ m → b ≤ F (m - 2) → Z m < b → b ≤ B m →
      heightDeficit m b = 4) ∧
    (∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → Z m < b → b < B m →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      heightDeficit m b = 4 ∧ heightDeficit m (b + 1) = 4 ∧
      C N = F (m - 1) - 4 ∧ C (N - 1) = F (m - 1) - 4 ∧
      d N = F (m - 1) - 4 ∧ X N 0 = N - 1 ∧
      z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
      g N = F (m - 1) - b + 4 - ε m b ∧
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      ((g N : ℤ) - (T N (g N) : ℤ)) = -(ε m b : ℤ) ∧
      Function.minimalPeriod (T N) (g N) = 1 + ε m b ∧
      Z (m - 1) < z ∧ z < B (m - 1)) ∧
    (∀ M b₀ : ℕ, 22 ≤ M → b₀ ≤ F (M - 2) → Z M < b₀ → b₀ < B M →
      let Ns := fun s : ℕ => g^[s] (F M - b₀)
      let ms := fun s : ℕ => M - s
      let bs := fun s : ℕ => F (ms s) - Ns s
      (∀ s : ℕ, s ≤ M - 21 →
        21 ≤ ms s ∧ Ns s = F (ms s) - bs s ∧
        bs s ≤ F (ms s - 2) ∧ Z (ms s) < bs s ∧ bs s < B (ms s) ∧
        bs s + 1 ≤ F (ms s - 2) ∧
        heightDeficit (ms s) (bs s) = 4 ∧ heightDeficit (ms s) (bs s + 1) = 4 ∧
        C (Ns s) = F (ms s - 1) - 4 ∧ C (Ns s - 1) = F (ms s - 1) - 4 ∧
        d (Ns s) = F (ms s - 1) - 4) ∧
      (∀ s : ℕ, s < M - 21 →
        Ns (s + 1) = g (Ns s) ∧ ms (s + 1) = ms s - 1 ∧
        bs (s + 1) = F (ms s - 1) - g (Ns s) ∧
        bs (s + 1) = bs s - 4 + ε (ms s) (bs s) ∧
        F (ms s - 2) - (Ns s - g (Ns s)) = 4 - ε (ms s) (bs s) ∧
        g (Ns s) = F (ms s - 1) - bs s + 4 - ε (ms s) (bs s) ∧
        ((g (Ns s) : ℤ) - (T (Ns s) (g (Ns s)) : ℤ)) =
          -(ε (ms s) (bs s) : ℤ) ∧
        Function.minimalPeriod (T (Ns s)) (g (Ns s)) = 1 + ε (ms s) (bs s))) ∧
    (∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → Z m < b → b < B m → b ≤ B m - 2 →
      let N := F m - b
      d N = F (m - 1) - 4 ∧ d (N - 1) = F (m - 1) - 4 ∧
      C N = F (m - 1) - 4 ∧ C (N - 1) = F (m - 1) - 4 ∧
      g (N - 1) = F (m - 1) - b + 3 ∧ g (N - 1) ≤ g N ∧
      g N - g (N - 1) = 1 - ε m b ∧
      d (g N) = F (m - 2) - 4 ∧ C (g N - 1) = F (m - 2) - 4 ∧
      (ε m b = 1 →
        g N = g (N - 1) ∧
        F (m - 2) - (N - g N) = 3 ∧
        F (m - 2) - (N - 1 - g (N - 1)) = 4 ∧
        Function.minimalPeriod (T N) (g N) = 2 ∧
        Function.minimalPeriod (T (N - 1)) (g (N - 1)) = 1)) ∧
    (∀ M : ℕ, 22 ≤ M →
      let b₀ := Z M + 1
      let Ns := fun s : ℕ => g^[s] (F M - b₀)
      let ms := fun s : ℕ => M - s
      let bs := fun s : ℕ => F (ms s) - Ns s
      b₀ ≤ F (M - 2) ∧ Z M < b₀ ∧ b₀ < B M ∧
      (∀ s : ℕ, s ≤ M - 21 → bs s = Z (ms s) + 1) ∧
      (∀ s : ℕ, s < M - 21 →
        let K : ℤ := (g (Ns s) : ℤ) - (T (Ns s) (g (Ns s)) : ℤ)
        (K = -1 ↔ ms s % 3 ≠ 1) ∧
        (ms s % 3 = 1 → K = 0) ∧ max K 0 = 0)) ∧
    (∀ m : ℕ, 22 ≤ m →
      let N := F m - B m
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      B m ≤ F (m - 2) ∧ heightDeficit m (B m) = 4 ∧
      z = B (m - 1) ∧ w = 4 ∧ g N = F (m - 1) - B (m - 1) ∧
      N - g N = F (m - 2) - 4 ∧
      Function.minimalPeriod (T N) (g N) = 1 ∧
      ((g N : ℤ) - (T N (g N) : ℤ)) = 0 ∧
      (heightDeficit m (B m + 1) = 4 ∨ heightDeficit m (B m + 1) = 5) ∧
      (d N = F (m - 1) - 4 ∨ d N = F (m - 1) - 5)) := by
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
  dsimp only
  let Z := fun k : ℕ => 3 * k + (k - 1) / 3 - 24
  let B := fun k : ℕ => 4 * k - 34
  let ε := fun m b : ℕ => if b = Z m + 1 ∧ m % 3 ≠ 1 then 1 else 0
  have cone := full30_2 U h24 seed20 seed21
  have bDomain : ∀ m : ℕ, 21 ≤ m → B m + 2 < F (m - 2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases he : m = 21
      · subst m; norm_num [B]
      have hp := ih (m - 1) (by omega) (by omega)
      have hf := fibStep (m - 2) (by omega)
      have hh := Nat.fib_mono (show 6 ≤ m - 4 by omega)
      norm_num at hh
      dsimp [B] at *
      simp only [Nat.sub_sub, Nat.reduceAdd] at hp hf
      omega
  have separation : ∀ j : ℕ, 21 ≤ j →
      45 ≤ Z j ∧ Z j + 4 ≤ B j ∧ Z j + 5 < B (j + 1) := by
    intro j hj
    dsimp [Z, B]
    omega
  have fourCap : ∀ j r : ℕ, 21 ≤ j → r ≤ F (j - 2) → r ≤ B j →
      heightDeficit j r ≤ 4 := by
    intro j r hj hr hb
    by_contra hn
    have cc := cone j r hj hr (by omega)
    dsimp [B] at hb
    omega
  let Q := fun k : ℕ =>
    (∀ v : ℕ, v ≤ F (k - 2) → (heightDeficit k v ≤ 3 ↔ v ≤ Z k)) ∧
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
  have base : Q 21 := by
    constructor
    · intro v hv
      have rr := seed21 v hv
      norm_num only [Z, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd] at *
      exact rr.1
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
  have step : ∀ j : ℕ, 21 ≤ j → Q j → Q (j + 1) := by
    intro j hj row
    let A := F j
    let H := F (j - 1)
    let E := F (j - 2)
    let W := Z j
    have ff : F (j + 1) = A + H := by simpa [A, H] using fibStep (j + 1) (by omega)
    have fg : A = H + E := fibStep j (by omega)
    have eb : E ≤ H := Nat.fib_mono (by omega)
    have hh : 10 ≤ H := by have := Nat.le_fib_add_one (j - 1); dsimp [H]; omega
    have sz := separation j hj
    have bd := bDomain j hj
    have smallW : 45 ≤ W ∧ W + 5 < E := by
      dsimp [W, E]; omega
    have zeroSmall : ∀ q : ℕ, q ≤ 4 → heightDeficit (j - 1) q = 0 := by
      intro q hq
      have hd : q ≤ F (j - 1 - 2) := by
        have hh := Nat.le_fib_add_one (j - 3)
        simp only [Nat.sub_sub, Nat.reduceAdd]; omega
      have hp := width (j - 1) (by omega)
      exact (profiles (j - 1) q (by omega) hd).2.1.mpr (by omega)
    have image : ∀ b x : ℕ, b ≤ H → x ∈ D (F (j + 1) - b) →
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
    have tailCycles : ∀ b x : ℕ, b ≤ H → W + 5 ≤ b →
        x ∈ D (F (j + 1) - b) → x ∈ Function.periodicPts (T (F (j + 1) - b)) →
        W + 1 ≤ A - x ∧ A - x ≤ b - 4 := by
      intro b x hb hwb hx hp
      have lower : ∀ y : ℕ, y ∈ D (F (j + 1) - b) →
          y ∈ Function.periodicPts (T (F (j + 1) - b)) → W + 1 ≤ A - y := by
        intro y hy hyp
        obtain ⟨r, hrb, hre, hr⟩ := image b y hb hy hyp
        by_cases he : heightDeficit j r ≤ 4
        · omega
        · have cc := cone j r hj hre (by omega)
          have sep := separation j hj
          dsimp [Z, B, W] at *
          omega
      have lx := lower x hx hp
      have hn : 3 ≤ F (j + 1) - b := by omega
      obtain ⟨y, hy, hyp, hyx⟩ := pred _ x hn hx hp
      have ly := lower y hy hyp
      have cy := coord j b y (by omega) hb hy hyp
      dsimp only at cy
      have ey : 4 ≤ heightDeficit j (A - y) := by
        have rr := row.1 (A - y) cy.2.1
        omega
      have eyb := slack j (A - y) (by omega) cy.2.1
      have my := map j b (A - y) (by omega) hb cy.2.1 cy.1
      rw [← cy.2.2.2.1, hyx] at my
      change x = A - (b - heightDeficit j (A - y)) at my
      exact ⟨lx, by omega⟩
    have tail : ∀ b : ℕ, b ≤ H → W + 5 ≤ b → 4 ≤ heightDeficit (j + 1) b := by
      intro b hb hwb
      let N := F (j + 1) - b
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cb := tailCycles b (g N) hb hwb (orbitDomain N (d N) hn) (selected N hn)
      have cc := coord j b (g N) (by omega) hb (orbitDomain N (d N) hn) (selected N hn)
      have rr := row.1 (A - g N) cc.2.1
      have ss := split j b (by omega) hb
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at ss
      omega
    have adjacent : heightDeficit (j + 1) (W + 5) = 4 := by
      have lo := tail (W + 5) (by omega) le_rfl
      have hi := fourCap (j + 1) (W + 5) (by omega)
        (by simpa only [show j + 1 - 2 = j - 1 by omega] using (show W + 5 ≤ H by omega))
        (by dsimp [W]; omega)
      omega
    have low : ∀ b : ℕ, b ≤ W → heightDeficit (j + 1) b ≤ 3 := by
      intro b hb
      let N := F (j + 1) - b
      have hbB : b ≤ H := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cc := coord j b (g N) (by omega) hbB (orbitDomain N (d N) hn) (selected N hn)
      obtain ⟨r, hrb, hre, hr⟩ := image b (g N) hbB (orbitDomain N (d N) hn) (selected N hn)
      have er := (row.1 r hre).mpr (by omega)
      have ez := (row.1 (A - g N) cc.2.1).mpr (by omega)
      have ew := zeroSmall (b - (A - g N)) (by omega)
      have ss := split j b (by omega) hbB
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at ss
      omega
    have band : ∀ b : ℕ, W ≤ b → b ≤ W + 3 → heightDeficit (j + 1) b = 3 := by
      intro b hw hb
      let N := F (j + 1) - b
      have hbB : b ≤ H := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have cycleBand : ∀ x : ℕ, x ∈ D N → x ∈ Function.periodicPts (T N) →
          W - 3 ≤ A - x ∧ A - x ≤ W := by
        intro x hx hp
        have lower : ∀ y : ℕ, y ∈ D N → y ∈ Function.periodicPts (T N) → W - 3 ≤ A - y := by
          intro y hy hyp
          obtain ⟨r, hrb, hre, hr⟩ := image b y hbB hy hyp
          by_cases he : b = W
          · have er := (row.1 r hre).mpr (by omega); omega
          · have er : heightDeficit j r ≤ 4 := by
              exact fourCap j r hj hre (by dsimp [W] at *; omega)
            omega
        have lx := lower x hx hp
        have cx := coord j b x (by omega) hbB hx hp
        obtain ⟨y, hy, hyp, hyx⟩ := pred N x hn hx hp
        have ly := lower y hy hyp
        have cy := coord j b y (by omega) hbB hy hyp
        have er : 3 ≤ heightDeficit j (A - y) := by
          by_cases hrw : A - y ≤ W
          · have hh := row.2 (A - y) ly hrw; omega
          · have hh := row.1 (A - y) cy.2.1; omega
        have eb := slack j (A - y) (by omega) cy.2.1
        have my := map j b (A - y) (by omega) hbB cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        change x = A - (b - heightDeficit j (A - y)) at my
        exact ⟨lx, by omega⟩
      have cb := cycleBand (g N) (orbitDomain N (d N) hn) (selected N hn)
      have ez := row.2 (A - g N) cb.1 cb.2
      obtain ⟨r, hrb, hre, hr⟩ := image b (g N) hbB (orbitDomain N (d N) hn) (selected N hn)
      have er := fourCap j r hj hre (by dsimp [W] at *; omega)
      have w4 : b - (A - g N) ≤ 4 := by omega
      have ew := zeroSmall (b - (A - g N)) w4
      have ss := split j b (by omega) hbB
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at ss
      omega
    have critical : (heightDeficit (j + 1) (W + 4) = if Even A then 3 else 4) ∧
        g (F (j + 1) - (W + 4)) = if Even A then A - W else A - W - 1 := by
      let N := F (j + 1) - (W + 4)
      let L := A - W - 1
      have hb : W + 4 ≤ H := by omega
      have hn : 3 ≤ N := by dsimp [N]; omega
      have hL : 1 ≤ L := by dsimp [L]; omega
      have eLow : heightDeficit j (W + 1) = 4 := by
        have lo : 4 ≤ heightDeficit j (W + 1) := by
          have rr := row.1 (W + 1) (by omega)
          omega
        have hi := fourCap j (W + 1) hj (by omega) (by dsimp [W]; omega)
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
            exact fourCap j r hj hre (by dsimp [W] at *; omega)
          omega
        have lx := lower x hx hp
        have cx := coord j (W + 4) x (by omega) hb hx hp
        obtain ⟨y, hy, hyp, hyx⟩ := pred N x hn hx hp
        have ly := lower y hy hyp
        have cy := coord j (W + 4) y (by omega) hb hy hyp
        have er : 3 ≤ heightDeficit j (A - y) := by
          by_cases hrw : A - y ≤ W
          · have hh := row.2 (A - y) (by omega) hrw; omega
          · have hh := row.1 (A - y) cy.2.1; omega
        have eb := slack j (A - y) (by omega) cy.2.1
        have my := map j (W + 4) (A - y) (by omega) hb cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        change x = A - (W + 4 - heightDeficit j (A - y)) at my
        dsimp [L]; omega
      have hd : d N = A - 4 := by
        have hc := cap (j + 1) (W + 5) (by omega) (by
          simpa only [show j + 1 - 2 = j - 1 by omega]
            using (show W + 5 ≤ H by omega))
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
        have cb : C x ≤ H - 4 := by
          by_cases hxb : x < H
          · have hu := h.uMono x H hx.1 (by omega)
            have ua := (h.anchors (j - 1) (by omega)).1
            change U H = E at ua
            rw [ua] at hu
            have hb := (h.bounds x hx.1).2.2.1
            have eh : 4 ≤ F (j - 3) := by have := Nat.le_fib_add_one (j - 3); omega
            have fb := fibStep (j - 1) (by omega)
            simp only [Nat.sub_sub] at fb
            change H = E + F (j - 3) at fb
            omega
          · have hz : A - x ≤ E := by omega
            have rz : 4 ≤ heightDeficit j (A - x) := by
              have rr := row.1 (A - x) hz
              dsimp [L, W] at *; omega
            have cc := cap j (A - x) (by omega) hz
            have ex : A - (A - x) = x := by dsimp [L] at *; omega
            unfold heightDeficit at rz
            change 4 ≤ H - C (A - (A - x)) at rz
            rw [ex] at rz
            change C (A - (A - x)) ≤ H at cc
            rw [ex] at cc
            omega
        unfold T
        dsimp [N, L]; omega
      have highMap : ∀ x : ℕ, x ∈ D N → L + 1 ≤ x → T N x ≤ L := by
        intro x hx hxl
        by_cases he : x = L + 1
        · rw [he, highEdge]
        have cb : H - 3 ≤ C x := by
          by_cases hxa : x ≤ A
          · have hz : A - x ≤ W := by dsimp [L] at *; omega
            have rr := (row.1 (A - x) (by omega)).mpr hz
            have ex : A - (A - x) = x := by omega
            unfold heightDeficit at rr
            change H - C (A - (A - x)) ≤ 3 at rr
            rw [ex] at rr
            omega
          · have gm := goldenMono (show A + 1 ≤ x by omega)
            have ga := (h.plusOne j (by omega)).1
            change G (A + 1) = H + 1 at ga
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
    constructor
    · intro b hb
      have hbH : b ≤ H := by simpa only [show j + 1 - 2 = j - 1 by omega] using hb
      by_cases hw : b ≤ W
      · have ee := low b hw
        exact ⟨fun _ => by omega, fun _ => ee⟩
      by_cases hi : b ≤ W + 3
      · have ee := band b (by omega) hi
        exact ⟨fun _ => by omega, fun _ => by omega⟩
      by_cases hc : b = W + 4
      · rw [hc]
        by_cases he : Even A
        · rw [if_pos he] at next criticalValue
          exact ⟨fun _ => by omega, fun _ => by omega⟩
        · rw [if_neg he] at next criticalValue
          exact ⟨fun _ => by omega, fun _ => by omega⟩
      · have rr := tail b hbH (by omega)
        exact ⟨fun _ => by omega, fun _ => by omega⟩
    · intro b hlo hhi
      by_cases hi : b ≤ W + 3
      · exact band b (by omega) hi
      · have be : b = W + 4 := by omega
        have he : Even A := by
          by_contra hn
          rw [if_neg hn] at next; omega
        rw [be, criticalValue, if_pos he]
  have rows : ∀ m : ℕ, 21 ≤ m → Q m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases he : m = 21
      · subst m; exact base
      have rr := step (m - 1) (by omega) (ih (m - 1) (by omega) (by omega))
      simpa only [show m - 1 + 1 = m by omega] using rr
  have closed : ∀ m b : ℕ, 21 ≤ m → b ≤ F (m - 2) → Z m < b → b ≤ B m →
      heightDeficit m b = 4 := by
    intro m b hm hb hz hB
    have lo := (rows m hm).1 b hb
    have hi := fourCap m b hm hb hB
    omega
  have εBounds : ∀ m b, ε m b ≤ 1 := by intro m b; dsimp [ε]; split <;> omega
  have selectBand : ∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → Z m < b → b ≤ B m →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
      g N = F (m - 1) - b + 4 - ε m b ∧
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      ((g N : ℤ) - (T N (g N) : ℤ)) = -(ε m b : ℤ) ∧
      Function.minimalPeriod (T N) (g N) = 1 + ε m b := by
    intro m b hm hb hz hB
    have e4 := closed m b (by omega) hb hz hB
    obtain ⟨gz, nw, zw, zd, wd, ez, ew, wp, jump, _, _, lower,
      τ, τb, hit, before, zτ, gτ, period, _⟩ := full30_3 U h24 seed20 seed21 m b hm hb e4
    let Ω := fun r : ℕ => b - heightDeficit (m - 1) r
    have sep := separation m (by omega)
    have prevSep := separation (m - 1) (by omega)
    have small := (lower b le_rfl).1
    have fm := Nat.fib_mono (show m - 3 ≤ m - 1 by omega)
    have τeq : τ = ε m b := by
      by_cases he : b = Z m + 1 ∧ m % 3 ≠ 1
      · have εeq : ε m b = 1 := by simp [ε, he]
        have r0 : b - 4 = Z (m - 1) := by dsimp [Z] at *; omega
        have r1 : b - 3 = Z (m - 1) + 1 := by omega
        have rr := (rows (m - 1) (by omega)).2 (b - 4) (by omega) (by omega)
        have nxt : Ω (b - 4) = b - 3 := by dsimp [Ω]; rw [rr]
        have hd := (lower (b - 3) (by omega)).1
        have ee := closed (m - 1) (b - 3) (by omega) hd (by omega)
          (by dsimp [B, Z] at *; omega)
        have τpos : 0 < τ := by
          by_contra hn
          have hτ : τ = 0 := by omega
          rw [hτ] at hit
          simp only [Function.iterate_zero, id_eq] at hit
          omega
        have τle : τ ≤ 1 := by
          by_contra hn
          have hh := before 1 (by omega)
          change heightDeficit (m - 1) (Ω (b - 4)) ≠ 4 at hh
          rw [nxt, ee] at hh
          exact hh rfl
        omega
      · have εeq : ε m b = 0 := by simp [ε, he]
        have rlo : Z (m - 1) < b - 4 := by dsimp [Z] at *; omega
        have hd := (lower (b - 4) (by omega)).1
        have ee := closed (m - 1) (b - 4) (by omega) hd rlo
          (by dsimp [B] at *; omega)
        have τzero : τ = 0 := by
          by_contra hn
          have hh := before 0 (by omega)
          simp only [Function.iterate_zero, id_eq] at hh
          exact hh ee
        omega
    have zeq : F (m - 1) - g (F m - b) = b - 4 + ε m b := by
      rw [τeq] at zτ
      by_cases he : b = Z m + 1 ∧ m % 3 ≠ 1
      · have εeq : ε m b = 1 := by simp [ε, he]
        have rr := (rows (m - 1) (by omega)).2 (b - 4)
          (by dsimp [Z] at *; omega) (by dsimp [Z] at *; omega)
        rw [εeq] at zτ ⊢
        change F (m - 1) - g (F m - b) = b - heightDeficit (m - 1) (b - 4) at zτ
        rw [rr] at zτ
        dsimp [Z] at hz; omega
      · have εeq : ε m b = 0 := by simp [ε, he]
        simpa only [εeq, Function.iterate_zero, id_eq, Nat.add_zero] using zτ
    have eb := εBounds m b
    have bd := bDomain m (by omega)
    have ff := fibStep m (by omega)
    have b4 : 4 ≤ b := by have := separation m (by omega); omega
    have weq : F (m - 2) - (F m - b - g (F m - b)) = 4 - ε m b := by omega
    have jeq : ((g (F m - b) : ℤ) - (T (F m - b) (g (F m - b)) : ℤ)) =
        -(ε m b : ℤ) := by rw [weq] at jump; omega
    exact ⟨zeq, weq, by omega, gz, nw, zw, zd, wd, jeq, by omega⟩
  have nodeValues : ∀ m b : ℕ, 21 ≤ m → b ≤ F (m - 2) → Z m < b → b < B m →
      heightDeficit m b = 4 ∧ heightDeficit m (b + 1) = 4 ∧
      C (F m - b) = F (m - 1) - 4 ∧ C (F m - b - 1) = F (m - 1) - 4 ∧
      d (F m - b) = F (m - 1) - 4 := by
    intro m b hm hb hz hB
    have bd := bDomain m hm
    have e0 := closed m b hm hb hz (by omega)
    have e1 := closed m (b + 1) hm (by omega) (by omega) (by omega)
    have c0 := cap m b (by omega) hb
    have c1 := cap m (b + 1) (by omega) (by omega)
    have ff := fibStep m (by omega)
    have hn := Nat.le_fib_add_one (m - 1)
    unfold heightDeficit at e0 e1
    unfold d
    rw [show F m - b - 1 = F m - (b + 1) by omega]
    exact ⟨by unfold heightDeficit; omega, by unfold heightDeficit; omega,
      by omega, by omega, by omega⟩
  have strict : ∀ m b : ℕ, 22 ≤ m → b ≤ F (m - 2) → Z m < b → b < B m →
      let N := F m - b
      let z := F (m - 1) - g N
      let w := F (m - 2) - (N - g N)
      heightDeficit m b = 4 ∧ heightDeficit m (b + 1) = 4 ∧
      C N = F (m - 1) - 4 ∧ C (N - 1) = F (m - 1) - 4 ∧
      d N = F (m - 1) - 4 ∧ X N 0 = N - 1 ∧
      z = b - 4 + ε m b ∧ w = 4 - ε m b ∧
      g N = F (m - 1) - b + 4 - ε m b ∧
      g N = F (m - 1) - z ∧ N - g N = F (m - 2) - w ∧ z + w = b ∧
      z ≤ F (m - 3) ∧ w ≤ F (m - 4) ∧
      ((g N : ℤ) - (T N (g N) : ℤ)) = -(ε m b : ℤ) ∧
      Function.minimalPeriod (T N) (g N) = 1 + ε m b ∧
      Z (m - 1) < z ∧ z < B (m - 1) := by
    intro m b hm hb hz hB
    obtain ⟨e0, e1, c0, c1, dep⟩ := nodeValues m b (by omega) hb hz hB
    obtain ⟨zeq, weq, gform, gz, nw, zw, zd, wd, jump, period⟩ :=
      selectBand m b hm hb hz (by omega)
    have lo : Z (m - 1) < F (m - 1) - g (F m - b) := by
      rw [zeq]
      dsimp [ε]
      split <;> (dsimp [Z] at *; omega)
    have hi : F (m - 1) - g (F m - b) < B (m - 1) := by
      have eb := εBounds m b
      by_cases he : b = Z m + 1 ∧ m % 3 ≠ 1
      · dsimp [ε] at zeq
        rw [if_pos he] at zeq
        dsimp [B, Z] at *; omega
      · have ee : ε m b = 0 := by simp [ε, he]
        rw [ee] at zeq
        dsimp [B] at *; omega
    exact ⟨e0, e1, c0, c1, dep, rfl, zeq, weq, gform, gz, nw, zw, zd, wd,
      jump, period, lo, hi⟩
  have spineCore : ∀ M b₀ : ℕ, 22 ≤ M → b₀ ≤ F (M - 2) → Z M < b₀ → b₀ < B M →
      ∀ s : ℕ, s ≤ M - 21 →
        21 ≤ M - s ∧ g^[s] (F M - b₀) = F (M - s) - (F (M - s) - g^[s] (F M - b₀)) ∧
        F (M - s) - g^[s] (F M - b₀) ≤ F (M - s - 2) ∧
        Z (M - s) < F (M - s) - g^[s] (F M - b₀) ∧
        F (M - s) - g^[s] (F M - b₀) < B (M - s) := by
    intro M b₀ hM hb₀ hz₀ hB₀ s
    induction s with
    | zero =>
      intro hs
      have ff := fibStep M (by omega)
      simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
      have coord0 : F M - (F M - b₀) = b₀ := by omega
      rw [coord0]
      exact ⟨by omega, rfl, hb₀, hz₀, hB₀⟩
    | succ s ih =>
      intro hs
      obtain ⟨hm, coordS, hb, hz, hB⟩ := ih (by omega)
      have hm22 : 22 ≤ M - s := by omega
      obtain ⟨_, _, _, _, _, _, _, _, _, gz, _, _, zd, _, _, _, lo, hi⟩ :=
        strict (M - s) (F (M - s) - g^[s] (F M - b₀)) hm22 hb hz hB
      rw [← coordS] at gz zd lo hi
      have order : M - (s + 1) = M - s - 1 := by omega
      simp only [Function.iterate_succ_apply', order]
      exact ⟨by omega, gz, by simpa only [Nat.sub_sub] using zd, lo, hi⟩
  refine ⟨bDomain, closed, strict, ?_, ?_, ?_, ?_⟩
  · intro M b₀ hM hb₀ hz₀ hB₀
    constructor
    · intro s hs
      obtain ⟨hm, coordS, hb, hz, hB⟩ := spineCore M b₀ hM hb₀ hz₀ hB₀ s hs
      have bd := bDomain (M - s) hm
      obtain ⟨e0, e1, c0, c1, dep⟩ := nodeValues (M - s)
        (F (M - s) - g^[s] (F M - b₀)) hm hb hz hB
      rw [← coordS] at c0 c1 dep
      exact ⟨hm, coordS, hb, hz, hB, by omega, e0, e1, c0, c1, dep⟩
    · intro s hs
      obtain ⟨hm, coordS, hb, hz, hB⟩ := spineCore M b₀ hM hb₀ hz₀ hB₀ s (by omega)
      obtain ⟨zeq, weq, gform, _, _, _, _, _, jump, period⟩ := selectBand (M - s)
        (F (M - s) - g^[s] (F M - b₀)) (by omega) hb hz (by omega)
      rw [← coordS] at zeq weq gform jump period
      have order : M - (s + 1) = M - s - 1 := by omega
      simp only [Function.iterate_succ_apply', order]
      exact ⟨True.intro, True.intro, True.intro, zeq, weq, gform, jump, period⟩
  · intro m b hm hb hz hB hB2
    change Z m < b at hz
    change b < B m at hB
    change b ≤ B m - 2 at hB2
    have sep := separation m (by omega)
    have bd := bDomain m (by omega)
    have ff := fibStep m (by omega)
    obtain ⟨_, _, c0, c1, dep⟩ := nodeValues m b (by omega) hb hz hB
    obtain ⟨_, _, _, c2, dep1⟩ := nodeValues m (b + 1) (by omega) (by omega) (by omega) (by omega)
    have coord1 : F m - (b + 1) = F m - b - 1 := by omega
    rw [coord1] at dep1
    obtain ⟨_, weq, gform, gz, _, _, zd, _, _, period, lo, hi⟩ :=
      (strict m b hm hb hz hB).2.2.2.2.2.2
    obtain ⟨_, w1, g1, _, _, _, _, _, _, p1⟩ :=
      selectBand m (b + 1) hm (by omega) (by omega) (by omega)
    have ε1 : ε m (b + 1) = 0 := by
      have he : ¬ (b + 1 = Z m + 1 ∧ m % 3 ≠ 1) := by omega
      simp only [ε, if_neg he]
    rw [ε1, coord1] at w1 g1 p1
    have child := nodeValues (m - 1) (F (m - 1) - g (F m - b)) (by omega)
      zd lo hi
    rw [← gz] at child
    obtain ⟨_, _, _, childC, childD⟩ := child
    simp only [Nat.sub_sub, Nat.reduceAdd] at childC childD
    have eb := εBounds m b
    have adj : g (F m - b - 1) = F (m - 1) - b + 3 := by omega
    have ord : g (F m - b - 1) ≤ g (F m - b) := by omega
    have diff : g (F m - b) - g (F m - b - 1) = 1 - ε m b := by omega
    refine ⟨dep, dep1, c0, c1, adj, ord, diff, childD, childC, ?_⟩
    intro he
    change ε m b = 1 at he
    rw [he] at weq gform period
    exact ⟨by omega, by omega, w1, by omega, by omega⟩
  · intro M hM
    have sep := separation M (by omega)
    have bd := bDomain M (by omega)
    have hb₀ : Z M + 1 ≤ F (M - 2) := by omega
    have hz₀ : Z M < Z M + 1 := by omega
    have hB₀ : Z M + 1 < B M := by omega
    have criticalCoord : ∀ s : ℕ, s ≤ M - 21 →
        F (M - s) - g^[s] (F M - (Z M + 1)) = Z (M - s) + 1 := by
      intro s
      induction s with
      | zero =>
        intro hs
        have ff := fibStep M (by omega)
        simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
        omega
      | succ s ih =>
        intro hs
        obtain ⟨hm, coordS, hb, hz, hB⟩ := spineCore M (Z M + 1) hM hb₀ hz₀ hB₀ s (by omega)
        obtain ⟨zeq, _, _, _, _, _, _, _, _, _⟩ := selectBand (M - s)
          (F (M - s) - g^[s] (F M - (Z M + 1))) (by omega) hb hz (by omega)
        rw [← coordS] at zeq
        rw [ih (by omega)] at zeq
        simp only [Function.iterate_succ_apply', show M - (s + 1) = M - s - 1 by omega]
        rw [zeq]
        dsimp [ε]
        split <;> (dsimp [Z] at *; omega)
    refine ⟨hb₀, hz₀, hB₀, criticalCoord, ?_⟩
    intro s hs
    obtain ⟨hm, coordS, hb, hz, hB⟩ := spineCore M (Z M + 1) hM hb₀ hz₀ hB₀ s (by omega)
    obtain ⟨_, _, _, _, _, _, _, _, jump, _⟩ := selectBand (M - s)
      (F (M - s) - g^[s] (F M - (Z M + 1))) (by omega) hb hz (by omega)
    rw [← coordS, criticalCoord s (by omega)] at jump
    dsimp [ε] at jump
    by_cases he : (M - s) % 3 ≠ 1
    · simp only [true_and, if_pos he, Nat.cast_one] at jump
      rw [jump]
      norm_num [he]
    · simp only [true_and, if_neg he, Nat.cast_zero, neg_zero] at jump
      rw [jump]
      norm_num [he]
  · intro m hm
    have bd := bDomain m (by omega)
    have sep := separation m (by omega)
    have ff := fibStep m (by omega)
    have eb : ε m (B m) = 0 := by simp [ε]; dsimp [Z, B] at *; omega
    obtain ⟨zeq, weq, _, gz, nw, _, _, _, jump, period⟩ :=
      selectBand m (B m) hm (by omega) (by omega) le_rfl
    rw [eb] at zeq weq jump period
    have ze : F (m - 1) - g (F m - B m) = B (m - 1) := by dsimp [B] at *; omega
    have e0 := closed m (B m) (by omega) (by omega) (by omega) le_rfl
    have lo := (rows m (by omega)).1 (B m + 1) (by omega)
    have hi : heightDeficit m (B m + 1) ≤ 5 := by
      by_contra hn
      have cc := cone m (B m + 1) (by omega) (by omega) (by omega)
      dsimp [B] at *; omega
    have alt : heightDeficit m (B m + 1) = 4 ∨ heightDeficit m (B m + 1) = 5 := by omega
    have ca := cap m (B m + 1) (by omega) (by omega)
    have da : d (F m - B m) = F (m - 1) - 4 ∨ d (F m - B m) = F (m - 1) - 5 := by
      have hp := Nat.le_fib_add_one (m - 1)
      unfold heightDeficit at alt
      unfold d
      rw [show F m - B m - 1 = F m - (B m + 1) by omega]
      omega
    rw [ze] at gz
    rw [weq] at nw
    exact ⟨by change B m ≤ F (m - 2); omega, e0, ze, by simpa using weq, gz, by simpa using nw,
      by simpa using period, by simpa using jump, alt, da⟩

end D5.S1.Recurrence.Invariants.CloitreActualDeficitFourBand
