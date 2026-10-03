/- GID: D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualLeftPlateau
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional maximal actual left Fibonacci platforms, cones and boundary phases. -/

import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
/-- The deficit below the preceding Fibonacci height. -/
def heightDeficit (m t : ℕ) : ℕ := F (m - 1) - C (F m - t)
/-- The natural floor of the proposed left platform width. -/
def platformWidth (m : ℕ) : ℕ := (2 * m - 9) / 3
/-- The complete inherited source hypotheses and the negative-offset interface. -/
structure Hyp24_1 (U : ℕ → ℕ) : Prop extends Hyp21_1 U where
  predecessor : ∀ j : ℕ, 5 ≤ j → C (F j - 1) = F (j - 1)
  negativeInvariant : ∀ j b : ℕ, 6 ≤ j → b ≤ F (j - 1) →
    Set.MapsTo (T (F (j + 1) - b))
      (Set.Icc (F j - b) (F j) ∩ D (F (j + 1) - b))
      (Set.Icc (F j - b) (F j) ∩ D (F (j + 1) - b))
  negativeCapture : ∀ j b x : ℕ, 6 ≤ j → b ≤ F (j - 1) →
    x ∈ D (F (j + 1) - b) → ∃ i : ℕ,
      (T (F (j + 1) - b))^[i] x ∈
        Set.Icc (F j - b) (F j) ∩ D (F (j + 1) - b)
  intersection : ∀ j b x : ℕ, 6 ≤ j → b ≤ F (j - 1) →
    x ∈ D (F (j + 1) - b) → x ∈ Function.periodicPts (T (F (j + 1) - b)) →
      max (F (j - 1)) (F j - b) ≤ x ∧
      x ≤ min (F j) (F j + F (j - 3) - b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2400000 in
-- Literal prefix base rows and simultaneous orbit induction need these elaboration bounds.
/-- The complete natural closed-block left platform, cone, actual routes and boundary phase. -/
theorem full24_3 (U : ℕ → ℕ) (h24 : Hyp24_1 U) :
    (∀ m t : ℕ, 8 ≤ m → t ≤ F (m - 2) →
      C (F m - t) ≤ F (m - 1) ∧
      (heightDeficit m t = 0 ↔ t ≤ platformWidth m) ∧
      (platformWidth m < t → 1 ≤ heightDeficit m t ∧
        heightDeficit m t ≤ max 1 (t - platformWidth m - 1))) ∧
    (∀ W m : ℕ, max 8 ((3 * W + 10) / 2) ≤ m →
      ∀ t : ℕ, t ≤ W → C (F m - t) = F (m - 1)) ∧
    (∀ j b : ℕ, 9 ≤ j → b ≤ F (j - 1) →
      let N := F (j + 1) - b
      let z := F j - g N
      let w := F (j - 1) - (N - g N)
      g N = F j - z ∧ N - g N = F (j - 1) - w ∧ z + w = b ∧
      z ≤ F (j - 2) ∧ w ≤ F (j - 3) ∧
      (heightDeficit (j + 1) b = 0 ↔
        (b ≤ platformWidth j ∧ z = b ∧ w = 0) ∨
        (b = platformWidth j + 1 ∧ Odd (F j) ∧ z = platformWidth j ∧ w = 1))) ∧
    (∀ j : ℕ, 9 ≤ j →
      let N := F (j + 1) - (platformWidth j + 1)
      Function.minimalPeriod (T N) (g N) = 2 ∧ d N = F j - 1 ∧
      g N = if Odd (F j) then F j - platformWidth j else F j - platformWidth j - 1) := by
  classical
  let h := h24.toHyp21_1
  let Row := fun m : ℕ => ∀ t : ℕ, t ≤ F (m - 2) →
    (heightDeficit m t = 0 ↔ t ≤ platformWidth m) ∧
    (platformWidth m < t → 1 ≤ heightDeficit m t ∧
      heightDeficit m t ≤ max 1 (t - platformWidth m - 1))
  let Route := fun j : ℕ => ∀ b : ℕ, b ≤ F (j - 1) →
    let N := F (j + 1) - b
    let z := F j - g N
    let w := F (j - 1) - (N - g N)
    g N = F j - z ∧ N - g N = F (j - 1) - w ∧ z + w = b ∧
    z ≤ F (j - 2) ∧ w ≤ F (j - 3) ∧
    (heightDeficit (j + 1) b = 0 ↔
      (b ≤ platformWidth j ∧ z = b ∧ w = 0) ∨
      (b = platformWidth j + 1 ∧ Odd (F j) ∧ z = platformWidth j ∧ w = 1))
  let Boundary := fun j : ℕ =>
    let N := F (j + 1) - (platformWidth j + 1)
    Function.minimalPeriod (T N) (g N) = 2 ∧ d N = F j - 1 ∧
    g N = if Odd (F j) then F j - platformWidth j else F j - platformWidth j - 1
  obtain ⟨orbitDomain, recurrence⟩ := actual_foundations
  have fibStep : ∀ m : ℕ, 2 ≤ m → F m = F (m - 1) + F (m - 2) := by
    intro m hm
    have hf := Nat.fib_add_two (n := m - 2)
    rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hf
    omega
  have cap : ∀ m t : ℕ, 8 ≤ m → t ≤ F (m - 2) → C (F m - t) ≤ F (m - 1) := by
    intro m t hm ht
    have hf := fibStep m (by omega)
    have hp := Nat.le_fib_add_one (m - 1)
    have hn : 1 ≤ F m - t := by omega
    have hb := (h.bounds (F m - t) hn).2.2.1
    have hu := h.uMono (F m - t) (F m) hn (by omega)
    rw [(h.anchors m (by omega)).1] at hu
    omega
  have goldenMono : Monotone G := by
    intro a b hab
    unfold D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.add_le_add_right hab 1
    · exact le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have inv : ∀ N : ℕ, 3 ≤ N → Set.MapsTo (T N) (D N) (D N) := by
    intro N hN x hx
    have hb := h.bounds x hx.1
    change 1 ≤ x ∧ x ≤ N - 1 at hx
    change 1 ≤ N - C x ∧ N - C x ≤ N - 1
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
  have pred : ∀ N x : ℕ, 3 ≤ N → x ∈ D N → x ∈ Function.periodicPts (T N) →
      ∃ y : ℕ, y ∈ D N ∧ y ∈ Function.periodicPts (T N) ∧ T N y = x := by
    intro N x hN hx ⟨r, hr, hp⟩
    refine ⟨(T N)^[r - 1] x, (inv N hN).iterate (r - 1) hx,
      ⟨r, hr, hp.apply_iterate (r - 1)⟩, ?_⟩
    rw [← Function.iterate_succ_apply' (T N) (r - 1) x, show (r - 1).succ = r by omega]
    exact hp.eq
  have widthBounds : ∀ m : ℕ, 8 ≤ m →
      2 ≤ platformWidth m ∧ platformWidth m ≤ m - 6 ∧ platformWidth m ≤ F (m - 2) := by
    intro m hm
    unfold platformWidth
    have := Nat.le_fib_add_one (m - 2)
    omega
  have widthNext : ∀ j : ℕ, 9 ≤ j →
      platformWidth (j + 1) = platformWidth j + if Odd (F j) then 1 else 0 := by
    intro j hj
    have hd := D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 3 j (by omega)
    norm_num at hd
    have he : Even (F j) ↔ j % 3 = 0 := by
      rw [even_iff_two_dvd, hd, Nat.dvd_iff_mod_eq_zero]
    by_cases ho : Odd (F j)
    · rw [if_pos ho]
      have hn : j % 3 ≠ 0 := by
        intro hh; exact (Nat.not_even_iff_odd.mpr ho) (he.mpr hh)
      have hr : j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases hr with hr | hr <;> unfold platformWidth <;> omega
    · rw [if_neg ho]
      have hh : j % 3 = 0 := he.mp (by simpa using ho)
      unfold platformWidth
      omega
  have base8 : Row 8 := by
    intro t ht
    norm_num at ht
    interval_cases t <;> decide +kernel
  have base9 : Row 9 := by
    intro t ht
    norm_num at ht
    interval_cases t <;> decide +kernel
  have step : ∀ j : ℕ, 9 ≤ j → Row j → Row (j - 1) →
      Row (j + 1) ∧ Route j ∧ Boundary j := by
    intro j hj row rowPrev
    let A := F j
    let B := F (j - 1)
    let E := F (j - 2)
    let H := F (j - 3)
    let p := platformWidth j
    have fAB : F (j + 1) = A + B := by simpa [A, B] using fibStep (j + 1) (by omega)
    have fBE : A = B + E := fibStep j (by omega)
    have hHE : H ≤ E := by
      dsimp [H, E]
      exact Nat.fib_mono (by omega)
    have fEH : B = E + H := by simpa [B, E, H, Nat.sub_sub] using fibStep (j - 1) (by omega)
    have hB : 6 ≤ B := by have := Nat.le_fib_add_one (j - 1); dsimp [B]; omega
    have hH : j - 4 ≤ H := by have := Nat.le_fib_add_one (j - 3); dsimp [H]; omega
    have hp := widthBounds j (by omega)
    have hprev := widthBounds (j - 1) (by omega)
    have psmall : 2 ≤ p ∧ p + 2 ≤ H ∧ p + 2 < B := by dsimp [p]; omega
    have coord : ∀ b x : ℕ, b ≤ B → x ∈ D (F (j + 1) - b) →
        x ∈ Function.periodicPts (T (F (j + 1) - b)) →
        let z := A - x
        z ≤ b ∧ z ≤ E ∧ b - z ≤ H ∧ x = A - z ∧
        F (j + 1) - b - x = B - (b - z) := by
      intro b x hb hx hper
      have hi := h24.intersection j b x (by omega) hb hx hper
      have hl1 := le_of_max_le_left hi.1
      have hl2 := le_of_max_le_right hi.1
      have hu1 := le_trans hi.2 (min_le_left _ _)
      have hu2 := le_trans hi.2 (min_le_right _ _)
      dsimp [A, B, H] at fAB fBE fEH ⊢
      omega
    have map : ∀ b z : ℕ, b ≤ B → z ≤ E → z ≤ b →
        T (F (j + 1) - b) (A - z) = A - (b - heightDeficit j z) := by
      intro b z hb hz hzb
      have hc := cap j z (by omega) hz
      have rl := row z hz
      have hd : heightDeficit j z ≤ b := by
        by_cases hzp : z ≤ p
        · have rr := rl.1.mpr hzp; omega
        · have rr := (rl.2 (by omega)).2
          have hm : max 1 (z - platformWidth j - 1) ≤ b := by
            apply max_le <;> dsimp [p] at * <;> omega
          omega
      unfold T heightDeficit at *
      dsimp [A, B] at fAB fBE ⊢
      omega
    have split : ∀ b : ℕ, b ≤ B →
        let N := F (j + 1) - b
        let z := A - g N
        let w := b - z
        heightDeficit (j + 1) b = heightDeficit j z + heightDeficit (j - 1) w := by
      intro b hb
      let N := F (j + 1) - b
      have hN : 3 ≤ N := by dsimp [N]; omega
      have hc := coord b (g N) hb (orbitDomain N (d N) hN) (selected N hN)
      have hs := recurrence N hN
      have hh1 := cap j (A - g N) (by omega) hc.2.1
      have hh2 := cap (j - 1) (b - (A - g N)) (by omega) hc.2.2.1
      dsimp only at hc
      have e1 := congrArg C hc.2.2.2.1
      have e2 := congrArg C hc.2.2.2.2
      change C N = C (g N) + C (N - g N) at hs
      rw [e1, e2] at hs
      change C (A - (A - g N)) ≤ B at hh1
      simp only [Nat.sub_sub] at hh2
      change C (B - (b - (A - g N))) ≤ E at hh2
      dsimp only
      unfold heightDeficit
      simp only [Nat.add_sub_cancel, Nat.sub_sub]
      change A - C N = (B - C (A - (A - g N))) +
        (E - C (B - (b - (A - g N))))
      omega
    have cycBounds : ∀ b x : ℕ, b ≤ B → p + 2 ≤ b →
        x ∈ D (F (j + 1) - b) → x ∈ Function.periodicPts (T (F (j + 1) - b)) →
        p + 1 ≤ A - x ∧ A - x ≤ b - 1 := by
      intro b x hb hpb hx hper
      have hN : 3 ≤ F (j + 1) - b := by omega
      obtain ⟨y, hy, hyp, hyx⟩ := pred _ x hN hx hper
      have cy := coord b y hb hy hyp
      have cx := coord b x hb hx hper
      have bound : ∀ z : ℕ, z ≤ E → z ≤ b → heightDeficit j z ≤ b - p - 1 := by
        intro z hz hzb
        have rr := row z hz
        by_cases hzp : z ≤ p
        · have hzero := rr.1.mpr hzp; omega
        · have hc := (rr.2 (by omega)).2
          have hm : max 1 (z - platformWidth j - 1) ≤ b - p - 1 := by
            apply max_le <;> dsimp [p] at * <;> omega
          omega
      have ey := bound (A - y) cy.2.1 cy.1
      have my := map b (A - y) hb cy.2.1 cy.1
      rw [← cy.2.2.2.1, hyx] at my
      have lower : p + 1 ≤ A - x := by omega
      obtain ⟨v, hv, hvp, hvx⟩ := pred _ y hN hy hyp
      have cv := coord b v hb hv hvp
      have ev := bound (A - v) cv.2.1 cv.1
      have mv := map b (A - v) hb cv.2.1 cv.1
      rw [← cv.2.2.2.1, hvx] at mv
      have ly : p + 1 ≤ A - y := by omega
      have eypos : 1 ≤ heightDeficit j (A - y) := (row (A - y) cy.2.1).2 (by omega) |>.1
      exact ⟨lower, by omega⟩
    have small : ∀ b : ℕ, b ≤ p →
        g (F (j + 1) - b) = A - b ∧ heightDeficit (j + 1) b = 0 := by
      intro b hb
      have hbB : b ≤ B := by omega
      let N := F (j + 1) - b
      have hN : 3 ≤ N := by dsimp [N]; omega
      obtain ⟨y, hy, hyp, hyx⟩ := pred N (g N) hN (orbitDomain N (d N) hN) (selected N hN)
      have cy := coord b y hbB hy hyp
      have hz := (row (A - y) cy.2.1).1.mpr (by omega)
      have mm := map b (A - y) hbB cy.2.1 cy.1
      rw [← cy.2.2.2.1, hyx, hz] at mm
      have hg : g N = A - b := by simpa using mm
      have cz := coord b (g N) hbB (orbitDomain N (d N) hN) (selected N hN)
      have sz := split b hbB
      have rz := (row b (by omega)).1.mpr hb
      have rw0 := (rowPrev 0 (by omega)).1.mpr (by omega)
      dsimp only at sz
      have gz : A - g N = b := by omega
      change g N = A - b ∧ heightDeficit (j + 1) b = 0
      refine ⟨hg, ?_⟩
      change heightDeficit (j + 1) b = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (b - (A - g N)) at sz
      rw [gz, Nat.sub_self, rz, rw0] at sz
      exact sz
    have adjacent : heightDeficit (j + 1) (p + 2) = 1 := by
      have hb : p + 2 ≤ B := by omega
      let N := F (j + 1) - (p + 2)
      have hN : 3 ≤ N := by dsimp [N]; omega
      have cb := cycBounds (p + 2) (g N) hb le_rfl (orbitDomain N (d N) hN) (selected N hN)
      have cc := coord (p + 2) (g N) hb (orbitDomain N (d N) hN) (selected N hN)
      have hz : A - g N = p + 1 := by omega
      have rr := row (p + 1) (by omega)
      have ee : heightDeficit j (p + 1) = 1 := by
        have hrr := rr.2 (by omega)
        have hm : max 1 (p + 1 - platformWidth j - 1) = 1 := by dsimp [p]; omega
        omega
      have rw1 := (rowPrev 1 (by omega)).1.mpr (by omega)
      have ss := split (p + 2) hb
      change heightDeficit (j + 1) (p + 2) = heightDeficit j (A - g N) +
        heightDeficit (j - 1) (p + 2 - (A - g N)) at ss
      rw [hz, show p + 2 - (p + 1) = 1 by omega, ee, rw1] at ss
      simpa using ss
    have critical : Boundary j ∧
        heightDeficit (j + 1) (p + 1) = if Odd A then 0 else 1 := by
      let N := F (j + 1) - (p + 1)
      let L := A - (p + 1)
      have hb : p + 1 ≤ B := by omega
      have hN : 3 ≤ N := by dsimp [N]; omega
      have hL : 1 ≤ L := by dsimp [L]; omega
      have unit : heightDeficit j (p + 1) = 1 := by
        have rr := (row (p + 1) (by omega)).2 (by omega)
        have mm : max 1 (p + 1 - platformWidth j - 1) = 1 := by dsimp [p]; omega
        omega
      have lowEdge : T N L = L + 1 := by
        have mm := map (p + 1) (p + 1) hb (by omega) le_rfl
        rw [unit] at mm
        dsimp [N, L] at *
        omega
      have highEdge : T N (L + 1) = L := by
        have rz := (row p (by omega)).1.mpr le_rfl
        have mm := map (p + 1) p hb (by omega) (by omega)
        rw [rz] at mm
        have aa : A - p = L + 1 := by dsimp [L]; omega
        rw [aa] at mm
        exact mm
      have pair : ∀ x : ℕ, x ∈ D N → x ∈ Function.periodicPts (T N) →
          x = L ∨ x = L + 1 := by
        intro x hx hpX
        obtain ⟨y, hy, hpY, hyx⟩ := pred N x hN hx hpX
        have cy := coord (p + 1) y hb hy hpY
        have my := map (p + 1) (A - y) hb cy.2.1 cy.1
        rw [← cy.2.2.2.1, hyx] at my
        by_cases hz : A - y ≤ p
        · have rz := (row (A - y) cy.2.1).1.mpr hz
          rw [rz] at my
          exact Or.inl (by dsimp [L]; omega)
        · have zz : A - y = p + 1 := by omega
          rw [zz, unit] at my
          exact Or.inr (by dsimp [L]; omega)
      have hd : d N = A - 1 := by
        have hc := cap (j + 1) (p + 2) (by omega) (by
          simpa only [show j + 1 - 2 = j - 1 by omega] using (show p + 2 ≤ B by omega))
        unfold heightDeficit at adjacent
        have ee : N - 1 = F (j + 1) - (p + 2) := by dsimp [N]; omega
        unfold d
        rw [ee]
        simp only [Nat.add_sub_cancel] at adjacent hc
        omega
      have lowMap : ∀ x : ℕ, x ∈ D N → x ≤ L → L + 1 ≤ T N x := by
        intro x hx hxl
        by_cases he : x = L
        · rw [he, lowEdge]
        have hc : C x ≤ B - 1 := by
          by_cases hxb : x < B
          · have hu := h.uMono x B hx.1 (by omega)
            have ua := (h.anchors (j - 1) (by omega)).1
            change U B = E at ua
            rw [ua] at hu
            have cb := (h.bounds x hx.1).2.2.1
            omega
          · have hz : A - x ≤ E := by omega
            have rz := (row (A - x) hz).2 (by dsimp [L] at *; omega) |>.1
            have cc := cap j (A - x) (by omega) hz
            have ex : A - (A - x) = x := by dsimp [L] at *; omega
            unfold heightDeficit at rz cc
            change 1 ≤ B - C (A - (A - x)) at rz
            rw [ex] at rz
            omega
        unfold T
        dsimp [N, L]
        omega
      have highMap : ∀ x : ℕ, x ∈ D N → L + 1 ≤ x → T N x ≤ L := by
        intro x hx hxl
        by_cases hxa : x ≤ A
        · have hz : A - x ≤ p := by dsimp [L] at *; omega
          have rz := (row (A - x) (by omega)).1.mpr hz
          have cc := cap j (A - x) (by omega) (by omega)
          have ex : A - (A - x) = x := by omega
          unfold heightDeficit at rz
          change B - C (A - (A - x)) = 0 at rz
          change C (A - (A - x)) ≤ B at cc
          rw [ex] at rz cc
          unfold T
          dsimp [N, L]
          omega
        · have gm := goldenMono (show A + 1 ≤ x by omega)
          have ga := (h.plusOne j (by omega)).1
          change G (A + 1) = B + 1 at ga
          rw [ga] at gm
          have cb := (h.bounds x hx.1).2.1
          unfold T
          dsimp [N, L]
          omega
      have parity : ∀ i : ℕ, (i % 2 = 0 → L + 1 ≤ X N i) ∧
          (i % 2 = 1 → X N i ≤ L) := by
        intro i
        induction i with
        | zero =>
          change (0 % 2 = 0 → L + 1 ≤ N - 1) ∧ (0 % 2 = 1 → N - 1 ≤ L)
          dsimp [N, L]
          omega
        | succ i ih =>
          have hx := orbitDomain N i hN
          have xe : X N (i + 1) = T N (X N i) := by
            unfold X
            rw [Function.iterate_succ_apply']
          constructor
          · intro hi
            rw [xe]
            exact lowMap _ hx (ih.2 (by omega))
          · intro hi
            rw [xe]
            exact highMap _ hx (ih.1 (by omega))
      have gp := pair (g N) (orbitDomain N (d N) hN) (selected N hN)
      have hpD := parity (d N)
      have phase : g N = if Odd A then L + 1 else L := by
        by_cases ho : Odd A
        · rw [if_pos ho]
          have he : d N % 2 = 0 := by
            rw [Nat.odd_iff] at ho
            omega
          have hh := hpD.1 he
          change L + 1 ≤ g N at hh
          omega
        · rw [if_neg ho]
          have he : d N % 2 = 1 := by
            have heA : A % 2 = 0 := by
              have : Even A := by simpa using ho
              rwa [Nat.even_iff] at this
            omega
          have hh := hpD.2 he
          change g N ≤ L at hh
          omega
      have per2 : Function.IsPeriodicPt (T N) 2 (g N) := by
        change T N (T N (g N)) = g N
        rcases gp with he | he <;> rw [he]
        · rw [lowEdge, highEdge]
        · rw [highEdge, lowEdge]
      have nf : ¬ Function.IsFixedPt (T N) (g N) := by
        intro hf
        change T N (g N) = g N at hf
        rcases gp with he | he <;> rw [he] at hf
        · rw [lowEdge] at hf; omega
        · rw [highEdge] at hf; omega
      have mp := Function.minimalPeriod_eq_prime per2 nf
      have value : heightDeficit (j + 1) (p + 1) = if Odd A then 0 else 1 := by
        have ss := split (p + 1) hb
        change heightDeficit (j + 1) (p + 1) = heightDeficit j (A - g N) +
          heightDeficit (j - 1) (p + 1 - (A - g N)) at ss
        by_cases ho : Odd A
        · rw [if_pos ho] at phase ⊢
          have zz : A - g N = p := by dsimp [L] at *; omega
          have rr := (row p (by omega)).1.mpr le_rfl
          have rp := (rowPrev 1 (by omega)).1.mpr (by omega)
          rw [zz, show p + 1 - p = 1 by omega, rr, rp] at ss
          exact ss
        · rw [if_neg ho] at phase ⊢
          have zz : A - g N = p + 1 := by dsimp [L] at *; omega
          have rp := (rowPrev 0 (by omega)).1.mpr (by omega)
          rw [zz, Nat.sub_self, unit, rp] at ss
          exact ss
      refine ⟨⟨mp, hd, ?_⟩, value⟩
      change g N = if Odd A then A - p else A - p - 1
      rw [phase]
      split <;> dsimp [L] <;> omega
    have newRow : Row (j + 1) := by
      intro b hb
      have hbB : b ≤ B := by
        simpa only [show j + 1 - 2 = j - 1 by omega] using hb
      have next := widthNext j hj
      change platformWidth (j + 1) = p + if Odd A then 1 else 0 at next
      have nextBounds : p ≤ platformWidth (j + 1) ∧ platformWidth (j + 1) ≤ p + 1 := by
        split at next <;> omega
      by_cases hbp : b ≤ p
      · have vv := (small b hbp).2
        refine ⟨⟨fun _ => by omega, fun _ => vv⟩, ?_⟩
        intro hn; omega
      by_cases hb1 : b = p + 1
      · rw [hb1]
        have vv := critical.2
        by_cases ho : Odd A
        · rw [if_pos ho] at vv next
          refine ⟨⟨fun _ => by omega, fun _ => vv⟩, ?_⟩
          intro hn; omega
        · rw [if_neg ho] at vv next
          refine ⟨⟨fun hh => by omega, fun hh => by omega⟩, ?_⟩
          intro hn
          refine ⟨by omega, ?_⟩
          have := le_max_left 1 (p + 1 - platformWidth (j + 1) - 1)
          omega
      by_cases hb2 : b = p + 2
      · rw [hb2]
        refine ⟨⟨fun hh => by omega, fun hh => by omega⟩, ?_⟩
        intro hn
        refine ⟨by omega, ?_⟩
        have := le_max_left 1 (p + 2 - platformWidth (j + 1) - 1)
        omega
      have hlarge : p + 3 ≤ b := by omega
      let N := F (j + 1) - b
      let z := A - g N
      let w := b - z
      have hN : 3 ≤ N := by dsimp [N]; omega
      have cc := coord b (g N) hbB (orbitDomain N (d N) hN) (selected N hN)
      have cb := cycBounds b (g N) hbB (by omega) (orbitDomain N (d N) hN) (selected N hN)
      change z ≤ b ∧ z ≤ E ∧ w ≤ H ∧ _ at cc
      change p + 1 ≤ z ∧ z ≤ b - 1 at cb
      have zw : z + w = b := by dsimp [w]; omega
      have ss := split b hbB
      change heightDeficit (j + 1) b = heightDeficit j z + heightDeficit (j - 1) w at ss
      have rz := row z cc.2.1
      have rw := rowPrev w (by simpa only [Nat.sub_sub] using cc.2.2.1)
      have positive : 1 ≤ heightDeficit (j + 1) b := by
        have ee := (rz.2 (by omega)).1
        omega
      have cone : heightDeficit (j + 1) b ≤ b - p - 2 := by
        by_cases hz : p + 2 ≤ z
        · have ez := (rz.2 (by omega)).2
          have mz : max 1 (z - platformWidth j - 1) = z - p - 1 := by dsimp [p]; omega
          rw [mz] at ez
          have ew : heightDeficit (j - 1) w ≤ w - 1 := by
            by_cases hw : w ≤ platformWidth (j - 1)
            · have ee := rw.1.mpr hw; omega
            · have ee := (rw.2 (by omega)).2
              have mm : max 1 (w - platformWidth (j - 1) - 1) ≤ w - 1 := by
                apply max_le <;> omega
              omega
          omega
        · have ze : z = p + 1 := by omega
          have ez := (rz.2 (by omega))
          have mz : max 1 (z - platformWidth j - 1) = 1 := by dsimp [p] at *; omega
          have ez1 : heightDeficit j z = 1 := by omega
          have ew : heightDeficit (j - 1) w ≤ w - 2 := by
            by_cases hw : w ≤ platformWidth (j - 1)
            · have ee := rw.1.mpr hw; omega
            · have ee := (rw.2 (by omega)).2
              have mm : max 1 (w - platformWidth (j - 1) - 1) ≤ w - 2 := by
                apply max_le <;> omega
              omega
          omega
      refine ⟨⟨fun hh => by omega, fun hh => by omega⟩, ?_⟩
      intro hn
      refine ⟨positive, ?_⟩
      have ee : b - p - 2 ≤ b - platformWidth (j + 1) - 1 := by omega
      exact le_trans cone (le_trans ee (le_max_right _ _))
    have routes : Route j := by
      intro b hb
      let N := F (j + 1) - b
      let z := A - g N
      let w := B - (N - g N)
      have hN : 3 ≤ N := by dsimp [N]; omega
      have cc := coord b (g N) hb (orbitDomain N (d N) hN) (selected N hN)
      change z ≤ b ∧ z ≤ E ∧ b - z ≤ H ∧ g N = A - z ∧ N - g N = B - (b - z) at cc
      have hzg : g N ≤ A := by omega
      have hw : w = b - z := by dsimp [w]; omega
      have hg : g N = A - z := cc.2.2.2.1
      have hcg : N - g N = B - w := by rw [hw]; exact cc.2.2.2.2
      change g N = A - z ∧ N - g N = B - w ∧ z + w = b ∧ z ≤ E ∧ w ≤ H ∧
        (heightDeficit (j + 1) b = 0 ↔
          (b ≤ p ∧ z = b ∧ w = 0) ∨
          (b = p + 1 ∧ Odd A ∧ z = p ∧ w = 1))
      refine ⟨hg, hcg, ?_, cc.2.1, ?_, ?_⟩
      · omega
      · rw [hw]; exact cc.2.2.1
      have next := widthNext j hj
      change platformWidth (j + 1) = p + if Odd A then 1 else 0 at next
      have hbRow : b ≤ F (j + 1 - 2) := by simpa only [show j + 1 - 2 = j - 1 by omega] using hb
      have zero := (newRow b hbRow).1
      constructor
      · intro hz
        have hpN := zero.mp hz
        by_cases hbp : b ≤ p
        · left
          have gs := (small b hbp).1
          have ze : z = b := by
            change g N = A - b at gs
            dsimp only [z]
            omega
          exact ⟨hbp, ze, by omega⟩
        · right
          have ho : Odd A := by
            by_contra hn
            rw [if_neg hn] at next
            omega
          rw [if_pos ho] at next
          have be : b = p + 1 := by omega
          have ph := critical.1.2.2
          change g (F (j + 1) - (p + 1)) = if Odd A then A - p else A - p - 1 at ph
          rw [if_pos ho] at ph
          have gs : g N = A - p := by dsimp [N]; rw [be]; exact ph
          have ze : z = p := by dsimp [z]; omega
          exact ⟨be, ho, ze, by omega⟩
      · intro hr
        apply zero.mpr
        rcases hr with ⟨hbp, _, _⟩ | ⟨be, ho, _, _⟩
        · split at next <;> omega
        · rw [if_pos ho] at next; omega
    exact ⟨newRow, routes, critical.1⟩
  have rows : ∀ m : ℕ, 8 ≤ m → Row m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases h8 : m = 8
      · subst m; exact base8
      by_cases h9 : m = 9
      · subst m; exact base9
      have ss := step (m - 1) (by omega) (ih (m - 1) (by omega) (by omega))
        (ih (m - 1 - 1) (by omega) (by omega))
      simpa only [show m - 1 + 1 = m by omega] using ss.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m t hm ht
    exact ⟨cap m t hm ht, rows m hm t ht⟩
  · intro W m hm t ht
    have hm8 : 8 ≤ m := le_trans (le_max_left _ _) hm
    have hpm : W ≤ platformWidth m := by
      have hmW := le_trans (le_max_right _ _) hm
      unfold platformWidth
      omega
    have dom : t ≤ F (m - 2) := le_trans ht (le_trans hpm (widthBounds m hm8).2.2)
    have rz := (rows m hm8 t dom).1.mpr (by omega)
    have hc := cap m t hm8 dom
    unfold heightDeficit at rz
    omega
  · intro j b hj hb
    exact (step j hj (rows j (by omega)) (rows (j - 1) (by omega))).2.1 b hb
  · intro j hj
    exact (step j hj (rows j (by omega)) (rows (j - 1) (by omega))).2.2
end D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau
