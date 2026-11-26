/- GID: D5/S3/Combinatorics/Polyomino/OeisA395348FourLag
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Polyomino/OeisA395348FourLag
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal alternating spiral-queens play exists uniquely and satisfies the four-lag recurrence. -/

import D5.S3.Combinatorics.Polyomino.SquareSpiralShells

namespace SpiralQueens

private abbrev Point := ℤ × ℤ

private def Box (r : ℤ) (p : Point) : Prop :=
  -r ≤ p.1 ∧ p.1 ≤ r ∧ -r ≤ p.2 ∧ p.2 ≤ r

private def radius (p : Point) : ℤ :=
  max (max p.1 (-p.1)) (max p.2 (-p.2))

private theorem radius_spec (p : Point) :
    Box (radius p) p ∧
      (p.1 = radius p ∨ p.1 = -radius p ∨ p.2 = radius p ∨ p.2 = -radius p) := by
  rcases p with ⟨x, y⟩
  simp only [Box, radius]
  omega

private theorem radius_le {r : ℤ} {p : Point} : radius p ≤ r ↔ Box r p := by
  simp only [radius, Box, max_le_iff]
  omega

private theorem radius_eq {r : ℤ} {p : Point} (h : Box r p)
    (e : p.1 = r ∨ p.1 = -r ∨ p.2 = r ∨ p.2 = -r) : radius p = r := by
  have h₁ := radius_le.mpr h
  unfold Box at h
  unfold radius at *
  omega

private theorem radius_nonneg (p : Point) : 0 ≤ radius p := by
  unfold radius
  omega

private theorem radius_zero {p : Point} (h : radius p = 0) : p = (0, 0) := by
  rcases p with ⟨x, y⟩
  have h' := (radius_spec (x, y)).1
  simp only [h, Box, neg_zero] at h'
  congr <;> omega

-- The shell visits east, north, west, south, assigning each corner to the
-- side on which it is reached.
private def offset (r : ℤ) (p : Point) : ℤ :=
  if p.1 = r ∧ -r < p.2 then p.2 + r - 1
  else if p.2 = r then 3*r - 1 - p.1
  else if p.1 = -r then 5*r - 1 - p.2
  else 7*r - 1 + p.1

private theorem offset_spec {r : ℤ} {p : Point} (hr : 0 < r) (hp : radius p = r) :
    0 ≤ offset r p ∧ offset r p < 8*r ∧ shellPoint r (offset r p) = p := by
  rcases p with ⟨x, y⟩
  obtain ⟨hxy, hside⟩ := radius_spec (x, y)
  simp only [hp, Box] at hxy hside
  simp only [offset]
  split <;> try split <;> try split
  all_goals
    simp only [shellPoint]
    split <;> try split <;> try split
    all_goals simp only [Prod.mk.injEq]; omega

private theorem shellPoint_spec {r d : ℤ} (hr : 0 < r) (hd : 0 ≤ d) (hu : d < 8*r) :
    radius (shellPoint r d) = r ∧ offset r (shellPoint r d) = d := by
  unfold shellPoint
  split <;> try split <;> try split
  all_goals
    apply And.intro
    · apply radius_eq
      · change -r ≤ _ ∧ _ ≤ r ∧ -r ≤ _ ∧ _ ≤ r
        omega
      · first
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (Or.inl rfl))
        | exact Or.inr (Or.inr (Or.inr rfl))
    · unfold offset
      dsimp only
      split_ifs <;> omega

private def shellStart (r : ℤ) : ℤ := (2*r - 1)^2

private theorem shellStart_succ (r : ℤ) : shellStart (r+1) = shellStart r + 8*r := by
  unfold shellStart
  ring

private theorem shellStart_mono {r s : ℤ} (hr : 1 ≤ r) (h : r ≤ s) :
    shellStart r ≤ shellStart s := by
  have hh : 0 ≤ (2*s - 2*r) * (2*s + 2*r - 2) :=
    mul_nonneg (by omega) (by omega)
  unfold shellStart
  nlinarith only [hh]

private def labelInt (p : Point) : ℤ :=
  let r := radius p
  if r = 0 then 0 else shellStart r + offset r p

private def label (p : Point) : ℕ := (labelInt p).toNat

private theorem labelInt_nonneg (p : Point) : 0 ≤ labelInt p := by
  by_cases hz : radius p = 0
  · simp [labelInt, hz]
  have hr := radius_nonneg p
  have ho := (offset_spec (by omega : 0 < radius p) rfl).1
  have hs : 0 ≤ shellStart (radius p) := by unfold shellStart; positivity
  simp only [labelInt, ite_eq_right hz]
  omega

private theorem label_cast (p : Point) : (label p : ℤ) = labelInt p :=
  Int.toNat_of_nonneg (labelInt_nonneg p)

private theorem label_lt_of_radius_lt {p q : Point} (h : radius p < radius q) :
    label p < label q := by
  have hp := radius_nonneg p
  have hq := (offset_spec (by omega : 0 < radius q) rfl).1
  have hqn : radius q ≠ 0 := by omega
  have hq1 := shellStart_mono (by decide : (1 : ℤ) ≤ 1) (by omega : 1 ≤ radius q)
  have hone : shellStart 1 = 1 := by decide
  rw [hone] at hq1
  have hpc := label_cast p
  have hqc := label_cast q
  rw [labelInt, ite_eq_right hqn] at hqc
  by_cases hpz : radius p = 0
  · simp [labelInt, hpz] at hpc
    omega
  · have hstep := shellStart_mono (by omega : 1 ≤ radius p + 1)
        (by omega : radius p + 1 ≤ radius q)
    rw [shellStart_succ] at hstep
    obtain ⟨_, hb, _⟩ := offset_spec (by omega : 0 < radius p) (p := p) rfl
    rw [labelInt, ite_eq_right hpz] at hpc
    omega

private theorem label_lt_same_shell {p q : Point} {r : ℤ} (hr : 0 < r)
    (hp : radius p = r) (hq : radius q = r) :
    label p < label q ↔ offset r p < offset r q := by
  have hc := label_cast p
  have hd := label_cast q
  have hz : r ≠ 0 := by omega
  simp only [labelInt, hp, hq, ite_eq_right hz] at hc hd
  omega

private theorem label_injective : Function.Injective label := by
  intro p q h
  have hr : radius p = radius q := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hl
    · have := label_lt_of_radius_lt hl
      omega
    · have := label_lt_of_radius_lt hl
      omega
  by_cases hz : radius q = 0
  · rw [radius_zero (hr.trans hz), radius_zero hz]
  have hn := radius_nonneg q
  have hpos : 0 < radius q := by omega
  have h₁ := label_cast p
  have h₂ := label_cast q
  simp only [labelInt, hr, ite_eq_right hz] at h₁ h₂
  have h₃ : offset (radius q) p = offset (radius q) q := by omega
  calc
    p = shellPoint (radius q) (offset (radius q) p) := (offset_spec hpos hr).2.2.symm
    _ = shellPoint (radius q) (offset (radius q) q) := congrArg _ h₃
    _ = q := (offset_spec hpos rfl).2.2

private theorem earlier_box {p q : Point} {r : ℤ} (hq : radius q = r)
    (hl : label p < label q) : Box r p := by
  apply radius_le.mp
  by_contra hn
  have := label_lt_of_radius_lt (p := q) (q := p) (by omega)
  omega

private theorem earlier_of_boundary {p q : Point} {r : ℤ} (hr : 0 < r)
    (hq : radius q = r) (hp : p.1 = r ∨ p.1 = -r ∨ p.2 = r ∨ p.2 = -r)
    (hl : label p < label q) : offset r p < offset r q :=
  (label_lt_same_shell hr (radius_eq (earlier_box hq hl) hp) hq).mp hl

private theorem label_spiral (n : ℕ) : label (spiral n) = n := by
  by_cases hz : n = 0
  · subst n
    rfl
  obtain ⟨k, d, h, hd, hs⟩ := spiral_shells (by omega : 0 < n)
  rw [hs]
  obtain ⟨hr, hoff⟩ := shellPoint_spec (r := (k : ℤ)+1) (d := (d : ℤ))
    (by omega) (by omega) (by omega)
  have hc := label_cast (shellPoint ((k:ℤ)+1) (d:ℤ))
  have hd' : (k : ℤ)+1 ≠ 0 := by omega
  simp only [labelInt, hr, ite_eq_right hd', hoff, shellStart] at hc
  have hb : ((2*k+1)*(2*k+1) : ℕ) = (2*k+1)^2 := by ring
  rw [hb] at h
  have hcast := congrArg (fun a : ℕ => (a : ℤ)) h
  push_cast at hcast
  rw [show (2 * ((k : ℤ) + 1) - 1) ^ 2 = (2 * (k : ℤ) + 1) ^ 2 by ring] at hc
  omega

private theorem spiral_label (p : Point) : spiral (label p) = p := by
  apply label_injective
  exact label_spiral _

def Attacks (q p : ℤ × ℤ) : Prop :=
  q.1 = p.1 ∨ q.2 = p.2 ∨ q.1 + q.2 = p.1 + p.2 ∨ q.1 - q.2 = p.1 - p.2

private instance (q p : Point) : Decidable (Attacks q p) := by unfold Attacks; infer_instance

private def blackRight (r : ℤ) : Point := (r, r % 2)
private def blackLeft (r : ℤ) : Point := (-r, r % 2)
private def redColumn (r : ℤ) : ℤ := 3*(r % 2)-1
private def redTop (r : ℤ) : Point := (redColumn r, r)
private def redBottom (r : ℤ) : Point := (redColumn r, -r)

private def onShell (r s : ℤ) : Point :=
  if s = 0 then blackRight r
  else if s = 1 then redTop r
  else if s = 2 then blackLeft r
  else redBottom r

private def opening (t : ℕ) : Point :=
  #[(0, 0), (2, -1), (1, 1), (-1, 2), (-2, 0), (-1, -2)].getD t (0, 0)

private def play (t : ℕ) : Point :=
  if t < 6 then opening t else
  onShell (((t : ℤ)+6)/4) (((t : ℤ)+6)%4)

private def turn (r s : ℤ) : ℕ := (4*r-6+s).toNat

private theorem cast_turn {r s : ℤ} (hr : 3 ≤ r) (hs : 0 ≤ s) :
    (turn r s : ℤ) = 4*r-6+s := Int.toNat_of_nonneg (by omega)

private theorem turn_ge {r s : ℤ} (hr : 3 ≤ r) (hs : 0 ≤ s) : 6 ≤ turn r s := by
  have := cast_turn hr hs
  omega

private theorem turn_parity {r s : ℤ} (hr : 3 ≤ r) (hs : 0 ≤ s) :
    ((turn r s : ℤ) % 2) = s % 2 := by rw [cast_turn hr hs]; omega

private theorem play_turn {r s : ℤ} (hr : 3 ≤ r) (hs : 0 ≤ s) (hu : s < 4) :
    play (turn r s) = onShell r s := by
  have hge := turn_ge hr hs
  simp only [play, ite_eq_right (not_lt.mpr hge), cast_turn hr hs]
  congr 1 <;> omega

private theorem exists_turn {t : ℕ} (h : 6 ≤ t) :
    ∃ r s : ℤ, 3 ≤ r ∧ 0 ≤ s ∧ s < 4 ∧ t = turn r s := by
  let v : ℤ := (t : ℤ)+6
  have hr : 3 ≤ v/4 := by dsimp [v]; omega
  have hs : 0 ≤ v%4 := by omega
  exact ⟨v/4, v%4, hr, hs, by omega, by
    have hc := cast_turn hr hs
    apply Int.ofNat.inj
    change (t : ℤ) = (turn (v/4) (v%4) : ℤ)
    rw [hc]
    dsimp [v]
    omega⟩

private def Prior (moves : ℕ → Point) (t : ℕ) (c : ℤ) (q : Point) : Prop :=
  ∃ j : ℕ, j < t ∧ (j : ℤ) % 2 = c ∧ moves j = q

private def History (r s c : ℤ) (q : Point) : Prop :=
  Prior opening 6 c q ∨
    ∃ k u : ℤ, 3 ≤ k ∧ 0 ≤ u ∧ u < 4 ∧
      (k < r ∨ k = r ∧ u < s) ∧ u%2 = c ∧ onShell k u = q

private theorem prior_eq_history {r s : ℤ} {c : ℤ} {q : Point}
    (hr : 3 ≤ r) (hs : 0 ≤ s) (hu : s < 4) :
    Prior play (turn r s) c q ↔ History r s c q := by
  have hturn := cast_turn hr hs
  constructor
  · rintro ⟨j, hj, hc, hq⟩
    by_cases hsmall : j < 6
    · left
      exact ⟨j, hsmall, hc, by simpa [play, hsmall] using hq⟩
    · right
      obtain ⟨k, u, hk, hu₀, hu₁, rfl⟩ := exists_turn (by omega : 6 ≤ j)
      have h' := cast_turn hk hu₀
      exact ⟨k, u, hk, hu₀, hu₁, by omega, (turn_parity hk hu₀).symm.trans hc,
        by simpa only [play_turn hk hu₀ hu₁] using hq⟩
  · rintro (⟨j, hj, hc, hq⟩ | ⟨k, u, hk, hu₀, hu₁, hlt, hc, hq⟩)
    · exact ⟨j, lt_of_lt_of_le hj (turn_ge hr hs), hc, by simpa [play, hj] using hq⟩
    · have h' := cast_turn hk hu₀
      exact ⟨turn k u, by omega, (turn_parity hk hu₀).trans hc,
        by simpa only [play_turn hk hu₀ hu₁] using hq⟩

private theorem boot_black {q : Point} :
    Prior opening 6 0 q ↔ q = (0, 0) ∨ q = (1, 1) ∨ q = (-2, 0) := by
  constructor
  · rintro ⟨j, hj, hc, rfl⟩
    have : j = 0 ∨ j = 2 ∨ j = 4 := by omega
    rcases this with rfl | rfl | rfl
    all_goals decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, rfl, rfl⟩
    · exact ⟨2, by decide, rfl, rfl⟩
    · exact ⟨4, by decide, rfl, rfl⟩

private theorem boot_red {q : Point} :
    Prior opening 6 1 q ↔ q = (2, -1) ∨ q = (-1, 2) ∨ q = (-1, -2) := by
  constructor
  · rintro ⟨j, hj, hc, rfl⟩
    have : j = 1 ∨ j = 3 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl
    all_goals decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, by decide, rfl, rfl⟩
    · exact ⟨3, by decide, rfl, rfl⟩
    · exact ⟨5, by decide, rfl, rfl⟩

private theorem history_black {r s : ℤ} {q : Point} :
    History r s 0 q ↔
      (q = (0, 0) ∨ q = (1, 1) ∨ q = (-2, 0)) ∨
      (∃ k, 3 ≤ k ∧ (k < r ∨ k = r ∧ 0 < s) ∧ q = blackRight k) ∨
      (∃ k, 3 ≤ k ∧ (k < r ∨ k = r ∧ 2 < s) ∧ q = blackLeft k) := by
  unfold History
  rw [boot_black]
  apply or_congr_right
  constructor
  · rintro ⟨k, u, hk, hu₀, hu₁, hlt, hc, hq⟩
    have he : u = 0 ∨ u = 2 := by omega
    rcases he with rfl | rfl
    · left
      exact ⟨k, hk, hlt, by simpa [onShell] using hq.symm⟩
    · right
      exact ⟨k, hk, hlt, by simpa [onShell] using hq.symm⟩
  · rintro (⟨k, hk, hl, rfl⟩ | ⟨k, hk, hl, rfl⟩)
    · exact ⟨k, 0, hk, by decide, by decide, hl, rfl, rfl⟩
    · exact ⟨k, 2, hk, by decide, by decide, hl, rfl, rfl⟩

private theorem history_red {r s : ℤ} {q : Point} :
    History r s 1 q ↔
      (q = (2, -1) ∨ q = (-1, 2) ∨ q = (-1, -2)) ∨
      (∃ k, 3 ≤ k ∧ (k < r ∨ k = r ∧ 1 < s) ∧ q = redTop k) ∨
      (∃ k, 3 ≤ k ∧ (k < r ∨ k = r ∧ 3 < s) ∧ q = redBottom k) := by
  unfold History
  rw [boot_red]
  apply or_congr_right
  constructor
  · rintro ⟨k, u, hk, hu₀, hu₁, hlt, hc, hq⟩
    have he : u = 1 ∨ u = 3 := by omega
    rcases he with rfl | rfl
    · left
      exact ⟨k, hk, hlt, by simpa [onShell] using hq.symm⟩
    · right
      exact ⟨k, hk, hlt, by simpa [onShell] using hq.symm⟩
  · rintro (⟨k, hk, hl, rfl⟩ | ⟨k, hk, hl, rfl⟩)
    · exact ⟨k, 1, hk, by decide, by decide, hl, rfl, rfl⟩
    · exact ⟨k, 3, hk, by decide, by decide, hl, rfl, rfl⟩

private theorem prior_black_right {r s k : ℤ} (hk : 3 ≤ k)
    (h : k < r ∨ k = r ∧ 0 < s) : History r s 0 (blackRight k) :=
  history_black.mpr (Or.inr (Or.inl ⟨k, hk, h, rfl⟩))

private theorem prior_black_left {r s k : ℤ} (hk : 3 ≤ k)
    (h : k < r ∨ k = r ∧ 2 < s) : History r s 0 (blackLeft k) :=
  history_black.mpr (Or.inr (Or.inr ⟨k, hk, h, rfl⟩))

private theorem prior_red_top {r s k : ℤ} (hk : 3 ≤ k)
    (h : k < r ∨ k = r ∧ 1 < s) : History r s 1 (redTop k) :=
  history_red.mpr (Or.inr (Or.inl ⟨k, hk, h, rfl⟩))

private theorem prior_red_bottom {r s k : ℤ} (hk : 3 ≤ k)
    (h : k < r ∨ k = r ∧ 3 < s) : History r s 1 (redBottom k) :=
  history_red.mpr (Or.inr (Or.inr ⟨k, hk, h, rfl⟩))

-- One rejection suffices. Same-color queens contribute only occupancy.
private def Forbidden (r s c : ℤ) (p : Point) : Prop :=
  History r s c p ∨ ∃ q, History r s (1-c) q ∧ Attacks q p

private def Legal (moves : ℕ → Point) (t : ℕ) (p : Point) : Prop :=
  ∀ j : ℕ, j < t → moves j ≠ p ∧ ((j : ℤ)%2 ≠ (t : ℤ)%2 → ¬ Attacks (moves j) p)

private theorem legal_iff {moves : ℕ → Point} {t : ℕ} {p : Point} :
    Legal moves t p ↔
      ¬ (Prior moves t ((t : ℤ)%2) p ∨
        ∃ q, Prior moves t (1-(t : ℤ)%2) q ∧ Attacks q p) := by
  constructor
  · intro h hbad
    rcases hbad with ⟨j, hj, _, e⟩ | ⟨q, ⟨j, hj, hc, rfl⟩, ha⟩
    · exact (h j hj).1 e
    · exact (h j hj).2 (by omega) ha
  · intro h j hj
    by_cases hc : (j : ℤ)%2 = (t : ℤ)%2
    · exact ⟨fun e => h (Or.inl ⟨j, hj, hc, e⟩), fun hn => (hn hc).elim⟩
    · have noAttack : ¬ Attacks (moves j) p :=
        fun ha => h (Or.inr ⟨moves j, ⟨j, hj, by omega, rfl⟩, ha⟩)
      exact ⟨fun e => noAttack (Or.inl (congrArg Prod.fst e)), fun _ => noAttack⟩

private theorem legal_at_turn {r s : ℤ} {p : Point}
    (hr : 3 ≤ r) (hs : 0 ≤ s) (hu : s < 4) :
    Legal play (turn r s) p ↔ ¬ Forbidden r s (s%2) p := by
  rw [legal_iff, turn_parity hr hs]
  simp only [prior_eq_history hr hs hu, Forbidden]

private def Greedy (moves : ℕ → Point) : Prop :=
  ∀ t : ℕ, Legal moves t (moves t) ∧
    ∀ p : Point, label p < label (moves t) → ¬ Legal moves t p

private theorem greedy_unique {f g : ℕ → Point} (hf : Greedy f) (hg : Greedy g) : f = g := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have sameLegality (p : Point) : Legal f t p ↔ Legal g t p := by
      unfold Legal
      constructor
      · intro h j hj
        rw [← ih j hj]
        exact h j hj
      · intro h j hj
        rw [ih j hj]
        exact h j hj
    apply label_injective
    apply le_antisymm
    · by_contra! hl
      exact (hf t).2 _ hl ((sameLegality _).mpr (hg t).1)
    · by_contra! hl
      exact (hg t).2 _ hl ((sameLegality _).mp (hf t).1)

private theorem red_rows {r s y : ℤ} (hlo : -r < y) (hhi : y < r) (h₀ : y ≠ 0) (h₁ : y ≠ 1) :
    ∃ q, History r s 1 q ∧ q.2 = y := by
  by_cases h : y ≥ 3
  · exact ⟨redTop y, prior_red_top h (Or.inl hhi), rfl⟩
  by_cases h' : y ≤ -3
  · exact ⟨redBottom (-y), prior_red_bottom (by omega) (Or.inl (by omega)),
      by simp [redBottom]⟩
  have he : y = -2 ∨ y = -1 ∨ y = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact ⟨(-1, -2), Or.inl (boot_red.mpr (by decide)), rfl⟩
  · exact ⟨(2, -1), Or.inl (boot_red.mpr (by decide)), rfl⟩
  · exact ⟨(-1, 2), Or.inl (boot_red.mpr (by decide)), rfl⟩

private theorem black_cols {r s x : ℤ} (hlo : -r < x) (hhi : x ≤ r) (hs : 0 < s)
    (h₀ : x ≠ -1) (h₁ : x ≠ 2) :
    ∃ q, History r s 0 q ∧ q.1 = x := by
  by_cases h : x ≥ 3
  · exact ⟨blackRight x, prior_black_right h (by omega), rfl⟩
  by_cases h' : x ≤ -3
  · exact ⟨blackLeft (-x), prior_black_left (by omega) (Or.inl (by omega)),
      by simp [blackLeft]⟩
  have he : x = -2 ∨ x = 0 ∨ x = 1 := by omega
  rcases he with rfl | rfl | rfl
  · exact ⟨(-2, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩
  · exact ⟨(0, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩
  · exact ⟨(1, 1), Or.inl (boot_black.mpr (by decide)), rfl⟩

-- Each diagonal projection is covered. Even and odd witnesses are chosen
-- directly from completed shells or the opening.
private theorem red_diagonals {r s d : ℤ} (hr : 5 ≤ r) (hlo : -r ≤ d) (hhi : d ≤ r)
    (hd : d%2 = 1) :
    (∃ q, History r s 1 q ∧ q.1+q.2 = d) ∧
    (∃ q, History r s 1 q ∧ q.1-q.2 = d) := by
  by_cases hp : 5 ≤ d
  · refine ⟨⟨redTop (d-2), prior_red_top (by omega) (Or.inl (by omega)), ?_⟩,
      ⟨redBottom (d-2), prior_red_bottom (by omega) (Or.inl (by omega)), ?_⟩⟩
    all_goals simp only [redTop, redBottom, redColumn]; omega
  by_cases hn : d ≤ -5
  · refine ⟨⟨redBottom (-d-1), prior_red_bottom (by omega) (Or.inl (by omega)), ?_⟩,
      ⟨redTop (-d-1), prior_red_top (by omega) (Or.inl (by omega)), ?_⟩⟩
    all_goals simp only [redTop, redBottom, redColumn]; omega
  have he : d = -3 ∨ d = -1 ∨ d = 1 ∨ d = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨⟨(-1, -2), Or.inl (boot_red.mpr (by decide)), rfl⟩,
      ⟨(-1, 2), Or.inl (boot_red.mpr (by decide)), rfl⟩⟩
  · exact ⟨⟨redBottom 3, prior_red_bottom (by decide) (Or.inl (by omega)), rfl⟩,
      ⟨redTop 3, prior_red_top (by decide) (Or.inl (by omega)), rfl⟩⟩
  · exact ⟨⟨(-1, 2), Or.inl (boot_red.mpr (by decide)), rfl⟩,
      ⟨(-1, -2), Or.inl (boot_red.mpr (by decide)), rfl⟩⟩
  · exact ⟨⟨redTop 4, prior_red_top (by decide) (Or.inl (by omega)), rfl⟩,
      ⟨(2, -1), Or.inl (boot_red.mpr (by decide)), rfl⟩⟩

private theorem black_diagonals {r s d : ℤ} (hr : 5 ≤ r) (hlo : -r < d) (hhi : d < r)
    (hd : d%2 = 0) :
    (∃ q, History r s 0 q ∧ q.1+q.2 = d) ∧
    (∃ q, History r s 0 q ∧ q.1-q.2 = d) := by
  by_cases hp : 4 ≤ d
  · have hq : History r s 0 (blackRight d) :=
      prior_black_right (by omega) (Or.inl hhi)
    exact ⟨⟨_, hq, by simp [blackRight, hd]⟩, ⟨_, hq, by simp [blackRight, hd]⟩⟩
  by_cases hn : d ≤ -4
  · have hq : History r s 0 (blackLeft (-d)) :=
      prior_black_left (by omega) (Or.inl (by omega))
    have hn' : (-d)%2 = 0 := by omega
    exact ⟨⟨_, hq, by simp [blackLeft, hn']⟩, ⟨_, hq, by simp [blackLeft, hn']⟩⟩
  have he : d = -2 ∨ d = 0 ∨ d = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact ⟨⟨(-2, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩,
      ⟨(-2, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩⟩
  · exact ⟨⟨(0, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩,
      ⟨(0, 0), Or.inl (boot_black.mpr (by decide)), rfl⟩⟩
  · exact ⟨⟨(1, 1), Or.inl (boot_black.mpr (by decide)), rfl⟩,
      ⟨blackRight 3, prior_black_right (by decide) (Or.inl (by omega)), rfl⟩⟩

-- Before a Black turn, the entire open horizontal strip inside the top
-- and bottom edges is rejected apart from the two current-shell candidates.
private theorem black_strip {r s x y : ℤ} (hr : 5 ≤ r)
    (hx₀ : -r ≤ x) (hx₁ : x ≤ r) (hy₀ : -r < y) (hy₁ : y < r)
    (h : ¬ Forbidden r s 0 (x, y)) :
    (x, y) = blackRight r ∨ (x, y) = blackLeft r := by
  have hy : y = 0 ∨ y = 1 := by
    by_contra! hn
    obtain ⟨q, hq, hy⟩ := red_rows (s := s) hy₀ hy₁ hn.1 hn.2
    exact h (Or.inr ⟨q, hq, Or.inr (Or.inl hy)⟩)
  have hxm : x ≠ -1 := by
    intro he
    exact h (Or.inr ⟨(-1, 2), Or.inl (boot_red.mpr (by decide)), Or.inl he.symm⟩)
  have hxp : x ≠ 2 := by
    intro he
    exact h (Or.inr ⟨(2, -1), Or.inl (boot_red.mpr (by decide)), Or.inl he.symm⟩)
  have hpar : (x+y)%2 = 0 := by
    by_contra hne
    by_cases hx : x ≤ 0
    · obtain ⟨q, hq, hqd⟩ :=
        (red_diagonals (s := s) (d := x+y) hr (by omega) (by omega) (by omega)).1
      exact h (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inl hqd))⟩)
    · obtain ⟨q, hq, hqd⟩ :=
        (red_diagonals (s := s) (d := x-y) hr (by omega) (by omega) (by omega)).2
      exact h (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr hqd))⟩)
  have he : y = x%2 := by omega
  by_cases hh : x = r
  · left
    subst x
    simp [blackRight, he]
  by_cases hl : x = -r
  · right
    subst x
    have hmod : (-r)%2 = r%2 := by omega
    simp [blackLeft, he, hmod]
  exfalso
  apply h
  left
  by_cases hp : 3 ≤ x
  · convert prior_black_right (r := r) (s := s) hp (Or.inl (by omega : x < r)) using 1
    simp [blackRight, he]
  by_cases hn : x ≤ -3
  · have hmod : (-x)%2 = x%2 := by omega
    convert prior_black_left (r := r) (s := s) (by omega : 3 ≤ -x)
      (Or.inl (by omega : -x < r)) using 1
    simp [blackLeft, he, hmod]
  have hbas : x = -2 ∨ x = 0 ∨ x = 1 := by omega
  rcases hbas with rfl | rfl | rfl
  all_goals
    rw [he]
    exact Or.inl (boot_black.mpr (by decide))

-- After the right Black move, the open interval of columns on the left
-- contains only the two Red candidates. The left edge is dealt with by turn.
private theorem red_strip {r s x y : ℤ} (hr : 5 ≤ r) (hs : 0 < s)
    (hx₀ : -r < x) (hx₁ : x ≤ r) (hy₀ : -r ≤ y) (hy₁ : y ≤ r)
    (h : ¬ Forbidden r s 1 (x, y)) :
    (x, y) = redTop r ∨ (x, y) = redBottom r := by
  have hx : x = -1 ∨ x = 2 := by
    by_contra! hn
    obtain ⟨q, hq, hqx⟩ := black_cols (r := r) hx₀ hx₁ hs hn.1 hn.2
    exact h (Or.inr ⟨q, hq, Or.inl hqx⟩)
  have hyb : y ≠ 0 ∧ y ≠ 1 := by
    constructor
    · intro he
      exact h (Or.inr ⟨(0, 0), Or.inl (boot_black.mpr (by decide)),
        Or.inr (Or.inl he.symm)⟩)
    · intro he
      exact h (Or.inr ⟨(1, 1), Or.inl (boot_black.mpr (by decide)),
        Or.inr (Or.inl he.symm)⟩)
  have hpar : (x+y)%2 = 1 := by
    by_contra hne
    by_cases hc : (x = -1 ∧ 0 ≤ y) ∨ (x = 2 ∧ y ≤ 0)
    · obtain ⟨q, hq, hqd⟩ :=
        (black_diagonals (s := s) (d := x+y) hr (by omega) (by omega) (by omega)).1
      exact h (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inl hqd))⟩)
    · obtain ⟨q, hq, hqd⟩ :=
        (black_diagonals (s := s) (d := x-y) hr (by omega) (by omega) (by omega)).2
      exact h (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr hqd))⟩)
  have hcol : x = redColumn y := by unfold redColumn; omega
  by_cases ht : y = r
  · left
    subst y
    simp [redTop, hcol]
  by_cases hb : y = -r
  · right
    subst y
    have hmod : (-r)%2 = r%2 := by omega
    simp [redBottom, hcol, redColumn, hmod]
  exfalso
  apply h
  left
  by_cases hp : 3 ≤ y
  · convert prior_red_top (r := r) (s := s) hp (Or.inl (by omega : y < r)) using 1
    simp [redTop, hcol]
  by_cases hn : y ≤ -3
  · have hmod : (-y)%2 = y%2 := by omega
    convert prior_red_bottom (r := r) (s := s) (by omega : 3 ≤ -y)
      (Or.inl (by omega : -y < r)) using 1
    simp [redBottom, hcol, redColumn, hmod]
  have hbas : y = -2 ∨ y = -1 ∨ y = 2 := by omega
  rcases hbas with rfl | rfl | rfl
  all_goals
    rw [hcol]
    exact Or.inl (boot_red.mpr (by decide))

private theorem red_history_shape {r s : ℤ} {q : Point} (h : History r s 1 q) :
    (q.1 = -1 ∨ q.1 = 2) ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ (q.1+q.2)%2 = 1 := by
  rcases history_red.mp h with (rfl | rfl | rfl) | ⟨k, hk, _, rfl⟩ | ⟨k, hk, _, rfl⟩
  all_goals (simp [redTop, redBottom, redColumn]; try omega)

private theorem black_history_shape {r s : ℤ} {q : Point} (h : History r s 0 q) :
    q.1 ≠ -1 ∧ q.1 ≠ 2 ∧ (q.2 = 0 ∨ q.2 = 1) ∧ (q.1+q.2)%2 = 0 := by
  rcases history_black.mp h with (rfl | rfl | rfl) | ⟨k, hk, _, rfl⟩ | ⟨k, hk, _, rfl⟩
  all_goals (simp [blackRight, blackLeft]; try omega)

private theorem black_safe {r s : ℤ} (hr : 5 ≤ r) (hs : s = 0 ∨ s = 2) :
    ¬ Forbidden r s 0 (onShell r s) := by
  rintro (h | ⟨q, hq, ha⟩)
  · have h' := history_black.mp h
    rcases hs with rfl | rfl <;> rcases h' with (he | he | he) | ⟨k, hk, hl, he⟩ | ⟨k, hk, hl, he⟩
    all_goals
      have hx := congrArg Prod.fst he
      simp [onShell, blackRight, blackLeft] at hx
      omega
  · obtain ⟨hx, hy₀, hy₁, hp⟩ := red_history_shape (by simpa using hq : History r s 1 q)
    rcases hs with rfl | rfl <;>
      simp [Attacks, onShell, blackRight, blackLeft] at ha <;> omega

private theorem red_safe {r s : ℤ} (hr : 5 ≤ r) (hs : s = 1 ∨ s = 3) :
    ¬ Forbidden r s 1 (onShell r s) := by
  rintro (h | ⟨q, hq, ha⟩)
  · have h' := history_red.mp h
    rcases hs with rfl | rfl <;> rcases h' with (he | he | he) | ⟨k, hk, hl, he⟩ | ⟨k, hk, hl, he⟩
    all_goals
      have hy := congrArg Prod.snd he
      simp [onShell, redTop, redBottom] at hy
      omega
  · obtain ⟨hx₀, hx₁, hy, hp⟩ := black_history_shape (by simpa using hq : History r s 0 q)
    rcases hs with rfl | rfl <;>
      simp [Attacks, onShell, redTop, redBottom, redColumn] at ha <;> omega

private theorem radius_blackRight {r : ℤ} (hr : 3 ≤ r) : radius (blackRight r) = r := by
  apply radius_eq
  · simp [Box, blackRight]
    omega
  · exact Or.inl rfl

private theorem radius_blackLeft {r : ℤ} (hr : 3 ≤ r) : radius (blackLeft r) = r := by
  apply radius_eq
  · simp [Box, blackLeft]
    omega
  · exact Or.inr (Or.inl rfl)

private theorem radius_redTop {r : ℤ} (hr : 3 ≤ r) : radius (redTop r) = r := by
  apply radius_eq
  · simp [Box, redTop, redColumn]
    omega
  · exact Or.inr (Or.inr (Or.inl rfl))

private theorem radius_redBottom {r : ℤ} (hr : 3 ≤ r) : radius (redBottom r) = r := by
  apply radius_eq
  · simp [Box, redBottom, redColumn]
    omega
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem offset_blackRight {r : ℤ} (hr : 3 ≤ r) :
    offset r (blackRight r) = r%2 + r - 1 := by
  have hy : -r < r % 2 := by omega
  simp [offset, blackRight, hy]

private theorem offset_blackLeft {r : ℤ} (hr : 3 ≤ r) :
    offset r (blackLeft r) = 5*r - 1 - r%2 := by
  simp only [offset, blackLeft]
  split_ifs <;> omega

private theorem offset_redTop {r : ℤ} (_hr : 3 ≤ r) :
    offset r (redTop r) = 3*r - 1 - redColumn r := by
  simp only [offset, redTop]
  have h : redColumn r ≠ r := by unfold redColumn; omega
  simp [h]

private theorem offset_redBottom {r : ℤ} (hr : 3 ≤ r) :
    offset r (redBottom r) = 7*r - 1 + redColumn r := by
  have h₁ : -r ≠ r := by omega
  have h₂ : redColumn r ≠ -r := by unfold redColumn; omega
  simp [offset, redBottom, h₁, h₂]

private theorem earlier_black_right {r x y : ℤ} (hr : 5 ≤ r)
    (hl : label (x, y) < label (blackRight r)) : Forbidden r 0 0 (x, y) := by
  have hrad := radius_blackRight (by omega : 3 ≤ r)
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := earlier_box hrad hl
  have noFar : ¬ (x = -r ∨ y = r ∨ y = -r) := by
    intro hside
    have ho := earlier_of_boundary (by omega) hrad (by
      change x = r ∨ x = -r ∨ y = r ∨ y = -r
      omega) hl
    rw [offset_blackRight (by omega)] at ho
    unfold offset at ho
    dsimp only at ho
    dsimp only at hx₀ hx₁ hy₀ hy₁
    split_ifs at ho <;> omega
  by_contra hn
  rcases black_strip hr hx₀ hx₁ (by omega) (by omega) hn with he | he
  · rw [he] at hl
    omega
  · exact noFar (Or.inl (congrArg Prod.fst he))

private theorem earlier_black_left {r x y : ℤ} (hr : 5 ≤ r)
    (hl : label (x, y) < label (blackLeft r)) : Forbidden r 2 0 (x, y) := by
  have hrad := radius_blackLeft (by omega : 3 ≤ r)
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := earlier_box hrad hl
  by_cases htop : y = r
  · right
    exact ⟨redTop r, prior_red_top (by omega) (Or.inr ⟨rfl, by decide⟩),
      Or.inr (Or.inl htop.symm)⟩
  have noBottom : y ≠ -r := by
    intro he
    have ho := earlier_of_boundary (by omega) hrad (Or.inr (Or.inr (Or.inr he))) hl
    rw [offset_blackLeft (by omega)] at ho
    unfold offset at ho
    dsimp only at ho
    dsimp only at hx₀ hx₁ hy₀ hy₁
    split_ifs at ho <;> omega
  by_contra hn
  rcases black_strip hr hx₀ hx₁ (by omega) (by omega) hn with he | he
  · exact hn (Or.inl (he ▸ prior_black_right (by omega) (Or.inr ⟨rfl, by decide⟩)))
  · rw [he] at hl
    omega

private theorem earlier_red_top {r x y : ℤ} (hr : 5 ≤ r)
    (hl : label (x, y) < label (redTop r)) : Forbidden r 1 1 (x, y) := by
  have hrad := radius_redTop (by omega : 3 ≤ r)
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := earlier_box hrad hl
  have noFar : ¬ (x = -r ∨ y = -r) := by
    intro he
    have ho := earlier_of_boundary (by omega) hrad (by
      change x = r ∨ x = -r ∨ y = r ∨ y = -r
      omega) hl
    rw [offset_redTop (by omega)] at ho
    unfold offset redColumn at ho
    dsimp only at ho
    dsimp only at hx₀ hx₁ hy₀ hy₁
    split_ifs at ho <;> omega
  by_contra hn
  rcases red_strip hr (by decide : (0 : ℤ) < 1) (by omega) hx₁ hy₀ hy₁ hn with he | he
  · rw [he] at hl
    omega
  · exact noFar (Or.inr (congrArg Prod.snd he))

private theorem earlier_red_bottom {r x y : ℤ} (hr : 5 ≤ r)
    (hl : label (x, y) < label (redBottom r)) : Forbidden r 3 1 (x, y) := by
  have hrad := radius_redBottom (by omega : 3 ≤ r)
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := earlier_box hrad hl
  by_cases hleft : x = -r
  · right
    exact ⟨blackLeft r, prior_black_left (by omega) (Or.inr ⟨rfl, by decide⟩),
      Or.inl hleft.symm⟩
  by_contra hn
  rcases red_strip hr (by decide : (0 : ℤ) < 3) (by omega) hx₁ hy₀ hy₁ hn with he | he
  · exact hn (Or.inl (he ▸ prior_red_top (by omega) (Or.inr ⟨rfl, by decide⟩)))
  · rw [he] at hl
    omega

private theorem tail_greedy {r s : ℤ} (hr : 5 ≤ r) (hs : 0 ≤ s) (hu : s < 4) :
    Legal play (turn r s) (play (turn r s)) ∧
      ∀ p : Point, label p < label (play (turn r s)) → ¬ Legal play (turn r s) p := by
  have hr' : 3 ≤ r := by omega
  rw [play_turn hr' hs hu]
  simp only [legal_at_turn hr' hs hu, not_not]
  constructor
  · have hh : s = 0 ∨ s = 2 ∨ s = 1 ∨ s = 3 := by omega
    rcases hh with rfl | rfl | rfl | rfl
    · exact black_safe hr (Or.inl rfl)
    · exact black_safe hr (Or.inr rfl)
    · exact red_safe hr (Or.inl rfl)
    · exact red_safe hr (Or.inr rfl)
  · rintro ⟨x, y⟩ hl
    have hh : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hh with rfl | rfl | rfl | rfl
    · exact earlier_black_right hr hl
    · exact earlier_red_top hr hl
    · exact earlier_black_left hr hl
    · exact earlier_red_bottom hr hl

private def legalFin (t : Fin 14) (p : Point) : Prop :=
  ∀ j : Fin 14, j.val < t.val →
    play j.val ≠ p ∧ ((j.val : ℤ)%2 ≠ (t.val : ℤ)%2 → ¬ Attacks (play j.val) p)

private instance (t : Fin 14) (p : Point) : Decidable (legalFin t p) := by
  unfold legalFin
  infer_instance

private theorem legalFin_iff {t : Fin 14} {p : Point} : legalFin t p ↔ Legal play t.val p := by
  constructor
  · intro h j hj
    exact h ⟨j, lt_trans hj t.isLt⟩ hj
  · intro h j hj
    exact h j.val hj

private def openingCell (x y : Fin 9) : Point := ((x.val : ℤ)-4, (y.val : ℤ)-4)

private theorem openingCell_surj {p : Point} (h : Box 4 p) :
    ∃ x y : Fin 9, openingCell x y = p := by
  have hx : 0 ≤ p.1+4 := by unfold Box at h; omega
  have hy : 0 ≤ p.2+4 := by unfold Box at h; omega
  have cx := Int.toNat_of_nonneg hx
  have cy := Int.toNat_of_nonneg hy
  refine ⟨⟨(p.1+4).toNat, ?_⟩, ⟨(p.2+4).toNat, ?_⟩, ?_⟩
  · unfold Box at h
    omega
  · unfold Box at h
    omega
  · apply Prod.ext <;> simp only [openingCell] <;> omega

private theorem opening_size (t : Fin 14) : radius (play t.val) ≤ 4 := by
  fin_cases t <;> decide

-- The certificate checks the actual rule at every opening turn against every
-- point of the 9 by 9 box. The preceding-label theorem makes the box exhaustive.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
private theorem opening_certificate (t : Fin 14) :
    legalFin t (play t.val) ∧
      ∀ x y : Fin 9, label (openingCell x y) < label (play t.val) →
        ¬ legalFin t (openingCell x y) := by
  fin_cases t <;> decide +kernel

private theorem opening_greedy {t : ℕ} (ht : t < 14) :
    Legal play t (play t) ∧ ∀ p : Point, label p < label (play t) → ¬ Legal play t p := by
  let ti : Fin 14 := ⟨t, ht⟩
  obtain ⟨hlegal, hmin⟩ := opening_certificate ti
  refine ⟨legalFin_iff.mp hlegal, ?_⟩
  intro p hp
  have hbox := earlier_box rfl hp
  have hsize := opening_size ti
  have hbox' : Box 4 p := radius_le.mp (le_trans (radius_le.mpr hbox) hsize)
  obtain ⟨x, y, rfl⟩ := openingCell_surj hbox'
  exact fun h => hmin x y hp (legalFin_iff.mpr h)

private theorem play_greedy : Greedy play := by
  intro t
  by_cases ht : t < 14
  · exact opening_greedy ht
  obtain ⟨r, s, hr, hs, hu, rfl⟩ := exists_turn (by omega : 6 ≤ t)
  have := cast_turn hr hs
  exact tail_greedy (by omega) hs hu

private theorem label_blackRight {r : ℤ} (hr : 3 ≤ r) :
    (label (blackRight r) : ℤ) = (2*r-1)^2 + (r%2 + r - 1) := by
  have hz : r ≠ 0 := by omega
  rw [label_cast, labelInt]
  simp [radius_blackRight hr, offset_blackRight hr, shellStart, hz]

private theorem label_blackLeft {r : ℤ} (hr : 3 ≤ r) :
    (label (blackLeft r) : ℤ) = (2*r-1)^2 + (5*r - 1 - r%2) := by
  have hz : r ≠ 0 := by omega
  rw [label_cast, labelInt]
  simp [radius_blackLeft hr, offset_blackLeft hr, shellStart, hz]

private def blackLabels (moves : ℕ → Point) (n : ℕ) : ℕ := label (moves (2*n))

private theorem four_lag_for_schedule (n : ℕ) (hn : 2 ≤ n) :
    blackLabels play (n+4) = blackLabels play n + 8*n + 34 := by
  by_cases h₂ : n = 2
  · subst n
    decide
  obtain ⟨r, s, hr, hs, hu, ht⟩ := exists_turn (t := 2*n) (by omega)
  have hcast := cast_turn hr hs
  have hs' : s = 0 ∨ s = 2 := by omega
  have hr' : 3 ≤ r+2 := by omega
  have hnext : 2*(n+4) = turn (r+2) s := by
    have := cast_turn hr' hs
    omega
  unfold blackLabels
  rw [ht, hnext, play_turn hr hs hu, play_turn hr' hs hu]
  apply Int.ofNat.inj
  have hmod : (r+2)%2 = r%2 := by omega
  rcases hs' with rfl | rfl
  · change (label (blackRight (r+2)) : ℤ) =
      (label (blackRight r) : ℤ) + 8*(n : ℤ) + 34
    rw [label_blackRight hr', label_blackRight hr, hmod]
    have hn' : (n : ℤ) = 2*r-3 := by omega
    rw [hn']
    ring
  · change (label (blackLeft (r+2)) : ℤ) =
      (label (blackLeft r) : ℤ) + 8*(n : ℤ) + 34
    rw [label_blackLeft hr', label_blackLeft hr, hmod]
    have hn' : (n : ℤ) = 2*r-2 := by omega
    rw [hn']
    ring

private theorem exact_four_lag (moves : ℕ → Point) (h : Greedy moves) (n : ℕ) (hn : 2 ≤ n) :
    blackLabels moves (n+4) = blackLabels moves n + 8*n + 34 := by
  rw [greedy_unique h play_greedy]
  exact four_lag_for_schedule n hn

-- Labels implementoccupancy directly. Attack compatibility consults
-- exactly the opponent's earlier turns.
def SpiralLegal (moves : ℕ → ℕ) (t n : ℕ) : Prop :=
  ∀ j : ℕ, j < t → moves j ≠ n ∧
    ((j : ℤ)%2 ≠ (t : ℤ)%2 → ¬ Attacks (spiral (moves j)) (spiral n))

private theorem spiralLegal_iff {moves : ℕ → ℕ} {t n : ℕ} :
    SpiralLegal moves t n ↔ Legal (spiral ∘ moves) t (spiral n) := by
  constructor <;> intro h j hj
  · obtain ⟨hocc, hatt⟩ := h j hj
    refine ⟨?_, hatt⟩
    intro he
    apply hocc
    simpa only [Function.comp_apply, label_spiral] using (congrArg label he)
  · obtain ⟨hocc, hatt⟩ := h j hj
    exact ⟨fun he => hocc (congrArg spiral he), hatt⟩

def SpiralGreedy (moves : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, SpiralLegal moves t (moves t) ∧
    ∀ n : ℕ, n < moves t → ¬ SpiralLegal moves t n

private theorem spiralGreedy_iff {moves : ℕ → ℕ} :
    SpiralGreedy moves ↔ Greedy (spiral ∘ moves) := by
  constructor
  · intro h t
    refine ⟨spiralLegal_iff.mp (h t).1, ?_⟩
    intro p hp
    change label p < label (spiral (moves t)) at hp
    rw [label_spiral] at hp
    have hmin := (h t).2 (label p) hp
    simpa only [spiralLegal_iff, spiral_label] using hmin
  · intro h t
    refine ⟨spiralLegal_iff.mpr (h t).1, ?_⟩
    intro n hn hlegal
    apply (h t).2 (spiral n) _ (spiralLegal_iff.mp hlegal)
    simpa only [Function.comp_apply, label_spiral] using hn

private def placements (t : ℕ) : ℕ := label (play t)

private theorem placements_greedy : SpiralGreedy placements := by
  apply spiralGreedy_iff.mpr
  have h : spiral ∘ placements = play := by funext t; exact spiral_label (play t)
  rw [h]
  exact play_greedy

private theorem greedy_placements_unique : ∃! moves : ℕ → ℕ, SpiralGreedy moves := by
  refine ⟨placements, placements_greedy, ?_⟩
  intro other ho
  have he := greedy_unique (spiralGreedy_iff.mp ho) (spiralGreedy_iff.mp placements_greedy)
  funext t
  simpa only [Function.comp_apply, label_spiral] using congrArg label (congrFun he t)

/-- The recurrencefor the literal, smallest-legal-label process. -/
theorem a395348_four_lag :
    (∃! moves : ℕ → ℕ, SpiralGreedy moves) ∧
      ∀ moves : ℕ → ℕ, SpiralGreedy moves → ∀ n : ℕ, 2 ≤ n →
        moves (2*(n+4)) = moves (2*n) + 8*n + 34 := by
  refine ⟨greedy_placements_unique, ?_⟩
  intro moves h n hn
  have h' := exact_four_lag (spiral ∘ moves) (spiralGreedy_iff.mp h) n hn
  simpa only [blackLabels, Function.comp_apply, label_spiral] using h'

end SpiralQueens
