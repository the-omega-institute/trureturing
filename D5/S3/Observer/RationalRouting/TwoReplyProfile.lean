/- GID: D5/S3/Observer/RationalRouting/TwoReplyProfile
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/TwoReplyProfile
   mirror-E: none(waiver:uniform-symbolic-acquisition)
   anchors: []
   utility: none
   digest: Original bounded-scale future profiles are acquired at the actual moving cut. -/
import D5.S3.Observer.RationalRouting.FullFutureProfile
import Mathlib.Data.Nat.Size
/-! Exact original intervals and acquisition at one attained current state. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting
open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

/-- The known attained matrix acts on a possible original, not on a copied source. -/
def mobius (A : PositiveMatrix) (x : ℚ) : ℚ := ((A.a : ℚ) * x + A.b) / ((A.c : ℚ) * x + A.d)
private theorem diagonal_positive {A : PositiveMatrix} (hA : Unimodular A) : 0 < A.a ∧ 0 < A.d := by
  have ha : A.a ≠ 0 := by intro h; simp [Unimodular, h] at hA
  have hd : A.d ≠ 0 := by intro h; simp [Unimodular, h] at hA
  omega
private theorem denominator_positive {A : PositiveMatrix} (hA : Unimodular A) {x : ℚ} (hx : 0 < x) : 0 < (A.c : ℚ) * x + A.d := by
  have hd : (0 : ℚ) < A.d := by exact_mod_cast (diagonal_positive hA).2
  positivity
private theorem mobius_strict {A : PositiveMatrix} (hA : Unimodular A) {x y : ℚ} (hx : 0 < x) (hy : 0 < y) (hxy : x < y) : mobius A x < mobius A y := by
  have hd : (A.a : ℚ) * A.d - (A.b : ℚ) * A.c = 1 := by
    have hh : (A.a : ℚ) * A.d = (A.b : ℚ) * A.c + 1 := by exact_mod_cast hA
    linarith
  dsimp [mobius]; rw [div_lt_div_iff₀ (denominator_positive hA hx) (denominator_positive hA hy)]
  have he : ((A.a : ℚ) * y + A.b) * ((A.c : ℚ) * x + A.d) - ((A.a : ℚ) * x + A.b) * ((A.c : ℚ) * y + A.d) = y - x := by linear_combination (y - x) * hd
  linarith
private theorem attain_append (u v : List Bool) (x : ℚ) : attain (u ++ v) x = attain v (attain u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons b u ih => exact ih (step b x)
private theorem matrix_cons_eval (b : Bool) (w : List Bool) {x : ℚ} (hx : 0 < x) : mobius (wordMatrix (b :: w)) x = step b (mobius (wordMatrix w) x) := by
  have hp := denominator_positive (unimodular_wordMatrix w) hx; let N : ℚ := (wordMatrix w).a * x + (wordMatrix w).b
  let D : ℚ := (wordMatrix w).c * x + (wordMatrix w).d; have hD : D ≠ 0 := hp.ne'
  cases b
  · have he : mobius (wordMatrix (false :: w)) x = N / (D + N) := by
      dsimp [wordMatrix, PositiveMatrix.mul, leftStep, mobius, N, D]; push_cast
      congr 1 <;> ring
    rw [he]; change N / (D + N) = (N / D) / (1 + N / D)
    generalize hNN : N = n at *
    generalize hDD : D = d at *
    field_simp [hD]
  · have he : mobius (wordMatrix (true :: w)) x = (N + D) / D := by
      dsimp [wordMatrix, PositiveMatrix.mul, rightStep, mobius, N, D]; push_cast
      congr 1 <;> ring
    rw [he]; change (N + D) / D = N / D + 1
    rw [add_div, div_self hD]
private theorem chronological_matrix (u : List Bool) {x : ℚ} (hx : 0 < x) : attain u x = mobius (wordMatrix u.reverse) x := by
  suffices h : ∀ w : List Bool, attain w.reverse x = mobius (wordMatrix w) x by
    simpa using h u.reverse
  intro w
  induction w with
  | nil => simp [attain, wordMatrix, mobius, rootMatrix]
  | cons b w ih =>
    rw [List.reverse_cons, attain_append]; simp only [attain]
    rw [ih, matrix_cons_eval b w hx]

/-- Coefficients of the original inequality for a current threshold. -/
def thresholdSlope (A : PositiveMatrix) (D : ℕ) (r : ℤ) : ℚ := (D : ℚ) * A.a - (r : ℚ) * A.c

def thresholdIntercept (A : PositiveMatrix) (D : ℕ) (r : ℤ) : ℚ := (r : ℚ) * A.d - (D : ℚ) * A.b
private theorem threshold_determinant {A : PositiveMatrix} (hA : Unimodular A) (D : ℕ) (r : ℤ) : thresholdSlope A D r * A.d + (A.c : ℚ) * thresholdIntercept A D r = D := by
  have hd : (A.a : ℚ) * A.d = (A.b : ℚ) * A.c + 1 := by exact_mod_cast hA
  dsimp [thresholdSlope, thresholdIntercept]
  linear_combination (D : ℚ) * hd
private theorem raw_cell_inequalities {A : PositiveMatrix} (hA : Unimodular A) (D : ℕ) (r : ℤ) {x : ℚ} (hx : 0 < x) : reply D (mobius A x) = r ↔
      thresholdIntercept A D r ≤ thresholdSlope A D r * x ∧ thresholdSlope A D (r + 1) * x < thresholdIntercept A D (r + 1) := by
  rw [reply, Int.floor_eq_iff]; have hp := denominator_positive hA hx
  rw [mobius, ← mul_div_assoc, le_div_iff₀ hp, div_lt_iff₀ hp]; dsimp [thresholdSlope, thresholdIntercept]
  push_cast
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith
private theorem actual_lower_slope {A : PositiveMatrix} (hA : Unimodular A) {D : ℕ} (hD : 1 ≤ D) {r : ℤ} {x : ℚ} (hx : 0 < x)
    (hr : reply D (mobius A x) = r) : 0 < thresholdSlope A D r := by
  have hi := ((raw_cell_inequalities hA D r hx).mp hr).1; have he := threshold_determinant hA D r
  have hp : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  by_contra hn
  have hk : thresholdSlope A D r ≤ 0 := le_of_not_gt hn; have hl : thresholdIntercept A D r ≤ 0 := hi.trans (mul_nonpos_of_nonpos_of_nonneg hk hx.le)
  have hkd := mul_nonpos_of_nonpos_of_nonneg hk (Nat.cast_nonneg A.d : (0 : ℚ) ≤ A.d); have hcl := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg A.c : (0 : ℚ) ≤ A.c) hl
  linarith

/-- Inverting a raw cell clips its lower endpoint at zero. An upper endpoint at or beyond the image asymptote imposes no new original upper bound. -/
def firstInterval (A : PositiveMatrix) (D : ℕ) (I : ProfileCell) (r : ℤ) : ProfileCell := ⟨max I.lower (max 0 (thresholdIntercept A D r / thresholdSlope A D r)),
    if 0 < thresholdSlope A D (r + 1) then min I.upper (thresholdIntercept A D (r + 1) / thresholdSlope A D (r + 1))
    else I.upper⟩
private theorem first_interval_exact {A : PositiveMatrix} (hA : Unimodular A) {D : ℕ} (hD : 1 ≤ D) {I : ProfileCell} {r : ℤ} {x : ℚ} (hx : 0 < x)
    (hr : reply D (mobius A x) = r) (y : ℚ) : (firstInterval A D I r).Contains y ↔ I.Contains y ∧ reply D (mobius A y) = r := by
  have hk := actual_lower_slope hA hD hx hr
  have hp : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  have upper_all (hn : thresholdSlope A D (r + 1) ≤ 0) (hy : 0 < y) : thresholdSlope A D (r + 1) * y < thresholdIntercept A D (r + 1) := by
    have he := threshold_determinant hA D (r + 1); have hkd := mul_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg A.d : (0 : ℚ) ≤ A.d)
    have hl : 0 < thresholdIntercept A D (r + 1) := by
      by_contra h
      have hcl := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg A.c : (0 : ℚ) ≤ A.c) (le_of_not_gt h); linarith
    exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hn hy.le) hl
  by_cases hu : 0 < thresholdSlope A D (r + 1)
  · simp only [firstInterval, ite_eq_left hu, ProfileCell.Contains, max_le_iff, lt_min_iff]
    constructor
    · rintro ⟨hy, ⟨hil, ⟨_, hl⟩⟩, hiu, hh⟩
      refine ⟨⟨hy, hil, hiu⟩, (raw_cell_inequalities hA D r hy).mpr ?_⟩
      exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hk).mp hl, by simpa only [mul_comm] using (lt_div_iff₀ hu).mp hh⟩
    · rintro ⟨⟨hy, hil, hiu⟩, hh⟩
      have ht := (raw_cell_inequalities hA D r hy).mp hh
      exact ⟨hy, ⟨hil, ⟨hy.le, (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using ht.1)⟩⟩, hiu, (lt_div_iff₀ hu).mpr (by simpa only [mul_comm] using ht.2)⟩
  · simp only [firstInterval, ite_eq_right hu, ProfileCell.Contains, max_le_iff]
    constructor
    · rintro ⟨hy, ⟨hil, ⟨_, hl⟩⟩, hiu⟩
      refine ⟨⟨hy, hil, hiu⟩, (raw_cell_inequalities hA D r hy).mpr ?_⟩
      exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hk).mp hl, upper_all (le_of_not_gt hu) hy⟩
    · rintro ⟨⟨hy, hil, hiu⟩, hh⟩
      have ht := (raw_cell_inequalities hA D r hy).mp hh
      exact ⟨hy, ⟨hil, ⟨hy.le, (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using ht.1)⟩⟩, hiu⟩

/-- The least numerator strictly above a rational endpoint, computed by one integer division without reducing a fraction in the denominator loop. -/
def nextNumerator (l : ℚ) (m : ℕ) : ℤ := ((m : ℤ) * l.num) / (l.den : ℤ) + 1
private theorem next_numerator_eq (l : ℚ) (m : ℕ) : nextNumerator l m = reply m l + 1 := by
  rw [nextNumerator, reply]; congr 1
  rw [← Rat.floor_intCast_div_natCast]; congr 1
  push_cast; rw [mul_div_assoc, Rat.num_div_den]

/-- The scan is over the original denominators only. Repeated fractions need no distinctness test: any selected pair names the same unresolved cut. -/
def findCut : ℕ → ProfileCell → Option (ℤ × ℕ)
  | 0, _ => none
  | n + 1, C =>
      let j := nextNumerator C.lower (n + 1)
      if j * (C.upper.den : ℤ) < (n + 1 : ℕ) * C.upper.num then some (j, n + 1)
      else findCut n C
private theorem candidate_upper (C : ProfileCell) (m : ℕ) (j : ℤ) : j * (C.upper.den : ℤ) < (m : ℤ) * C.upper.num ↔ (j : ℚ) < (m : ℚ) * C.upper := by
  have hd : (0 : ℚ) < C.upper.den := by exact_mod_cast C.upper.pos
  have he : (m : ℚ) * C.upper = ((m : ℚ) * C.upper.num) / C.upper.den := by rw [mul_div_assoc, Rat.num_div_den]
  rw [he, lt_div_iff₀ hd]; exact_mod_cast (Iff.rfl : j * (C.upper.den : ℤ) < (m : ℤ) * C.upper.num ↔ _)
private theorem candidate_lower (C : ProfileCell) (m : ℕ) (hm : 1 ≤ m) : C.lower < (nextNumerator C.lower m : ℚ) / m := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [lt_div_iff₀ hp, next_numerator_eq]; have h := Int.lt_floor_add_one ((m : ℚ) * C.lower)
  simpa [reply, mul_comm] using h
private theorem candidate_le {C : ProfileCell} {m : ℕ} (hm : 1 ≤ m) {j : ℤ} (hj : C.lower < (j : ℚ) / m) : nextNumerator C.lower m ≤ j := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hf : reply m C.lower < j := by
    apply Int.floor_lt.mpr; have ht := (lt_div_iff₀ hp).mp hj
    simpa [mul_comm] using ht
  rw [next_numerator_eq]; omega
private theorem find_cut_spec (B : ℕ) (C : ProfileCell) : (∀ j m, findCut B C = some (j, m) → 1 ≤ m ∧ m ≤ B ∧ C.lower < (j : ℚ) / m ∧ (j : ℚ) / m < C.upper) ∧
    (findCut B C = none → ∀ m : ℕ, 1 ≤ m → m ≤ B → ∀ j : ℤ, ¬ (C.lower < (j : ℚ) / m ∧ (j : ℚ) / m < C.upper)) := by
  induction B with
  | zero =>
    constructor
    · intro j m h; simp [findCut] at h
    · intro _ m hm hmB; omega
  | succ n ih =>
    dsimp only [findCut]
    split_ifs with hc
    · constructor
      · intro j m h
        have he := Option.some.inj h
        cases he
        refine ⟨by omega, le_rfl, candidate_lower C (n + 1) (by omega), ?_⟩
        have hp : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
        exact (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using (candidate_upper C (n + 1) _).mp hc)
      · intro h; simp at h
    · constructor
      · intro j m h
        obtain ⟨hm, hmB, hl, hu⟩ := ih.1 j m h
        exact ⟨hm, by omega, hl, hu⟩
      · intro h m hm hmB j hj
        by_cases he : m = n + 1
        · subst m
          have hj' := candidate_le hm hj.1
          have hp : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
          have hupper : (j : ℚ) < ((n + 1 : ℕ) : ℚ) * C.upper := by simpa only [mul_comm] using (div_lt_iff₀ hp).mp hj.2
          have hsmall : (nextNumerator C.lower (n + 1) : ℚ) < ((n + 1 : ℕ) : ℚ) * C.upper := lt_of_le_of_lt (by exact_mod_cast hj') hupper
          exact hc ((candidate_upper C (n + 1) _).mpr hsmall)
        · exact ih.2 h m hm (by omega) j hj
private theorem different_reply_cut {m : ℕ} (hm : 1 ≤ m) {x y : ℚ} (h : reply m x < reply m y) : x < ((reply m x + 1 : ℤ) : ℚ) / m ∧ ((reply m x + 1 : ℤ) : ℚ) / m ≤ y := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  constructor
  · rw [lt_div_iff₀ hp]; simpa [reply, mul_comm] using Int.lt_floor_add_one ((m : ℚ) * x)
  · rw [div_le_iff₀ hp]
    have he : reply m x + 1 ≤ reply m y := by omega
    have ht := Int.le_floor.mp he
    simpa [mul_comm] using ht
private theorem no_interior_cut_same {B : ℕ} {C : ProfileCell} (h : ∀ m : ℕ, 1 ≤ m → m ≤ B → ∀ j : ℤ, ¬ (C.lower < (j : ℚ) / m ∧ (j : ℚ) / m < C.upper))
    {x y : ℚ} (hx : C.Contains x) (hy : C.Contains y) : SameInstant B x y := by
  intro m hm hmB
  apply le_antisymm
  · by_contra hn
    have hl : reply m y < reply m x := lt_of_not_ge hn; have ht := different_reply_cut hm hl
    exact h m hm hmB _ ⟨hy.2.1.trans_lt ht.1, ht.2.trans_lt hx.2.2⟩
  · by_contra hn
    have hl : reply m x < reply m y := lt_of_not_ge hn; have ht := different_reply_cut hm hl
    exact h m hm hmB _ ⟨hx.2.1.trans_lt ht.1, ht.2.trans_lt hy.2.2⟩
private theorem target_constant_exact {B : ℕ} {C : ProfileCell} (hl : 0 ≤ C.lower) {x : ℚ} (hx : C.Contains x) :
    findCut B C = none ↔ ∀ y : ℚ, C.Contains y → SameInstant B y x := by
  constructor
  · intro hn y hy; exact no_interior_cut_same ((find_cut_spec B C).2 hn) hy hx
  · intro constant
    cases he : findCut B C with
    | none => rfl
    | some cut =>
      obtain ⟨j,m⟩ := cut
      obtain ⟨hm,hmB,hlt,hut⟩ := (find_cut_spec B C).1 j m he
      let t : ℚ := (j : ℚ) / m; have ht : C.Contains t := ⟨hl.trans_lt hlt, hlt.le, hut⟩
      let y := (C.lower + t) / 2
      have hy : C.Contains y := ⟨by dsimp [y]; linarith [ht.1], by dsimp [y]; linarith, by dsimp [y]; linarith⟩
      have hp : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
      have hs : reply m y < j := by
        apply Int.floor_lt.mpr
        have hyt : y < t := by dsimp [y]; linarith
        simpa only [t, mul_comm] using (lt_div_iff₀ hp).mp hyt
      have hb : j ≤ reply m t := by
        apply Int.le_floor.mpr; dsimp [t]
        rw [mul_div_cancel₀ _ hp.ne']
      rw [constant y hy m hm hmB] at hs; rw [constant t ht m hm hmB] at hb
      omega
private theorem raw_fraction_bounds (D s : ℕ) (hs : 1 ≤ s) (p r : ℤ) : reply D ((p : ℚ) / s) = r ↔ r * (s : ℤ) ≤ (D : ℤ) * p ∧ (D : ℤ) * p < (r + 1) * s := by
  have hp : (0 : ℚ) < s := by exact_mod_cast (show 0 < s by omega)
  rw [reply, Int.floor_eq_iff, ← mul_div_assoc, le_div_iff₀ hp, div_lt_iff₀ hp]; exact_mod_cast (Iff.rfl : r * (s : ℤ) ≤ (D : ℤ) * p ∧ (D : ℤ) * p < (r + 1) * s ↔ _)
private theorem raw_fraction_unique (Q : ℕ) (hQ : 1 ≤ Q) (s₁ s₂ : ℕ) (h₁ : 1 ≤ s₁) (h₂ : 1 ≤ s₂) (h₁Q : s₁ ≤ Q) (h₂Q : s₂ ≤ Q) (p₁ p₂ r : ℤ)
    (hr₁ : reply (Q ^ 2) ((p₁ : ℚ) / s₁) = r) (hr₂ : reply (Q ^ 2) ((p₂ : ℚ) / s₂) = r) : (p₁ : ℚ) / s₁ = (p₂ : ℚ) / s₂ := by
  obtain ⟨hl₁, hu₁⟩ := (raw_fraction_bounds (Q ^ 2) s₁ h₁ p₁ r).mp hr₁
  obtain ⟨hl₂, hu₂⟩ := (raw_fraction_bounds (Q ^ 2) s₂ h₂ p₂ r).mp hr₂
  have hs₁ : (0 : ℤ) < s₁ := by exact_mod_cast (show 0 < s₁ by omega)
  have hs₂ : (0 : ℤ) < s₂ := by exact_mod_cast (show 0 < s₂ by omega)
  have hprod : (s₁ : ℤ) * s₂ ≤ (Q : ℤ) ^ 2 := by
    have hh := Nat.mul_le_mul h₁Q h₂Q
    have hc : (s₁ : ℤ) * s₂ ≤ (Q : ℤ) * Q := by exact_mod_cast hh
    nlinarith
  have hD : (0 : ℤ) ≤ (Q : ℤ) ^ 2 := sq_nonneg _; push_cast at hl₁ hu₁ hl₂ hu₂
  have hup : (Q : ℤ) ^ 2 * (p₁ * s₂ - p₂ * s₁) < (s₁ : ℤ) * s₂ := by nlinarith [mul_lt_mul_of_pos_right hu₁ hs₂, mul_le_mul_of_nonneg_right hl₂ hs₁.le]
  have hlo : (Q : ℤ) ^ 2 * (p₂ * s₁ - p₁ * s₂) < (s₁ : ℤ) * s₂ := by nlinarith [mul_lt_mul_of_pos_right hu₂ hs₁, mul_le_mul_of_nonneg_right hl₁ hs₂.le]
  have he : p₁ * s₂ = p₂ * s₁ := by
    apply le_antisymm
    · by_contra h
      have hh : 1 ≤ p₁ * s₂ - p₂ * s₁ := by omega
      have hm := mul_le_mul_of_nonneg_left hh hD; nlinarith
    · by_contra h
      have hh : 1 ≤ p₂ * s₁ - p₁ * s₂ := by omega
      have hm := mul_le_mul_of_nonneg_left hh hD; nlinarith
  apply (div_eq_div_iff (by exact_mod_cast hs₁.ne') (by exact_mod_cast hs₂.ne')).mpr
  exact_mod_cast he

def transportNumerator (A : PositiveMatrix) (j : ℤ) (m : ℕ) : ℤ := (A.a : ℤ) * j + (A.b : ℤ) * m

def transportDenominator (A : PositiveMatrix) (j : ℤ) (m : ℕ) : ℕ := A.c * j.toNat + A.d * m
private theorem transport_bounds {A : PositiveMatrix} (hA : Unimodular A) {B U m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ B) {j : ℤ} (hj : 0 ≤ j) (hjU : j.toNat ≤ m * U) :
    1 ≤ transportDenominator A j m ∧ transportDenominator A j m ≤ B * (A.c * U + A.d) := by
  have hd := (diagonal_positive hA).2
  constructor
  · dsimp [transportDenominator]
    have hdm : 1 ≤ A.d * m := by nlinarith
    omega
  · calc
      transportDenominator A j m ≤ A.c * (m * U) + A.d * m := Nat.add_le_add_right (Nat.mul_le_mul_left A.c hjU) _
      _ = m * (A.c * U + A.d) := by ring
      _ ≤ B * (A.c * U + A.d) := Nat.mul_le_mul_right _ hmB
private theorem transport_value {A : PositiveMatrix} (hA : Unimodular A) {m : ℕ} (hm : 1 ≤ m) {j : ℤ} (hj : 0 < j) : mobius A ((j : ℚ) / m) =
      (transportNumerator A j m : ℚ) / transportDenominator A j m := by
  have hmc : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hjc : (0 : ℚ) < j := by exact_mod_cast hj
  have hjn : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.le
  have hjq : (j.toNat : ℚ) = j := by exact_mod_cast hjn
  have hd : (0 : ℚ) < A.d := by exact_mod_cast (diagonal_positive hA).2
  have hs : (0 : ℚ) < (A.c : ℚ) * j + (A.d : ℚ) * m := by positivity
  dsimp [mobius, transportNumerator, transportDenominator]; push_cast
  rw [hjq]; field_simp
private theorem cut_integer_bounds {I : ProfileCell} (hl : 0 ≤ I.lower) {U m : ℕ} (hm : 1 ≤ m) (hU : I.upper ≤ (U : ℚ)) {j : ℤ}
    (hj : I.lower < (j : ℚ) / m ∧ (j : ℚ) / m < I.upper) : 0 < j ∧ j.toNat ≤ m * U := by
  have hmc : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hjp : (0 : ℚ) < (j : ℚ) / m := hl.trans_lt hj.1; have hjq : (0 : ℚ) < j := (div_pos_iff_of_pos_right hmc).mp hjp
  have hjz : (0 : ℤ) < j := by exact_mod_cast hjq
  have hjupper : (j : ℚ) < (U : ℚ) * m := (div_lt_iff₀ hmc).mp (hj.2.trans_le hU)
  have hjupperZ : j ≤ (m * U : ℕ) := by
    have hh : j < (U : ℤ) * m := by exact_mod_cast hjupper
    push_cast; nlinarith
  exact ⟨hjz, by omega⟩
private theorem first_interval_lower_nonneg (A : PositiveMatrix) (D : ℕ) (I : ProfileCell) (r : ℤ) : 0 ≤ (firstInterval A D I r).lower := by
  exact (le_max_left _ _).trans (le_max_right _ _)
private theorem first_interval_cut_unique {A : PositiveMatrix} (hA : Unimodular A) {B U : ℕ} (hB : 1 ≤ B) {I : ProfileCell} (hl : 0 ≤ I.lower)
    (hU : I.upper ≤ (U : ℚ)) {x : ℚ} (hx : I.Contains x) :
    let Q := B * (A.c * U + A.d); let J := firstInterval A (Q ^ 2) I (reply (Q ^ 2) (mobius A x))
    ∀ j₁ j₂ : ℤ, ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B → 1 ≤ m₂ → m₂ ≤ B → J.lower < (j₁ : ℚ) / m₁ → (j₁ : ℚ) / m₁ < J.upper → J.lower < (j₂ : ℚ) / m₂ → (j₂ : ℚ) / m₂ < J.upper →
      (j₁ : ℚ) / m₁ = (j₂ : ℚ) / m₂ := by
  dsimp only; let Q := B * (A.c * U + A.d)
  let r := reply (Q ^ 2) (mobius A x); let J := firstInterval A (Q ^ 2) I r
  have hQ : 1 ≤ Q := by
    have hd := (diagonal_positive hA).2; dsimp [Q]
    simpa using Nat.mul_le_mul hB (show 1 ≤ A.c * U + A.d by omega)
  have hD : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
  intro j₁ j₂ m₁ m₂ hm₁ hm₁B hm₂ hm₂B hl₁ hu₁ hl₂ hu₂
  have hpos₁ : 0 < (j₁ : ℚ) / m₁ := (first_interval_lower_nonneg A (Q ^ 2) I r).trans_lt hl₁
  have hpos₂ : 0 < (j₂ : ℚ) / m₂ := (first_interval_lower_nonneg A (Q ^ 2) I r).trans_lt hl₂; have hi₁ := (first_interval_exact hA hD hx.1 rfl _).mp ⟨hpos₁, hl₁.le, hu₁⟩
  have hi₂ := (first_interval_exact hA hD hx.1 rfl _).mp ⟨hpos₂, hl₂.le, hu₂⟩
  have hjI₁ : I.lower < (j₁ : ℚ) / m₁ ∧ (j₁ : ℚ) / m₁ < I.upper := by exact ⟨(le_max_left _ _).trans_lt hl₁, hi₁.1.2.2⟩
  have hjI₂ : I.lower < (j₂ : ℚ) / m₂ ∧ (j₂ : ℚ) / m₂ < I.upper := by exact ⟨(le_max_left _ _).trans_lt hl₂, hi₂.1.2.2⟩
  obtain ⟨hj₁, hj₁U⟩ := cut_integer_bounds hl hm₁ hU hjI₁
  obtain ⟨hj₂, hj₂U⟩ := cut_integer_bounds hl hm₂ hU hjI₂
  obtain ⟨hs₁, hs₁Q⟩ := transport_bounds hA hm₁ hm₁B hj₁.le hj₁U
  obtain ⟨hs₂, hs₂Q⟩ := transport_bounds hA hm₂ hm₂B hj₂.le hj₂U
  have hv₁ := transport_value hA hm₁ hj₁; have hv₂ := transport_value hA hm₂ hj₂
  have he := raw_fraction_unique Q hQ _ _ hs₁ hs₂ hs₁Q hs₂Q (transportNumerator A j₁ m₁) (transportNumerator A j₂ m₂) r (by rw [← hv₁]; exact hi₁.2) (by rw [← hv₂]; exact hi₂.2)
  rw [← hv₁, ← hv₂] at he
  rcases lt_trichotomy ((j₁ : ℚ) / m₁) ((j₂ : ℚ) / m₂) with h | h | h
  · exact False.elim ((ne_of_lt (mobius_strict hA hpos₁ hpos₂ h)) he)
  · exact h
  · exact False.elim ((ne_of_lt (mobius_strict hA hpos₂ hpos₁ h)) he.symm)
private theorem interval_representative {C : ProfileCell} {x : ℚ} (hx : C.Contains x) : C.Contains C.representative := by
  dsimp [ProfileCell.Contains, ProfileCell.representative]
  split_ifs with hl
  · exact ⟨hl, le_rfl, hx.2.1.trans_lt hx.2.2⟩
  · have hu : 0 < C.upper := hx.1.trans hx.2.2
    exact ⟨by positivity, by linarith, by linarith⟩
private theorem cell_congr {B : ℕ} {x y : ℚ} (h : SameInstant B x y) : containingCell B x = containingCell B y := by
  induction B with
  | zero => rfl
  | succ n ih =>
    have hl : SameInstant n x y := fun m hm hmB => h m hm (by omega)
    have he := h (n + 1) (by omega) le_rfl
    simp only [containingCell, he, ih hl]

/-- A read-only program has only completed output and actual current read instructions. Its continuation receives the entire integer reply. -/
inductive ProfileProgram where
  | done (output : ProfileCell)
  | read (scale : ℕ) (next : ℤ → ProfileProgram)

def ProfileProgram.execute (z : ℚ) : ProfileProgram → ProfileCell
  | .done C => C
  | .read D next => (next (reply D z)).execute z

/-- Derived values do not produce entries in this actual-read trace. -/
def ProfileProgram.actualReads (z : ℚ) : ProfileProgram → List (ℕ × ℤ)
  | .done _ => []
  | .read D next => (D, reply D z) :: (next (reply D z)).actualReads z

/-- Exact endpoint bounds of a proposed current reply. The upper original endpoint is excluded, hence the ceiling minus one. -/
def determinedReply (A : PositiveMatrix) (C : ProfileCell) (D : ℕ) : Option ℤ :=
  let l := reply D (mobius A C.lower); let h := ⌈(D : ℚ) * mobius A C.upper⌉ - 1
  if l = h then some l else none
private theorem mobius_lower_bound {A : PositiveMatrix} (hA : Unimodular A) {l x : ℚ} (hl : 0 ≤ l) (hx : 0 < x) (hlx : l ≤ x) : mobius A l ≤ mobius A x := by
  have hd : (A.a : ℚ) * A.d - (A.b : ℚ) * A.c = 1 := by
    have he : (A.a : ℚ) * A.d = (A.b : ℚ) * A.c + 1 := by exact_mod_cast hA
    linarith
  have hdpos : (0 : ℚ) < A.d := by exact_mod_cast (diagonal_positive hA).2
  have hpl : 0 < (A.c : ℚ) * l + A.d := by positivity
  dsimp [mobius]; rw [div_le_div_iff₀ hpl (denominator_positive hA hx)]
  have he : ((A.a : ℚ) * x + A.b) * ((A.c : ℚ) * l + A.d) - ((A.a : ℚ) * l + A.b) * ((A.c : ℚ) * x + A.d) = x - l := by linear_combination (x - l) * hd
  linarith
private theorem determined_reply_correct {A : PositiveMatrix} (hA : Unimodular A) {C : ProfileCell} (hl : 0 ≤ C.lower) {D : ℕ} (hD : 1 ≤ D)
    {x : ℚ} (hx : C.Contains x) {r : ℤ} (hr : determinedReply A C D = some r) : reply D (mobius A x) = r := by
  have hp : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlo : reply D (mobius A C.lower) ≤ reply D (mobius A x) := Int.floor_mono (mul_le_mul_of_nonneg_left (mobius_lower_bound hA hl hx.1 hx.2.1) hp.le)
  have hup : reply D (mobius A x) < ⌈(D : ℚ) * mobius A C.upper⌉ := Int.floor_lt_ceil_of_lt (mul_lt_mul_of_pos_left (mobius_strict hA hx.1 (hx.1.trans hx.2.2) hx.2.2) hp)
  dsimp only [determinedReply] at hr
  split_ifs at hr with he
  · have her := Option.some.inj hr
    omega
private theorem threshold_order {A : PositiveMatrix} (hA : Unimodular A) (D : ℕ) (r : ℤ) {y : ℚ} (hy : 0 ≤ y) : ((D : ℚ) * mobius A y < r ↔
      thresholdSlope A D r * y < thresholdIntercept A D r) ∧ ((r : ℚ) < (D : ℚ) * mobius A y ↔ thresholdIntercept A D r < thresholdSlope A D r * y) := by
  have hd : (0 : ℚ) < A.d := by exact_mod_cast (diagonal_positive hA).2
  have hp : 0 < (A.c : ℚ) * y + A.d := by positivity
  dsimp [mobius, thresholdSlope, thresholdIntercept]; rw [← mul_div_assoc, div_lt_iff₀ hp, lt_div_iff₀ hp]
  constructor <;> constructor <;> intro h <;> nlinarith
private theorem determined_reply_exact {A : PositiveMatrix} (hA : Unimodular A) {C : ProfileCell} (hl : 0 ≤ C.lower) {D : ℕ} (hD : 1 ≤ D) {x : ℚ} (hx : C.Contains x) (r : ℤ) :
    determinedReply A C D = some r ↔ ∀ y : ℚ, C.Contains y → reply D (mobius A y) = r := by
  constructor
  · intro hr y hy; exact determined_reply_correct hA hl hD hy hr
  · intro constant
    let l := reply D (mobius A C.lower); let h := ⌈(D : ℚ) * mobius A C.upper⌉ - 1
    have hp : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
    have hlo : l ≤ reply D (mobius A x) := Int.floor_mono (mul_le_mul_of_nonneg_left (mobius_lower_bound hA hl hx.1 hx.2.1) hp.le)
    have hup : reply D (mobius A x) ≤ h := by
      have hh := Int.floor_lt_ceil_of_lt (mul_lt_mul_of_pos_left (mobius_strict hA hx.1 (hx.1.trans hx.2.2) hx.2.2) hp); dsimp [h]
      change reply D (mobius A x) < _ at hh; omega
    have he : l = h := by
      by_contra hn
      have hlt : l < h := by omega
      let j : ℤ := l + 1
      have hjl : (D : ℚ) * mobius A C.lower < j := by simpa only [j, l, reply, Int.cast_add, Int.cast_one] using Int.lt_floor_add_one ((D : ℚ) * mobius A C.lower)
      have hju : (j : ℚ) < (D : ℚ) * mobius A C.upper := by
        apply Int.lt_ceil.mp; dsimp [j, h] at *
        omega
      have hL := (threshold_order hA D j hl).1.mp hjl; have hU := (threshold_order hA D j (hx.1.trans hx.2.2).le).2.mp hju
      have hk : 0 < thresholdSlope A D j := by
        by_contra hn
        have hh := mul_le_mul_of_nonpos_left (hx.2.1.trans_lt hx.2.2).le (le_of_not_gt hn); linarith
      let t := thresholdIntercept A D j / thresholdSlope A D j
      have hlt : C.lower < t := (lt_div_iff₀ hk).mpr (by simpa [mul_comm] using hL)
      have hut : t < C.upper := (div_lt_iff₀ hk).mpr (by simpa [mul_comm] using hU)
      have ht : C.Contains t := ⟨hl.trans_lt hlt, hlt.le, hut⟩; let y := (C.lower + t) / 2
      have hy : C.Contains y := ⟨by dsimp [y]; linarith [ht.1], by dsimp [y]; linarith, by dsimp [y]; linarith⟩
      have hsmall : reply D (mobius A y) < j := by
        apply Int.floor_lt.mpr; apply (threshold_order hA D j hy.1.le).1.mpr
        have htval : thresholdSlope A D j * t = thresholdIntercept A D j := by dsimp [t]; field_simp
        have hyt : y < t := by dsimp [y]; linarith
        have hh := mul_lt_mul_of_pos_left hyt hk; linarith
      have hlarge : j ≤ reply D (mobius A t) := by
        apply Int.le_floor.mpr
        have htval : thresholdSlope A D j * t = thresholdIntercept A D j := by dsimp [t]; field_simp
        have hn : ¬ (D : ℚ) * mobius A t < j := by
          rw [(threshold_order hA D j ht.1.le).1]; linarith
        exact le_of_not_gt hn
      rw [constant y hy] at hsmall; rw [constant t ht] at hlarge
      omega
    have hr : l = r := by
      have hc := constant x hx; omega
    dsimp only [determinedReply]; change (if l = h then some l else none) = some r
    rw [ite_eq_left he, hr]

def readOrDerive (A : PositiveMatrix) (C : ProfileCell) (D : ℕ) (next : ℤ → ProfileProgram) : ProfileProgram := match determinedReply A C D with
  | some r => next r
  | none => .read D next
private theorem read_or_derive_execute {A : PositiveMatrix} (hA : Unimodular A) {C : ProfileCell} (hl : 0 ≤ C.lower) {D : ℕ} (hD : 1 ≤ D)
    {x : ℚ} (hx : C.Contains x) (next : ℤ → ProfileProgram) : (readOrDerive A C D next).execute (mobius A x) = (next (reply D (mobius A x))).execute (mobius A x) := by
  unfold readOrDerive
  cases he : determinedReply A C D with
  | none => rfl
  | some r => rw [determined_reply_correct hA hl hD hx he]
private theorem read_or_derive_trace {A : PositiveMatrix} (hA : Unimodular A) {C : ProfileCell} (hl : 0 ≤ C.lower) {D : ℕ} (hD : 1 ≤ D)
    {x : ℚ} (hx : C.Contains x) (next : ℤ → ProfileProgram) : (readOrDerive A C D next).actualReads (mobius A x) =
      (if determinedReply A C D = none then [(D, reply D (mobius A x))] else []) ++ (next (reply D (mobius A x))).actualReads (mobius A x) := by
  unfold readOrDerive
  cases he : determinedReply A C D with
  | none => simp [ProfileProgram.actualReads]
  | some r =>
      have hr := determined_reply_correct hA hl hD hx he; simp [hr]

def splitInterval (C : ProfileCell) (t : ℚ) (upperSide : Bool) : ProfileCell := if upperSide then ⟨max C.lower t, C.upper⟩ else ⟨C.lower, min C.upper t⟩
private theorem split_interval_exact (C : ProfileCell) (t x : ℚ) (upperSide : Bool) : (splitInterval C t upperSide).Contains x ↔
      C.Contains x ∧ (if upperSide then t ≤ x else x < t) := by
  cases upperSide <;>
    simp only [splitInterval, Bool.false_eq_true, ite_false, ite_true, ProfileCell.Contains, max_le_iff, lt_min_iff]
  <;> tauto
private theorem split_no_cut {B : ℕ} {C : ProfileCell} {j : ℤ} {m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ B) (unique : ∀ j' : ℤ, ∀ m' : ℕ, 1 ≤ m' → m' ≤ B →
      C.lower < (j' : ℚ) / m' → (j' : ℚ) / m' < C.upper → (j' : ℚ) / m' = (j : ℚ) / m) (side : Bool) : ∀ m' : ℕ, 1 ≤ m' → m' ≤ B → ∀ j' : ℤ,
      ¬ ((splitInterval C ((j : ℚ) / m) side).lower < (j' : ℚ) / m' ∧ (j' : ℚ) / m' < (splitInterval C ((j : ℚ) / m) side).upper) := by
  intro m' hm' hm'B j' hh
  cases side
  · simp only [splitInterval, Bool.false_eq_true, ite_false] at hh
    have he := unique j' m' hm' hm'B hh.1 (lt_min_iff.mp hh.2).1; have ht := (lt_min_iff.mp hh.2).2
    exact (lt_irrefl _) (he ▸ ht)
  · simp only [splitInterval, ite_true] at hh
    have he := unique j' m' hm' hm'B (max_lt_iff.mp hh.1).1 hh.2; have ht := (max_lt_iff.mp hh.1).2
    exact (lt_irrefl _) (he ▸ ht)

def originalUpper (I : ProfileCell) : ℕ := (Int.ceil I.upper).toNat

def profileScale (A : PositiveMatrix) (I : ProfileCell) (B : ℕ) : ℕ := B * (A.c * originalUpper I + A.d)

/-- The finite controller receives only the known matrix, earned interval, requested resolution and actual replies. There is no source-valued argument. -/
def acquireProfile (A : PositiveMatrix) (I : ProfileCell) (B : ℕ) : ProfileProgram := if findCut B I = none then .done (fastContainingCell B I.representative) else
    let Q := profileScale A I B
    readOrDerive A I (Q ^ 2) fun r =>
      let J := firstInterval A (Q ^ 2) I r
      match findCut B J with
      | none => .done (fastContainingCell B J.representative)
      | some (j, m) =>
          let s := transportDenominator A j m; let p := transportNumerator A j m
          readOrDerive A J s fun h =>
            let K := splitInterval J ((j : ℚ) / m) (decide (p ≤ h))
            .done (fastContainingCell B K.representative)
private theorem original_upper_bounds {I : ProfileCell} {x : ℚ} (hx : I.Contains x) : 1 ≤ originalUpper I ∧ I.upper ≤ (originalUpper I : ℚ) := by
  have hp : 0 < (Int.ceil I.upper) := Int.ceil_pos.mpr (hx.1.trans hx.2.2); have he : ((Int.ceil I.upper).toNat : ℤ) = Int.ceil I.upper := Int.toNat_of_nonneg hp.le
  constructor
  · dsimp [originalUpper]; omega
  · have he' : (originalUpper I : ℚ) = (Int.ceil I.upper : ℤ) := by
      exact_mod_cast he
    rw [he']; exact Int.le_ceil _
private theorem current_cut_compare {A : PositiveMatrix} (hA : Unimodular A) {j : ℤ} {m : ℕ} (hm : 1 ≤ m) (hj : 0 < j) {x : ℚ} (hx : 0 < x) :
    transportNumerator A j m ≤ reply (transportDenominator A j m) (mobius A x) ↔ (j : ℚ) / m ≤ x := by
  have ht : (0 : ℚ) < (j : ℚ) / m := by
    apply div_pos
    · exact_mod_cast hj
    · exact_mod_cast (show 0 < m by omega)
  have hd : (0 : ℚ) < transportDenominator A j m := by
    have ha : 0 < A.d := (diagonal_positive hA).2; dsimp [transportDenominator]
    positivity
  have he : (transportNumerator A j m ≤ reply (transportDenominator A j m) (mobius A x)) ↔ mobius A ((j : ℚ) / m) ≤ mobius A x := by
    rw [transport_value hA hm hj, div_le_iff₀ hd, reply, Int.le_floor]; simp only [mul_comm]
  rw [he]
  constructor
  · intro h; by_contra hn; exact (not_lt_of_ge h) (mobius_strict hA hx ht (lt_of_not_ge hn))
  · intro h
    rcases lt_or_eq_of_le h with hh | hh
    · exact (mobius_strict hA ht hx hh).le
    · simp [hh]

/-- This trace describes genuine current replies only; its optional singleton may be the second scale when the first reply was derived from earlier evidence. -/
def TwoReplyTrace (Q : ℕ) (z : ℚ) (rows : List (ℕ × ℤ)) : Prop := ∃ s : ℕ, 1 ≤ s ∧ s ≤ Q ∧ (rows = [] ∨ rows = [(Q ^ 2, reply (Q ^ 2) z)] ∨ rows = [(s, reply s z)] ∨
      rows = [(Q ^ 2, reply (Q ^ 2) z), (s, reply s z)])
private theorem acquisition_spec {A : PositiveMatrix} (hA : Unimodular A) {I : ProfileCell} (hl : 0 ≤ I.lower) {B : ℕ} (hB : 1 ≤ B) {x : ℚ} (hx : I.Contains x) :
    (acquireProfile A I B).execute (mobius A x) = containingCell B x ∧ TwoReplyTrace (profileScale A I B) (mobius A x) ((acquireProfile A I B).actualReads (mobius A x)) := by
  obtain ⟨hU, hIU⟩ := original_upper_bounds hx
  let Q := profileScale A I B
  have hQ : 1 ≤ Q := by
    have hd : 0 < A.d := (diagonal_positive hA).2; dsimp [Q, profileScale]
    simpa using Nat.mul_le_mul hB (show 1 ≤ A.c * originalUpper I + A.d by omega)
  have hD : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
  have finish {C : ProfileCell} (hCx : C.Contains x) (hn : ∀ m : ℕ, 1 ≤ m → m ≤ B → ∀ j : ℤ, ¬ (C.lower < (j : ℚ) / m ∧ (j : ℚ) / m < C.upper)) :
      fastContainingCell B C.representative = containingCell B x := by
    rw [fast_containing_cell_eq]; exact cell_congr (no_interior_cut_same hn (interval_representative hCx) hCx)
  unfold acquireProfile
  split_ifs with hstart
  · constructor
    · exact finish hx ((find_cut_spec B I).2 hstart)
    · exact ⟨1, le_rfl, hQ, Or.inl rfl⟩
  · change (readOrDerive A I (Q ^ 2) _).execute (mobius A x) = _ ∧ TwoReplyTrace Q (mobius A x) ((readOrDerive A I (Q ^ 2) _).actualReads (mobius A x))
    rw [read_or_derive_execute hA hl hD hx, read_or_derive_trace hA hl hD hx]; let r := reply (Q ^ 2) (mobius A x)
    let J := firstInterval A (Q ^ 2) I r; have hJ : J.Contains x := (first_interval_exact hA hD hx.1 rfl x).mpr ⟨hx, rfl⟩
    have hJl : 0 ≤ J.lower := first_interval_lower_nonneg A (Q ^ 2) I r
    cases hcut : findCut B J with
    | none =>
      dsimp only; rw [hcut]
      change (ProfileProgram.done (fastContainingCell B J.representative)).execute _ = _ ∧ TwoReplyTrace Q (mobius A x)
          ((if determinedReply A I (Q ^ 2) = none then [(Q ^ 2, r)] else []) ++ [])
      constructor
      · exact finish hJ ((find_cut_spec B J).2 hcut)
      · refine ⟨1, le_rfl, hQ, ?_⟩
        split_ifs <;> simp [r]
    | some cut =>
      obtain ⟨j, m⟩ := cut
      dsimp only; rw [hcut]
      obtain ⟨hm, hmB, hjl, hju⟩ := (find_cut_spec B J).1 j m hcut
      have hjI : I.lower < (j : ℚ) / m ∧ (j : ℚ) / m < I.upper := by
        have hp : 0 < (j : ℚ) / m := hJl.trans_lt hjl; have hi := (first_interval_exact hA hD hx.1 rfl _).mp ⟨hp, hjl.le, hju⟩
        exact ⟨(le_max_left _ _).trans_lt hjl, hi.1.2.2⟩
      obtain ⟨hj, hjU⟩ := cut_integer_bounds hl hm hIU hjI
      obtain ⟨hs, hsQ⟩ := transport_bounds hA hm hmB hj.le hjU
      let s := transportDenominator A j m; let p := transportNumerator A j m
      let h := reply s (mobius A x); let side := decide (p ≤ h)
      let K := splitInterval J ((j : ℚ) / m) side; have hcompare : p ≤ h ↔ (j : ℚ) / m ≤ x := current_cut_compare hA hm hj hx.1
      have hK : K.Contains x := by
        apply (split_interval_exact J ((j : ℚ) / m) x side).mpr; refine ⟨hJ, ?_⟩
        dsimp [side]
        by_cases hh : p ≤ h
        · simpa [hh] using hcompare.mp hh
        · simpa [hh] using (lt_of_not_ge (fun hh' => hh (hcompare.mpr hh')))
      have hKn := split_no_cut hm hmB (fun j' m' hm' hm'B hj'l hj'u =>
          first_interval_cut_unique hA hB hl hIU hx j' j m' m hm' hm'B hm hmB hj'l hj'u hjl hju) side
      change (readOrDerive A J s _).execute (mobius A x) = _ ∧ TwoReplyTrace Q (mobius A x) ((if determinedReply A I (Q ^ 2) = none then [(Q ^ 2, r)] else []) ++
            (readOrDerive A J s _).actualReads (mobius A x))
      rw [read_or_derive_execute hA hJl hs hJ, read_or_derive_trace hA hJl hs hJ]
      constructor
      · exact finish hK hKn
      · refine ⟨s, hs, hsQ, ?_⟩
        change ((if determinedReply A I (Q ^ 2) = none then [(Q ^ 2, r)] else []) ++ ((if determinedReply A J s = none then [(s, h)] else []) ++ [])) = [] ∨ _
        split_ifs <;> simp [r, h, s, ProfileProgram.actualReads]

/-- The finite payload inequalities concern complete actual integer replies. They do not assign time, price or backing to the source service. -/
def BoundedReplies (Q V : ℕ) (rows : List (ℕ × ℤ)) : Prop := ∀ row ∈ rows, 1 ≤ row.1 ∧ row.1 ≤ Q^2 ∧ 0 ≤ row.2 ∧ row.2 < (row.1 : ℤ) * V
private theorem current_value_bounds {A : PositiveMatrix} (hA : Unimodular A) {U : ℕ} {x : ℚ} (hx : 0 < x) (hU : x < U) : 0 < mobius A x ∧ mobius A x < A.a * U + A.b + 1 := by
  have ha : (0 : ℚ) < A.a := by exact_mod_cast (diagonal_positive hA).1
  have hd : (1 : ℚ) ≤ A.d := by exact_mod_cast (diagonal_positive hA).2
  have hn : 0 < (A.a : ℚ) * x + A.b := by positivity
  have hden : 1 ≤ (A.c : ℚ) * x + A.d := by
    have hh : 0 ≤ (A.c : ℚ) * x := by positivity
    linarith
  constructor
  · exact div_pos hn (denominator_positive hA hx)
  · change ((A.a : ℚ) * x + A.b) / ((A.c : ℚ) * x + A.d) < _
    have hh := div_le_self hn.le hden; have hh' := mul_lt_mul_of_pos_left hU ha
    linarith
private theorem bounded_reply {z : ℚ} {V D : ℕ} (hz : 0 < z) (hV : z < V) (hD : 1 ≤ D) : 0 ≤ reply D z ∧ reply D z < (D : ℤ) * V := by
  have hp : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg hp.le hz.le)
  · apply Int.floor_lt.mpr
    push_cast; exact mul_lt_mul_of_pos_left hV hp
private theorem trace_payload {Q V : ℕ} (hQ : 1 ≤ Q) {z : ℚ} (hz : 0 < z) (hV : z < V) {rows : List (ℕ × ℤ)} (trace : TwoReplyTrace Q z rows) : BoundedReplies Q V rows := by
  obtain ⟨s,hs,hsQ,ht⟩ := trace
  have hD : 1 ≤ Q^2 := one_le_pow₀ hQ
  have hQQ : Q ≤ Q^2 := by nlinarith
  have first := bounded_reply hz hV hD; have second := bounded_reply hz hV hs
  push_cast at first
  rcases ht with ht | ht | ht | ht <;> subst rows <;>
    simp [BoundedReplies,hD,hs,hsQ.trans hQQ,first.1,first.2,second.1,second.2]
private theorem endpoint_den_bound (e : GridEndpoint) : e.value.den ≤ e.denominator := by
  have hd : (Rat.divInt e.numerator (e.denominator : ℤ)).den ∣ e.denominator := Int.natCast_dvd_natCast.mp (Rat.den_dvd e.numerator (e.denominator : ℤ))
  have he : e.value = Rat.divInt e.numerator (e.denominator : ℤ) := by
    rw [Rat.divInt_eq_div]; simp only [GridEndpoint.value,Int.cast_natCast]
  rw [he]; exact Nat.le_of_dvd e.positive hd
private theorem containing_cell_denominators (B : ℕ) (hB : 1 ≤ B) (y : ℚ) : (containingCell B y).lower.den ≤ B ∧ (containingCell B y).upper.den ≤ B := by
  induction B with
  | zero => omega
  | succ n ih =>
    have hl := endpoint_den_bound ⟨reply (n+1) y,n+1,Nat.succ_pos n⟩; have hu := endpoint_den_bound ⟨reply (n+1) y+1,n+1,Nat.succ_pos n⟩
    simp only [GridEndpoint.value,Int.cast_add,Int.cast_one] at hl hu
    by_cases hn : n=0
    · subst n
      simp only [containingCell,ite_true,max_def]
      split_ifs <;> constructor <;> (try dsimp only) <;> first | exact hl | exact hu | norm_num
    · obtain ⟨hprevL,hprevU⟩ := ih (by omega)
      simp only [containingCell,ite_eq_right hn,max_def,min_def]
      split_ifs <;> constructor <;> (try dsimp only) <;> omega

/-- Binary widths of the actual scale names and nonnegative complete replies. One delimiter bit per integer is included. Provenance and service work are separate. -/
def replyWidths : List (ℕ × ℤ) → ℕ
  | [] => 0
  | (D,r) :: rows => (Nat.size D + 1) + (Nat.size r.toNat + 1) + replyWidths rows
private theorem product_size (a b : ℕ) : Nat.size (a*b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr; rw [pow_add]
  calc
    a*b ≤ a * 2^Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2^Nat.size a * 2^Nat.size b := mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
private theorem bounded_reply_size {z : ℚ} {V D : ℕ} (hz : 0 < z) (hV : z < V) (hD : 1 ≤ D) : Nat.size (reply D z).toNat ≤ Nat.size D + Nat.size V := by
  obtain ⟨hn,hu⟩ := bounded_reply hz hV hD
  have he : ((reply D z).toNat : ℤ) = reply D z := Int.toNat_of_nonneg hn
  have hn' : (reply D z).toNat < D*V := by
    exact_mod_cast (show ((reply D z).toNat : ℤ) < ((D*V : ℕ) : ℤ) by
      rw [he]; exact_mod_cast hu)
  exact (Nat.size_le_size hn'.le).trans (product_size D V)
private theorem trace_widths {Q V : ℕ} (hQ : 1 ≤ Q) {z : ℚ} (hz : 0 < z) (hV : z < V) {rows : List (ℕ × ℤ)} (trace : TwoReplyTrace Q z rows) :
    replyWidths rows ≤ 6*Nat.size Q + 2*Nat.size V + 4 := by
  obtain ⟨s,hs,hsQ,ht⟩ := trace
  have hd : Nat.size (Q^2) ≤ 2*Nat.size Q := by simpa only [pow_two,two_mul] using product_size Q Q
  have hs' := Nat.size_le_size hsQ; have hr := bounded_reply_size hz hV (one_le_pow₀ hQ : 1 ≤ Q^2)
  have hh := bounded_reply_size hz hV hs
  rcases ht with ht | ht | ht | ht <;> subst rows <;>
    simp only [replyWidths] <;> omega
private theorem containing_cell_bounded (B : ℕ) (hB : 1 ≤ B) (y : ℚ) (U : ℕ) (hU : y < U) : 0 ≤ (containingCell B y).lower ∧ (containingCell B y).upper ≤ U := by
  induction B with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      have hfloor : reply 1 y + 1 ≤ (U : ℤ) := by
        have hh : ⌊y⌋ < (U : ℤ) := Int.floor_lt.mpr hU
        simpa [reply] using (show ⌊y⌋ + 1 ≤ (U : ℤ) by omega)
      simp only [containingCell,ite_true]
      constructor
      · exact le_max_left _ _
      · simpa using (show (reply 1 y : ℚ) + 1 ≤ U by exact_mod_cast hfloor)
    · obtain ⟨hl,hu⟩ := ih (by omega)
      simp only [containingCell,ite_eq_right hn]; exact ⟨hl.trans (le_max_left _ _),(min_le_left _ _).trans hu⟩
private theorem rational_numerator_bound {q : ℚ} (hq : 0 ≤ q) {B U : ℕ} (hd : q.den ≤ B) (hU : q ≤ U) : q.num.natAbs ≤ B*U := by
  have hn : (q.num : ℚ) = q * q.den := by
    calc
      (q.num : ℚ) = ((q.num : ℚ) / q.den) * q.den := (div_mul_cancel₀ _ (by exact_mod_cast q.den_pos.ne')).symm
      _ = q * q.den := by rw [Rat.num_div_den]
  have hb : (q.num : ℚ) ≤ (B*U : ℕ) := by
    rw [hn]; push_cast
    calc
      q * (q.den : ℚ) ≤ (U : ℚ) * q.den := mul_le_mul_of_nonneg_right hU (by positivity)
      _ ≤ (U : ℚ) * B := mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by positivity)
      _ = (B : ℚ) * U := mul_comm _ _
  have hb' : q.num ≤ (B*U : ℕ) := by exact_mod_cast hb
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  exact_mod_cast (show (q.num.natAbs : ℤ) ≤ (B*U : ℕ) by
    rw [Int.natAbs_of_nonneg hnum]; exact hb')
private theorem containing_cell_numerators (B : ℕ) (hB : 1 ≤ B) {y : ℚ} (hy : 0 < y) (U : ℕ) (hU : y < U) : (containingCell B y).lower.num.natAbs ≤ B*U ∧
      (containingCell B y).upper.num.natAbs ≤ B*U := by
  obtain ⟨hl,hu⟩ := containing_cell_bounded B hB y U hU
  have hi := (containing_cell_exact B hB hy y).mpr ⟨hy,fun _ _ _ => rfl⟩
  obtain ⟨hdl,hdu⟩ := containing_cell_denominators B hB y
  exact ⟨rational_numerator_bound hl hdl (hi.2.1.trans (hi.2.2.le.trans hu)), rational_numerator_bound (hy.le.trans hi.2.2.le) hdu hu⟩

/-- Binary magnitude width of a signed integer, without its sign delimiter. -/
def integerWidth (n : ℤ) : ℕ := Nat.size n.natAbs

/-- The larger of the two reduced endpoint-coordinate widths. -/
def rationalWidth (q : ℚ) : ℕ := max (integerWidth q.num) (Nat.size q.den)

def ProfileCell.width (C : ProfileCell) : ℕ := max (rationalWidth C.lower) (rationalWidth C.upper)
private theorem sum_size (a b : ℕ) : Nat.size (a+b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  apply Nat.size_le.mpr; have ha := (Nat.size_le.mp (le_max_left (Nat.size a) (Nat.size b)))
  have hb := (Nat.size_le.mp (le_max_right (Nat.size a) (Nat.size b))); rw [pow_succ]
  omega
private theorem integer_mul_width (a b : ℤ) : integerWidth (a*b) ≤ integerWidth a + integerWidth b := by
  simpa only [integerWidth,Int.natAbs_mul] using product_size a.natAbs b.natAbs
private theorem integer_sub_width (a b : ℤ) : integerWidth (a-b) ≤ max (integerWidth a) (integerWidth b) + 1 := by
  exact (Nat.size_le_size (Int.natAbs_sub_le a b)).trans (sum_size a.natAbs b.natAbs)
private theorem integer_add_one_width (a : ℤ) : integerWidth (a+1) ≤ integerWidth a + 2 := by
  have hh := (Nat.size_le_size (Int.natAbs_add_le a 1)).trans (sum_size a.natAbs 1); simp only [Int.natAbs_one,Nat.size_one] at hh
  dsimp only [integerWidth]; omega
private theorem div_int_width (n d : ℤ) : rationalWidth ((n : ℚ)/d) ≤ max (integerWidth n) (max 1 (integerWidth d)) := by
  rw [← Rat.divInt_eq_div]; apply max_le
  · dsimp only [integerWidth]
    rw [Rat.num_divInt]; have he := Int.natAbs_ediv_le_natAbs (d.sign*n) (d.gcd n)
    have hs : d.sign.natAbs ≤ 1 := by rw [Int.natAbs_sign]; split_ifs <;> omega
    have hn : (d.sign*n).natAbs ≤ n.natAbs := by
      rw [Int.natAbs_mul]
      simpa using Nat.mul_le_mul_right n.natAbs hs
    exact (Nat.size_le_size (he.trans hn)).trans (le_max_left _ _)
  · rw [Rat.den_divInt]
    split_ifs
    · simpa only [Nat.size_one] using (le_max_left 1 (integerWidth d)).trans (le_max_right (integerWidth n) (max 1 (integerWidth d)))
    · exact (Nat.size_le_size (Nat.div_le_self _ _)).trans ((le_max_right 1 (integerWidth d)).trans (le_max_right _ _))
private theorem max_rational_width (x y : ℚ) : rationalWidth (max x y) ≤ max (rationalWidth x) (rationalWidth y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact le_max_left _ _
private theorem min_rational_width (x y : ℚ) : rationalWidth (min x y) ≤ max (rationalWidth x) (rationalWidth y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact le_max_left _ _
  · rw [min_eq_right h]; exact le_max_right _ _
private theorem threshold_width (A : PositiveMatrix) (D : ℕ) (r : ℤ) :
    let mu := Nat.size (max (max A.a A.b) (max A.c A.d)); let H := max (Nat.size D) (integerWidth r) + mu + 1
    integerWidth ((D : ℤ)*A.a-r*A.c) ≤ H ∧ integerWidth (r*A.d-(D : ℤ)*A.b) ≤ H := by
  dsimp only; let mu := Nat.size (max (max A.a A.b) (max A.c A.d))
  have ha : Nat.size A.a ≤ mu := Nat.size_le_size ((le_max_left A.a A.b).trans (le_max_left _ _))
  have hb : Nat.size A.b ≤ mu := Nat.size_le_size ((le_max_right A.a A.b).trans (le_max_left _ _))
  have hc : Nat.size A.c ≤ mu := Nat.size_le_size ((le_max_left A.c A.d).trans (le_max_right _ _))
  have hd : Nat.size A.d ≤ mu := Nat.size_le_size ((le_max_right A.c A.d).trans (le_max_right _ _)); have hDa := integer_mul_width (D : ℤ) A.a
  have hrc := integer_mul_width r A.c; have hrd := integer_mul_width r A.d
  have hDb := integer_mul_width (D : ℤ) A.b; have hlo := integer_sub_width ((D : ℤ)*A.a) (r*A.c)
  have hup := integer_sub_width (r*A.d) ((D : ℤ)*A.b); simp only [integerWidth,Int.natAbs_natCast] at hDa hrc hrd hDb
  dsimp only [integerWidth] at *
  constructor <;> omega
private theorem first_interval_width (A : PositiveMatrix) (D : ℕ) (I : ProfileCell) (r : ℤ) :
    let mu := Nat.size (max (max A.a A.b) (max A.c A.d))
    (firstInterval A D I r).width ≤ max I.width (max (Nat.size D) (integerWidth r) + mu + 3) := by
  dsimp only; let mu := Nat.size (max (max A.a A.b) (max A.c A.d))
  have h₀ := threshold_width A D r; have h₁ := threshold_width A D (r+1)
  have hr := integer_add_one_width r
  have quotient (k : ℤ) : rationalWidth (thresholdIntercept A D k / thresholdSlope A D k) ≤ max (integerWidth (k*A.d-(D : ℤ)*A.b)) (max 1 (integerWidth ((D : ℤ)*A.a-k*A.c))) := by
    convert div_int_width (k*A.d-(D : ℤ)*A.b) ((D : ℤ)*A.a-k*A.c) using 1 <;>
      simp [thresholdIntercept,thresholdSlope]
  have q₀ := quotient r; have q₁ := quotient (r+1)
  have hm₀ := max_rational_width 0 (thresholdIntercept A D r / thresholdSlope A D r)
  have hm₁ := max_rational_width I.lower (max 0 (thresholdIntercept A D r / thresholdSlope A D r))
  have hm₂ := min_rational_width I.upper (thresholdIntercept A D (r+1) / thresholdSlope A D (r+1))
  have hz : rationalWidth 0 = 1 := by norm_num [rationalWidth,integerWidth]
  dsimp only [ProfileCell.width,firstInterval]; dsimp only [ProfileCell.width] at *
  split_ifs <;> omega

/-- The source's lambda(n) is one plus the natural binary magnitude width. -/
def acquisitionWidth (A : PositiveMatrix) (I : ProfileCell) (B e : ℕ) : ℕ := 16*(e + (Nat.size B+1) + (Nat.size (originalUpper I)+1) +
    (Nat.size (max (max A.a A.b) (max A.c A.d))+1) + 1)
private theorem scale_widths (A : PositiveMatrix) (I : ProfileCell) (B : ℕ) :
    let mu := Nat.size (max (max A.a A.b) (max A.c A.d))
    Nat.size (profileScale A I B) ≤ Nat.size B + mu + Nat.size (originalUpper I) + 1 ∧ Nat.size (A.a*originalUpper I+A.b+1) ≤ mu + Nat.size (originalUpper I) + 2 := by
  dsimp only; let U := originalUpper I
  let mu := Nat.size (max (max A.a A.b) (max A.c A.d)); have ha : Nat.size A.a ≤ mu := Nat.size_le_size ((le_max_left A.a A.b).trans (le_max_left _ _))
  have hb : Nat.size A.b ≤ mu := Nat.size_le_size ((le_max_right A.a A.b).trans (le_max_left _ _))
  have hc : Nat.size A.c ≤ mu := Nat.size_le_size ((le_max_left A.c A.d).trans (le_max_right _ _))
  have hd : Nat.size A.d ≤ mu := Nat.size_le_size ((le_max_right A.c A.d).trans (le_max_right _ _)); have hcu := product_size A.c U
  have hau := product_size A.a U; have ht := sum_size (A.c*U) A.d
  have hv := sum_size (A.a*U) A.b; have hv' := sum_size (A.a*U+A.b) 1
  have hq := product_size B (A.c*U+A.d); simp only [Nat.size_one] at hv'
  change Nat.size (B*(A.c*U+A.d)) ≤ _ ∧ _; dsimp only [U,mu] at *
  constructor <;> omega
private theorem first_interval_uniform_width {A : PositiveMatrix} (hA : Unimodular A) {I : ProfileCell} {B : ℕ} (hB : 1 ≤ B) {x : ℚ} (hx : I.Contains x) :
    let Q := profileScale A I B; let J := firstInterval A (Q^2) I (reply (Q^2) (mobius A x))
    ∀ e : ℕ, I.width ≤ e → 4*J.width ≤ acquisitionWidth A I B e := by
  dsimp only; let Q := profileScale A I B
  let D := Q^2; let V := A.a*originalUpper I+A.b+1
  let mu := Nat.size (max (max A.a A.b) (max A.c A.d))
  have hQ : 1 ≤ Q := by
    have hd : 0 < A.d := (diagonal_positive hA).2; dsimp [Q,profileScale]
    simpa using Nat.mul_le_mul hB (show 1 ≤ A.c*originalUpper I+A.d by omega)
  have hD : 1 ≤ D := one_le_pow₀ hQ; have hz := current_value_bounds hA hx.1 (hx.2.2.trans_le (original_upper_bounds hx).2)
  have hzV : mobius A x < (V : ℚ) := by simpa only [V,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hz.2
  have hr := bounded_reply_size hz.1 hzV hD; have hn := (bounded_reply hz.1 hzV hD).1
  have hna := Int.natAbs_of_nonneg hn; have hnt := Int.toNat_of_nonneg hn
  have hnat : (reply D (mobius A x)).natAbs = (reply D (mobius A x)).toNat := by omega
  rw [← hnat] at hr; have hq := (scale_widths A I B).1
  have hv := (scale_widths A I B).2
  have hd : Nat.size D ≤ 2*Nat.size Q := by simpa only [D,pow_two,two_mul] using product_size Q Q
  have hw := first_interval_width A D I (reply D (mobius A x))
  intro e he
  dsimp only [acquisitionWidth,integerWidth,Q,D,V,mu] at *; omega

/-- All integer operands of one original-denominator cut test, including its quotient and cross-products. It contains no rational reduction operation. -/
def cutOperands (C : ProfileCell) (m : ℕ) : List ℤ :=
  let n := (m : ℤ)*C.lower.num; let j := nextNumerator C.lower m
  [(m : ℤ),C.lower.num,C.lower.den,C.upper.num,C.upper.den, n,n/(C.lower.den : ℤ),j,j*(C.upper.den : ℤ),(m : ℤ)*C.upper.num]

def CutOperandWidths (B : ℕ) (C : ProfileCell) (W : ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → m ≤ B → ∀ n ∈ cutOperands C m, integerWidth n ≤ W
private theorem cut_operand_widths (B : ℕ) (C : ProfileCell) : CutOperandWidths B C (Nat.size B + 2*C.width + 2) := by
  intro m hm hmB n hn
  have hs := Nat.size_le_size hmB; have hln : integerWidth C.lower.num ≤ C.width := (le_max_left _ _).trans (le_max_left _ _)
  have hld : Nat.size C.lower.den ≤ C.width := (le_max_right _ _).trans (le_max_left _ _)
  have hun : integerWidth C.upper.num ≤ C.width := (le_max_left _ _).trans (le_max_right _ _)
  have hud : Nat.size C.upper.den ≤ C.width := (le_max_right _ _).trans (le_max_right _ _); have hmul := integer_mul_width (m : ℤ) C.lower.num
  have hmul' := integer_mul_width (m : ℤ) C.upper.num; have hdiv := Nat.size_le_size (Int.natAbs_ediv_le_natAbs ((m : ℤ)*C.lower.num) (C.lower.den : ℤ))
  have hj := integer_add_one_width (((m : ℤ)*C.lower.num)/(C.lower.den : ℤ)); have hcross := integer_mul_width (nextNumerator C.lower m) (C.upper.den : ℤ)
  simp only [integerWidth,Int.natAbs_natCast] at hmul hmul' hcross; change integerWidth (nextNumerator C.lower m) ≤ _ at hj
  dsimp only [integerWidth] at hln hun hj hdiv hld hud; simp only [cutOperands,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [integerWidth,Int.natAbs_natCast] <;> omega
private theorem moving_cut_operand_widths {A : PositiveMatrix} (hA : Unimodular A) {I : ProfileCell} {B : ℕ} (hB : 1 ≤ B) {x : ℚ} (hx : I.Contains x) :
    let Q := profileScale A I B; let J := firstInterval A (Q^2) I (reply (Q^2) (mobius A x))
    ∀ e : ℕ, I.width ≤ e → CutOperandWidths B I (acquisitionWidth A I B e) ∧ CutOperandWidths B J (acquisitionWidth A I B e) := by
  dsimp only
  intro e he
  have hw := first_interval_uniform_width hA hB hx e he; have initial := cut_operand_widths B I
  have current := cut_operand_widths B (firstInterval A ((profileScale A I B)^2) I (reply ((profileScale A I B)^2) (mobius A x)))
  constructor
  · intro m hm hmB n hn
    have hi := initial m hm hmB n hn; dsimp only [acquisitionWidth] at *
    omega
  · intro m hm hmB n hn
    have hi := current m hm hmB n hn; dsimp only [acquisitionWidth] at *
    omega

/-- A superset of integer operands in any endpoint-scan quotient or comparison between two selected grid candidates. The original zero endpoint contributes 0. -/
def gridOperands (y : ℚ) (m n : ℕ) : List ℤ :=
  let p := gridQuotient m y; let q := gridQuotient n y
  [(m : ℤ),(n : ℤ),y.num,y.den,(m : ℤ)*y.num,(n : ℤ)*y.num, p,q,p+1,q+1,p*(n : ℤ),q*(m : ℤ),(p+1)*(n : ℤ),(q+1)*(m : ℤ),0]

def GridOperandWidths (B : ℕ) (y : ℚ) (W : ℕ) : Prop := ∀ m n : ℕ, 1 ≤ m → m ≤ B → 1 ≤ n → n ≤ B → ∀ k ∈ gridOperands y m n, integerWidth k ≤ W
private theorem grid_operand_widths (B : ℕ) (y : ℚ) : GridOperandWidths B y (2*Nat.size B+rationalWidth y+2) := by
  intro m n hm hmB hn hnB k hk
  have hs := Nat.size_le_size hmB; have ht := Nat.size_le_size hnB
  have hnum : integerWidth y.num ≤ rationalWidth y := le_max_left _ _; have hden : Nat.size y.den ≤ rationalWidth y := le_max_right _ _
  have hmul := integer_mul_width (m : ℤ) y.num; have hmul' := integer_mul_width (n : ℤ) y.num
  have hp := Nat.size_le_size (Int.natAbs_ediv_le_natAbs ((m : ℤ)*y.num) (y.den : ℤ)); have hq := Nat.size_le_size (Int.natAbs_ediv_le_natAbs ((n : ℤ)*y.num) (y.den : ℤ))
  have hp' := integer_add_one_width (gridQuotient m y); have hq' := integer_add_one_width (gridQuotient n y)
  have hc₁ := integer_mul_width (gridQuotient m y) (n : ℤ); have hc₂ := integer_mul_width (gridQuotient n y) (m : ℤ)
  have hc₃ := integer_mul_width (gridQuotient m y+1) (n : ℤ); have hc₄ := integer_mul_width (gridQuotient n y+1) (m : ℤ)
  change integerWidth (gridQuotient m y) ≤ integerWidth ((m : ℤ)*y.num) at hp; change integerWidth (gridQuotient n y) ≤ integerWidth ((n : ℤ)*y.num) at hq
  simp only [integerWidth,Int.natAbs_natCast] at *; simp only [gridOperands,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (try simp only [integerWidth,Int.natAbs_natCast,Int.natAbs_zero,Nat.size_zero]) <;> omega
private theorem representative_width (C : ProfileCell) : rationalWidth C.representative ≤ C.width+2 := by
  unfold ProfileCell.representative
  split_ifs with hl
  · exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  · have he : C.upper/2 = (C.upper.num : ℚ)/((2 : ℤ)*C.upper.den) := by
      calc
        C.upper/2 = ((C.upper.num : ℚ)/C.upper.den)/2 := by rw [Rat.num_div_den]
        _ = (C.upper.num : ℚ)/((2 : ℤ)*C.upper.den) := by push_cast; ring
    rw [he]; have hw := div_int_width C.upper.num ((2 : ℤ)*C.upper.den)
    have hm := integer_mul_width 2 (C.upper.den : ℤ); have hn : integerWidth C.upper.num ≤ C.width := (le_max_left _ _).trans (le_max_right _ _)
    have hd : Nat.size C.upper.den ≤ C.width := (le_max_right _ _).trans (le_max_right _ _)
    have htwo : integerWidth 2 = 2 := by decide
    simp only [integerWidth,Int.natAbs_natCast] at hm; dsimp only [integerWidth] at htwo
    push_cast at hw ⊢; dsimp only [integerWidth] at *
    omega
private theorem split_interval_width (C : ProfileCell) (t : ℚ) (side : Bool) : (splitInterval C t side).width ≤ max C.width (rationalWidth t) := by
  have hl := max_rational_width C.lower t; have hu := min_rational_width C.upper t
  dsimp only [ProfileCell.width,splitInterval] at *
  split_ifs <;> dsimp only at * <;> omega
private theorem cut_rational_width {I : ProfileCell} (hl : 0 ≤ I.lower) {B m U : ℕ} (hm : 1 ≤ m) (hmB : m ≤ B) (hU : I.upper ≤ (U : ℚ))
    {j : ℤ} (hj : I.lower < (j : ℚ)/m ∧ (j : ℚ)/m < I.upper) : rationalWidth ((j : ℚ)/m) ≤ Nat.size B+Nat.size U+1 := by
  obtain ⟨hj₀,hjU⟩ := cut_integer_bounds hl hm hU hj
  have hna := Int.natAbs_of_nonneg hj₀.le; have hnt := Int.toNat_of_nonneg hj₀.le
  have hn : j.natAbs = j.toNat := by omega
  have hjabs : j.natAbs ≤ m*U := by rwa [hn]
  have hjw := (Nat.size_le_size hjabs).trans (product_size m U); have hmw := Nat.size_le_size hmB
  have hw := div_int_width j (m : ℤ); simp only [integerWidth,Int.natAbs_natCast,Int.cast_natCast] at hw
  omega

/-- Exact arithmetic trace of the original-denominator cut scan. The counter charges one integer division and one cross-product comparison per step. -/
inductive CutScanRun : ℕ → ProfileCell → Option (ℤ × ℕ) → ℕ → Prop where
  | zero (C) : CutScanRun 0 C none 0
  | found (n : ℕ) (C : ProfileCell) (test : nextNumerator C.lower (n + 1) * (C.upper.den : ℤ) < (n + 1 : ℕ) * C.upper.num) :
      CutScanRun (n + 1) C (some (nextNumerator C.lower (n + 1), n + 1)) 1
  | miss (n : ℕ) (C : ProfileCell) (result : Option (ℤ × ℕ)) (k : ℕ) (test : ¬ nextNumerator C.lower (n + 1) * (C.upper.den : ℤ) < (n + 1 : ℕ) * C.upper.num)
      (tail : CutScanRun n C result k) : CutScanRun (n + 1) C result (k + 1)
private theorem cut_scan_run (B : ℕ) (C : ProfileCell) : ∃ k ≤ B, CutScanRun B C (findCut B C) k := by
  induction B with
  | zero => exact ⟨0,le_rfl,CutScanRun.zero C⟩
  | succ n ih =>
    dsimp only [findCut]
    split_ifs with h
    · exact ⟨1,by omega,CutScanRun.found n C h⟩
    · obtain ⟨k,hk,run⟩ := ih
      exact ⟨k+1,by omega,CutScanRun.miss n C _ k h run⟩

/-- The final endpoint scan makes one division at every original denominator. Its comparison count is one at denominator one and two thereafter. -/
inductive EndpointScanRun : ℕ → ℚ → GridEndpoint × GridEndpoint → ℕ → ℕ → Prop where
  | zero (y) : EndpointScanRun 0 y (zeroEndpoint,oneEndpoint) 0 0
  | first (y : ℚ) : EndpointScanRun 1 y (zeroEndpoint.maximum ⟨gridQuotient 1 y,1,by omega⟩, ⟨gridQuotient 1 y+1,1,by omega⟩) 1 1
  | next (n : ℕ) (hn : 1 ≤ n) (y : ℚ) (C : GridEndpoint × GridEndpoint) (d k : ℕ) (tail : EndpointScanRun n y C d k) : EndpointScanRun (n+1) y
        (C.1.maximum ⟨gridQuotient (n+1) y,n+1,by omega⟩, C.2.minimum ⟨gridQuotient (n+1) y+1,n+1,by omega⟩) (d+1) (k+2)
private theorem endpoint_loop_run (n m : ℕ) (hm : 1 ≤ m) (y : ℚ) (C : GridEndpoint × GridEndpoint) (d k : ℕ) (run : EndpointScanRun m y C d k) :
    EndpointScanRun (m+n) y (endpointScanLoop n m y C) (d+n) (k+2*n) := by
  induction n generalizing m C d k with
  | zero => simpa only [endpointScanLoop,Nat.add_zero,Nat.mul_zero] using run
  | succ n ih =>
    have next := EndpointScanRun.next m hm y C d k run
    have tail := ih (m+1) (by omega) _ (d+1) (k+2) next
    simpa only [endpointScanLoop,Nat.mul_add,Nat.mul_one,Nat.add_assoc, Nat.add_comm,Nat.add_left_comm] using tail
private theorem endpoint_scan_run (B : ℕ) (y : ℚ) : ∃ k ≤ 2*B, EndpointScanRun B y (tailScanEndpoints B y) B k := by
  cases B with
  | zero => exact ⟨0,by omega,EndpointScanRun.zero y⟩
  | succ n =>
    refine ⟨1+2*n,by omega,?_⟩
    simpa only [tailScanEndpoints,Nat.add_comm] using endpoint_loop_run n 1 le_rfl y _ 1 1 (EndpointScanRun.first y)

/-- Original-denominator arithmetic, with all fixed endpoint arithmetic kept outside these counters. The trace is proof data, not an acquired archive. -/
def AcquisitionScans (A : PositiveMatrix) (I : ProfileCell) (B : ℕ) (z : ℚ) (output : ProfileCell) : Prop := ∃ K : ProfileCell, ∃ n₀ n₁ k : ℕ, CutScanRun B I (findCut B I) n₀ ∧
    (if findCut B I = none then n₁ = 0 else
      let Q := profileScale A I B; let J := firstInterval A (Q^2) I (reply (Q^2) z)
      CutScanRun B J (findCut B J) n₁) ∧
    EndpointScanRun B K.representative (tailScanEndpoints B K.representative) B k ∧
    output = fastContainingCell B K.representative ∧
    n₀+n₁+B ≤ 3*B ∧ n₀+n₁+k ≤ 4*B ∧
    ∀ e : ℕ, I.width ≤ e → GridOperandWidths B K.representative (acquisitionWidth A I B e)
private theorem acquisition_scans {A : PositiveMatrix} (hA : Unimodular A) {I : ProfileCell} (hl : 0 ≤ I.lower) {B : ℕ} (hB : 1 ≤ B) {x : ℚ} (hx : I.Contains x) :
    AcquisitionScans A I B (mobius A x) ((acquireProfile A I B).execute (mobius A x)) := by
  have grid_bound {K : ProfileCell} (hw : ∀ e : ℕ, I.width ≤ e → 4*K.width ≤ acquisitionWidth A I B e) : ∀ e : ℕ, I.width ≤ e →
        GridOperandWidths B K.representative (acquisitionWidth A I B e) := by
    intro e he m n hm hmB hn hnB k hk
    have hrun := grid_operand_widths B K.representative m n hm hmB hn hnB k hk; have hrep := representative_width K
    have hkw := hw e he; dsimp only [acquisitionWidth] at *
    omega
  have initial_width : ∀ e : ℕ, I.width ≤ e → 4*I.width ≤ acquisitionWidth A I B e := by
    intro e he
    dsimp only [acquisitionWidth]; omega
  have first_width := first_interval_uniform_width hA hB hx
  obtain ⟨n₀,hn₀,run₀⟩ := cut_scan_run B I
  unfold acquireProfile
  split_ifs with hstart
  · obtain ⟨k,hk,run⟩ := endpoint_scan_run B I.representative
    exact ⟨I,n₀,0,k,run₀,by simp [hstart],run,rfl,by omega,by omega,grid_bound initial_width⟩
  · let Q := profileScale A I B
    have hQ : 1 ≤ Q := by
      have hd : 0 < A.d := (diagonal_positive hA).2; dsimp [Q,profileScale]
      simpa using Nat.mul_le_mul hB (show 1 ≤ A.c * originalUpper I + A.d by omega)
    have hD : 1 ≤ Q^2 := one_le_pow₀ hQ; rw [read_or_derive_execute hA hl hD hx]
    let r := reply (Q^2) (mobius A x); let J := firstInterval A (Q^2) I r
    have hJ : J.Contains x := (first_interval_exact hA hD hx.1 rfl x).mpr ⟨hx,rfl⟩; have hJl := first_interval_lower_nonneg A (Q^2) I r
    obtain ⟨n₁,hn₁,run₁⟩ := cut_scan_run B J
    cases hcut : findCut B J with
    | none =>
      dsimp only; rw [hcut]
      obtain ⟨k,hk,run⟩ := endpoint_scan_run B J.representative
      exact ⟨J,n₀,n₁,k,run₀,by simpa [hstart] using run₁, run,rfl,by omega,by omega,grid_bound first_width⟩
    | some cut =>
      obtain ⟨j,m⟩ := cut
      dsimp only; rw [hcut]
      obtain ⟨hm,hmB,hjl,hju⟩ := (find_cut_spec B J).1 j m hcut
      have hp : 0 < (j : ℚ)/m := hJl.trans_lt hjl; have hi := (first_interval_exact hA hD hx.1 rfl _).mp ⟨hp,hjl.le,hju⟩
      have hjI : I.lower < (j : ℚ)/m ∧ (j : ℚ)/m < I.upper := ⟨(le_max_left _ _).trans_lt hjl,hi.1.2.2⟩
      obtain ⟨hj,hjU⟩ := cut_integer_bounds hl hm (original_upper_bounds hx).2 hjI
      obtain ⟨hs,_⟩ := transport_bounds hA hm hmB hj.le hjU
      let s := transportDenominator A j m; let p := transportNumerator A j m
      rw [read_or_derive_execute hA hJl hs hJ]; let K := splitInterval J ((j : ℚ)/m) (decide (p ≤ reply s (mobius A x)))
      have htwidth := cut_rational_width hl hm hmB (original_upper_bounds hx).2 hjI
      have final_width : ∀ e : ℕ, I.width ≤ e → 4*K.width ≤ acquisitionWidth A I B e := by
        intro e he
        have hjw := first_width e he; change 4*J.width ≤ acquisitionWidth A I B e at hjw
        have hsplit := split_interval_width J ((j : ℚ)/m) (decide (p ≤ reply s (mobius A x))); change K.width ≤ max J.width (rationalWidth ((j : ℚ)/m)) at hsplit
        dsimp only [acquisitionWidth] at *; omega
      obtain ⟨k,hk,run⟩ := endpoint_scan_run B K.representative
      exact ⟨K,n₀,n₁,k,run₀,by simpa [hstart] using run₁, run,rfl,by omega,by omega,grid_bound final_width⟩

/-- Actual acquisition on one authentic chronological prefix. The finite output is exactly the original cell and evaluates every future word and every
scale through the requested bound; the actual-read trace has at most two rows. -/
theorem acquired_original_profile (u : List Bool) (I : ProfileCell) (B : ℕ) (hB : 1 ≤ B) (hl : 0 ≤ I.lower) {x : ℚ} (hx : I.Contains x) :
    let A := wordMatrix u.reverse
    let z := attain u x
    let program := acquireProfile A I B
    let C := program.execute z
    let Q := profileScale A I B
    let J := firstInterval A (Q ^ 2) I (reply (Q ^ 2) z)
    let V := A.a * originalUpper I + A.b + 1
    C = containingCell B x ∧ (∀ y : ℚ, C.Contains y ↔ 0 < y ∧ SameFuture B y x) ∧ (∀ v : List Bool, ∀ m : ℕ, 1 ≤ m → m ≤ B → C.evaluate v m = reply m (attain v x)) ∧
      TwoReplyTrace Q z (program.actualReads z) ∧
      (findCut B I = none ↔ ∀ y : ℚ, I.Contains y → SameFuture B y x) ∧
      (∀ r : ℤ, determinedReply A I (Q ^ 2) = some r ↔ ∀ y : ℚ, I.Contains y → reply (Q ^ 2) (mobius A y) = r) ∧
      (∀ s : ℕ, 1 ≤ s → ∀ r : ℤ, determinedReply A J s = some r ↔ ∀ y : ℚ, J.Contains y → reply s (mobius A y) = r) ∧
      AcquisitionScans A I B z C ∧
      BoundedReplies Q V (program.actualReads z) ∧
      C.lower.den ≤ B ∧ C.upper.den ≤ B ∧
      replyWidths (program.actualReads z) ≤ 6*Nat.size Q + 2*Nat.size V + 4 ∧
      C.lower.num.natAbs ≤ B*originalUpper I ∧ C.upper.num.natAbs ≤ B*originalUpper I ∧
      J.width ≤ max I.width (max (Nat.size (Q^2)) (integerWidth (reply (Q^2) z)) + Nat.size (max (max A.a A.b) (max A.c A.d)) + 3) ∧
      (∀ e : ℕ, I.width ≤ e → 4*J.width ≤ acquisitionWidth A I B e ∧ CutOperandWidths B I (acquisitionWidth A I B e) ∧ CutOperandWidths B J (acquisitionWidth A I B e)) := by
  dsimp only; rw [chronological_matrix u hx.1]
  obtain ⟨he, ht⟩ := acquisition_spec (unimodular_wordMatrix u.reverse) hl hB hx
  let A := wordMatrix u.reverse; have hA := unimodular_wordMatrix u.reverse
  let Q := profileScale A I B
  have hQ : 1 ≤ Q := by
    have hd : 0 < A.d := (diagonal_positive hA).2; dsimp [Q, profileScale]
    simpa using Nat.mul_le_mul hB (show 1 ≤ A.c * originalUpper I + A.d by omega)
  have hD : 1 ≤ Q ^ 2 := one_le_pow₀ hQ; let J := firstInterval A (Q ^ 2) I (reply (Q ^ 2) (mobius A x))
  have hJ : J.Contains x := (first_interval_exact hA hD hx.1 rfl x).mpr ⟨hx,rfl⟩; refine ⟨he, ?_, ?_, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]
    intro y
    rw [containing_cell_exact B hB hx.1 y]
    constructor
    · rintro ⟨hy, hi⟩; exact ⟨hy, (instantaneous_iff_full_future hy hx.1).mp hi⟩
    · rintro ⟨hy, hi⟩; exact ⟨hy, (instantaneous_iff_full_future hy hx.1).mpr hi⟩
  · rw [he]
    exact (containing_cell_evaluator B hB hx.1).2 x ((containing_cell_exact B hB hx.1 x).mpr ⟨hx.1, fun _ _ _ => rfl⟩)
  · rw [target_constant_exact hl hx]
    constructor
    · intro hi y hy; exact (instantaneous_iff_full_future hy.1 hx.1).mp (hi y hy)
    · intro hf y hy; exact (instantaneous_iff_full_future hy.1 hx.1).mpr (hf y hy)
  · intro r; exact determined_reply_exact hA hl hD hx r
  · intro s hs r; exact determined_reply_exact hA (first_interval_lower_nonneg _ _ _ _) hs hJ r
  · exact acquisition_scans hA hl hB hx
  · have hz := current_value_bounds hA hx.1 (hx.2.2.trans_le (original_upper_bounds hx).2)
    apply trace_payload hQ hz.1 _ ht
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hz.2
  · rw [he]; exact (containing_cell_denominators B hB x).1
  · rw [he]; exact (containing_cell_denominators B hB x).2
  · have hz := current_value_bounds hA hx.1 (hx.2.2.trans_le (original_upper_bounds hx).2)
    apply trace_widths hQ hz.1 _ ht
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hz.2
  · rw [he]; exact (containing_cell_numerators B hB hx.1 (originalUpper I) (hx.2.2.trans_le (original_upper_bounds hx).2)).1
  · rw [he]; exact (containing_cell_numerators B hB hx.1 (originalUpper I) (hx.2.2.trans_le (original_upper_bounds hx).2)).2
  · exact first_interval_width _ _ _ _
  · intro e he; exact ⟨first_interval_uniform_width hA hB hx e he, moving_cut_operand_widths hA hB hx e he⟩
end D5.S3.Observer.RationalRouting
