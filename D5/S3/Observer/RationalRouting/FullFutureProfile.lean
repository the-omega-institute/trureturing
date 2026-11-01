/- GID: D5/S3/Observer/RationalRouting/FullFutureProfile
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/FullFutureProfile
   mirror-E: none(waiver:uniform-symbolic-profile)
   anchors: []
   utility: none
   digest: A finite floor cell determines every finite chronological future at every bounded scale. -/

import D5.S3.Observer.RationalRouting.Source

/-! Finite floor vectors and their complete chronological future profiles. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

/-- The complete integer reply at an arbitrary installed scale. -/
def reply (m : ℕ) (x : ℚ) : ℤ := ⌊(m : ℚ) * x⌋

/-- Equality at every original denominator, with no divisibility restriction. -/
def SameInstant (B : ℕ) (x y : ℚ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ B → reply m x = reply m y

/-- All finite future words are quantified; none is executed by this definition. -/
def SameFuture (B : ℕ) (x y : ℚ) : Prop :=
  ∀ w : List Bool, SameInstant B (attain w x) (attain w y)

private theorem left_threshold (m j : ℤ) {x : ℚ} (hx : 0 < x)
    (hj : j < m) :
    (j ≤ ⌊(m : ℚ) * (x / (1 + x))⌋ ↔
      j ≤ ⌊((m - j : ℤ) : ℚ) * x⌋) := by
  rw [Int.le_floor, Int.le_floor]
  have hd : 0 < 1 + x := by linarith
  rw [← mul_div_assoc, le_div_iff₀ hd]
  push_cast
  constructor <;> intro h <;> nlinarith

private theorem left_reply_bounds (m : ℕ) {x : ℚ} (hx : 0 < x) (hm : 1 ≤ m) :
    0 ≤ reply m (step false x) ∧ reply m (step false x) < (m : ℤ) := by
  have hd : 0 < 1 + x := by linarith
  have hl : 0 < x / (1 + x) := div_pos hx hd
  have hu : x / (1 + x) < 1 := (div_lt_one hd).mpr (by linarith)
  have hm' : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  constructor
  · apply Int.floor_nonneg.mpr
    change 0 ≤ (m : ℚ) * (x / (1 + x))
    positivity
  · apply Int.floor_lt.mpr
    change (m : ℚ) * (x / (1 + x)) < ((m : ℤ) : ℚ)
    norm_cast
    nlinarith

private theorem instant_step {B : ℕ} {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h : SameInstant B x y) (b : Bool) : SameInstant B (step b x) (step b y) := by
  intro m hm hB
  cases b
  · have hxb := left_reply_bounds m hx hm
    have hyb := left_reply_bounds m hy hm
    have threshold : ∀ j : ℤ, 0 ≤ j → j < m →
        (j ≤ reply m (step false x) ↔ j ≤ reply m (step false y)) := by
      intro j hj hjm
      have hn : 1 ≤ (m - j).toNat := by omega
      have hnB : (m - j).toNat ≤ B := by omega
      have he : (((m : ℤ) - j).toNat : ℤ) = (m : ℤ) - j :=
        Int.toNat_of_nonneg (by omega)
      have hv := h _ hn hnB
      change ⌊((_ : ℕ) : ℚ) * x⌋ = ⌊((_ : ℕ) : ℚ) * y⌋ at hv
      have hc : (((m : ℤ) - j).toNat : ℚ) = ((m : ℤ) - j : ℤ) := by
        exact_mod_cast he
      rw [hc] at hv
      change (j ≤ ⌊(m : ℚ) * (x / (1 + x))⌋ ↔
        j ≤ ⌊(m : ℚ) * (y / (1 + y))⌋)
      have htx := left_threshold (m : ℤ) j hx hjm
      have hty := left_threshold (m : ℤ) j hy hjm
      simp only [Int.cast_natCast] at htx hty
      rw [htx, hty, hv]
    apply le_antisymm
    · exact (threshold _ hxb.1 hxb.2).mp le_rfl
    · exact (threshold _ hyb.1 hyb.2).mpr le_rfl
  · change ⌊(m : ℚ) * (x + 1)⌋ = ⌊(m : ℚ) * (y + 1)⌋
    simp only [mul_add, mul_one, Int.floor_add_natCast]
    exact congrArg (fun z : ℤ => z + m) (h m hm hB)

private theorem step_positive (b : Bool) {x : ℚ} (hx : 0 < x) : 0 < step b x := by
  cases b <;> dsimp [step]
  · exact div_pos hx (by linarith)
  · linarith

/-- The instantaneous vector is a forward congruence, hence determines the
entire unbounded-word profile, including the empty word. -/
theorem instantaneous_iff_full_future {B : ℕ} {x y : ℚ} (hx : 0 < x) (hy : 0 < y) :
    SameInstant B x y ↔ SameFuture B x y := by
  constructor
  · intro h w
    induction w generalizing x y with
    | nil => exact h
    | cons b w ih =>
      exact ih (step_positive b hx) (step_positive b hy) (instant_step hx hy h b)
  · intro h
    exact h []

/-- Finite rational endpoints. A zero lower endpoint is always excluded. -/
structure ProfileCell where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

def ProfileCell.Contains (C : ProfileCell) (x : ℚ) : Prop :=
  0 < x ∧ C.lower ≤ x ∧ x < C.upper

/-- One pass over the original denominators; the extrema remain selected
grid endpoints, rather than a tuple of all reports. -/
def containingCell : ℕ → ℚ → ProfileCell
  | 0, _ => ⟨0, 1⟩
  | n + 1, y =>
      let j := reply (n + 1) y
      let l := (j : ℚ) / (n + 1 : ℕ)
      let r := ((j : ℚ) + 1) / (n + 1 : ℕ)
      if n = 0 then ⟨max 0 l, r⟩
      else let C := containingCell n y; ⟨max C.lower l, min C.upper r⟩

private theorem grid_cell (m : ℕ) (hm : 1 ≤ m) (x y : ℚ) :
    reply m x = reply m y ↔
      (reply m y : ℚ) / m ≤ x ∧ x < ((reply m y : ℚ) + 1) / m := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [reply, Int.floor_eq_iff, div_le_iff₀ hp, lt_div_iff₀ hp]
  simp only [mul_comm]

/-- The finite endpoint scan describes exactly one whole instantaneous class. -/
theorem containing_cell_exact (B : ℕ) (hB : 1 ≤ B) {y : ℚ} (hy : 0 < y) (x : ℚ) :
    (containingCell B y).Contains x ↔ 0 < x ∧ SameInstant B x y := by
  induction B with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      change (0 < x ∧ max 0 ((reply 1 y : ℚ) / 1) ≤ x ∧
        x < ((reply 1 y : ℚ) + 1) / 1) ↔ _
      simp only [max_le_iff]
      constructor
      · rintro ⟨hx, ⟨_, hl⟩, hu⟩
        refine ⟨hx, ?_⟩
        intro m hm hmB
        have he : m = 1 := by omega
        subst m
        exact (grid_cell 1 le_rfl x y).mpr ⟨hl, hu⟩
      · rintro ⟨hx, h⟩
        have hc := (grid_cell 1 le_rfl x y).mp (h 1 le_rfl le_rfl)
        exact ⟨hx, ⟨hx.le, hc.1⟩, hc.2⟩
    · have hn' : 1 ≤ n := by omega
      simp only [containingCell, if_neg hn, ProfileCell.Contains, max_le_iff, lt_min_iff]
      rw [show (0 < x ∧ ((containingCell n y).lower ≤ x ∧
          (reply (n + 1) y : ℚ) / (n + 1 : ℕ) ≤ x) ∧
          x < (containingCell n y).upper ∧
          x < ((reply (n + 1) y : ℚ) + 1) / (n + 1 : ℕ)) ↔
        ((containingCell n y).Contains x ∧
          (reply (n + 1) y : ℚ) / (n + 1 : ℕ) ≤ x ∧
          x < ((reply (n + 1) y : ℚ) + 1) / (n + 1 : ℕ)) by
            simp only [ProfileCell.Contains]; tauto]
      rw [ih hn', ← grid_cell (n + 1) (by omega) x y]
      constructor
      · rintro ⟨⟨hx, h⟩, hlast⟩
        refine ⟨hx, ?_⟩
        intro m hm hmB
        by_cases he : m = n + 1
        · simpa [he] using hlast
        · exact h m hm (by omega)
      · rintro ⟨hx, h⟩
        exact ⟨⟨hx, fun m hm hmB => h m hm (by omega)⟩,
          h (n + 1) (by omega) le_rfl⟩

/-- A positive included endpoint, or a rational interior point of the zero slice. -/
def ProfileCell.representative (C : ProfileCell) : ℚ :=
  if 0 < C.lower then C.lower else C.upper / 2

def ProfileCell.evaluate (C : ProfileCell) (w : List Bool) (m : ℕ) : ℤ :=
  reply m (attain w C.representative)

/-- The finite cell contains its computable representative and evaluates every
future coordinate correctly, uniformly over all positive sources in that cell. -/
theorem containing_cell_evaluator (B : ℕ) (hB : 1 ≤ B) {y : ℚ} (hy : 0 < y) :
    (containingCell B y).Contains (containingCell B y).representative ∧
    ∀ x : ℚ, (containingCell B y).Contains x → ∀ w : List Bool,
      ∀ m : ℕ, 1 ≤ m → m ≤ B →
        (containingCell B y).evaluate w m = reply m (attain w x) := by
  let C := containingCell B y
  have hself : C.Contains y := (containing_cell_exact B hB hy y).mpr
    ⟨hy, fun _ _ _ => rfl⟩
  have hrep : C.Contains C.representative := by
    dsimp [ProfileCell.Contains, ProfileCell.representative]
    split_ifs with hl
    · exact ⟨hl, le_rfl, hself.2.1.trans_lt hself.2.2⟩
    · have hu : 0 < C.upper := hy.trans hself.2.2
      exact ⟨by positivity, by linarith, by linarith⟩
  refine ⟨hrep, ?_⟩
  intro x hx w m hm hmB
  have hr := (containing_cell_exact B hB hy C.representative).mp hrep
  have hxy := (containing_cell_exact B hB hy x).mp hx
  have hi : SameInstant B C.representative x := by
    intro n hn hnB
    exact (hr.2 n hn hnB).trans (hxy.2 n hn hnB).symm
  exact ((instantaneous_iff_full_future hr.1 hxy.1).mp hi w) m hm hmB

end D5.S3.Observer.RationalRouting
