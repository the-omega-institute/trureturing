/- GID: D5/S3/Observer/RationalRouting/FullFutureProfile
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/FullFutureProfile
   mirror-E: none(waiver:uniform-symbolic-profile)
   anchors: []
   utility: none
   digest: A finite floor cell determines every finite chronological future at every bounded scale. -/

import D5.S3.Observer.RationalRouting.Source
import Batteries.Tactic.OpenPrivate

/-! Finite floor vectors and their complete chronological future profiles. -/

set_option autoImplicit false

open private step_control from D5.S3.Observer.RationalRouting.Source

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

/-- The instantaneous vector is a forward congruence, hence determines the
entire unbounded-word profile, including the empty word. -/
theorem instantaneous_iff_full_future {B : ℕ} {x y : ℚ} (hx : 0 < x) (hy : 0 < y) :
    SameInstant B x y ↔ SameFuture B x y := by
  constructor
  · intro h w
    induction w generalizing x y with
    | nil => exact h
    | cons b w ih =>
      exact ih (step_control b hx le_rfl).1 (step_control b hy le_rfl).1
        (instant_step hx hy h b)
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

/-- An unreduced selected endpoint. Proofs of positivity are erased in execution. -/
structure GridEndpoint where
  numerator : ℤ
  denominator : ℕ
  positive : 0 < denominator

def GridEndpoint.value (e : GridEndpoint) : ℚ := (e.numerator : ℚ) / e.denominator

def GridEndpoint.le (e f : GridEndpoint) : Prop :=
  e.numerator * (f.denominator : ℤ) ≤ f.numerator * e.denominator

instance (e f : GridEndpoint) : Decidable (e.le f) := inferInstanceAs (Decidable (_ ≤ _))

def GridEndpoint.maximum (e f : GridEndpoint) : GridEndpoint := if e.le f then f else e
def GridEndpoint.minimum (e f : GridEndpoint) : GridEndpoint := if e.le f then e else f

private theorem endpoint_le (e f : GridEndpoint) : e.le f ↔ e.value ≤ f.value := by
  have he : (0 : ℚ) < e.denominator := by exact_mod_cast e.positive
  have hf : (0 : ℚ) < f.denominator := by exact_mod_cast f.positive
  rw [GridEndpoint.value, GridEndpoint.value, div_le_div_iff₀ he hf]
  exact_mod_cast (Iff.rfl : e.le f ↔ _)

private theorem endpoint_maximum (e f : GridEndpoint) :
    (e.maximum f).value = max e.value f.value := by
  unfold GridEndpoint.maximum
  split_ifs with h
  · exact (max_eq_right ((endpoint_le e f).mp h)).symm
  · exact (max_eq_left (le_of_not_ge (fun hh => h ((endpoint_le e f).mpr hh)))).symm

private theorem endpoint_minimum (e f : GridEndpoint) :
    (e.minimum f).value = min e.value f.value := by
  unfold GridEndpoint.minimum
  split_ifs with h
  · exact (min_eq_left ((endpoint_le e f).mp h)).symm
  · exact (min_eq_right (le_of_not_ge (fun hh => h ((endpoint_le e f).mpr hh)))).symm

def zeroEndpoint : GridEndpoint := ⟨0, 1, by omega⟩
def oneEndpoint : GridEndpoint := ⟨1, 1, by omega⟩

/-- Exactly one integer division at a denominator. No rational is constructed here. -/
def gridQuotient (m : ℕ) (y : ℚ) : ℤ := ((m : ℤ) * y.num) / (y.den : ℤ)

private theorem grid_quotient_eq (m : ℕ) (y : ℚ) : gridQuotient m y = reply m y := by
  rw [gridQuotient, reply, ← Rat.floor_intCast_div_natCast]
  congr 1
  push_cast
  rw [mul_div_assoc, Rat.num_div_den]

def scanEndpoints : ℕ → ℚ → GridEndpoint × GridEndpoint
  | 0, _ => (zeroEndpoint, oneEndpoint)
  | n + 1, y =>
      let j := gridQuotient (n + 1) y
      let l : GridEndpoint := ⟨j, n + 1, Nat.succ_pos n⟩
      let r : GridEndpoint := ⟨j + 1, n + 1, Nat.succ_pos n⟩
      if n = 0 then (zeroEndpoint.maximum l, r)
      else let C := scanEndpoints n y; (C.1.maximum l, C.2.minimum r)

/-- The executable pass is tail recursive. Its state contains the current
index and the two selected pairs, with no list of earlier candidates. -/
def endpointScanLoop : ℕ → ℕ → ℚ → GridEndpoint × GridEndpoint → GridEndpoint × GridEndpoint
  | 0, _, _, C => C
  | n+1, m, y, C =>
      let j := gridQuotient (m+1) y
      let l : GridEndpoint := ⟨j,m+1,Nat.succ_pos m⟩
      let r : GridEndpoint := ⟨j+1,m+1,Nat.succ_pos m⟩
      endpointScanLoop n (m+1) y (C.1.maximum l,C.2.minimum r)

def tailScanEndpoints : ℕ → ℚ → GridEndpoint × GridEndpoint
  | 0, _ => (zeroEndpoint,oneEndpoint)
  | n+1, y =>
      let j := gridQuotient 1 y
      endpointScanLoop n 1 y
        (zeroEndpoint.maximum ⟨j,1,by omega⟩,⟨j+1,1,by omega⟩)

private theorem endpoint_loop_eq (n m : ℕ) (hm : 1 ≤ m) (y : ℚ) :
    endpointScanLoop n m y (scanEndpoints m y) = scanEndpoints (m+n) y := by
  induction n generalizing m with
  | zero => simp [endpointScanLoop]
  | succ n ih =>
    have hm₀ : m ≠ 0 := by omega
    have hs : scanEndpoints (m+1) y =
        ((scanEndpoints m y).1.maximum ⟨gridQuotient (m+1) y,m+1,Nat.succ_pos m⟩,
         (scanEndpoints m y).2.minimum ⟨gridQuotient (m+1) y+1,m+1,Nat.succ_pos m⟩) := by
      simp only [scanEndpoints,ite_eq_right hm₀]
    simp only [endpointScanLoop]
    rw [← hs,ih (m+1) (by omega)]
    congr 1 <;> omega

private theorem tail_scan_eq (B : ℕ) (y : ℚ) : tailScanEndpoints B y = scanEndpoints B y := by
  cases B with
  | zero => rfl
  | succ n =>
    simpa only [tailScanEndpoints,scanEndpoints,ite_true,Nat.one_add] using
      endpoint_loop_eq n 1 le_rfl y


/-- Only the two selected endpoints are converted to reduced rationals. -/
def fastContainingCell (B : ℕ) (y : ℚ) : ProfileCell :=
  let C := tailScanEndpoints B y
  ⟨C.1.value, C.2.value⟩

/-- Integer cross-product selection computes the same exact cell as the
mathematical grid intersection, while avoiding reductions in the scan. -/
theorem fast_containing_cell_eq (B : ℕ) (y : ℚ) :
    fastContainingCell B y = containingCell B y := by
  rw [show fastContainingCell B y =
      (⟨(scanEndpoints B y).1.value,(scanEndpoints B y).2.value⟩ : ProfileCell) by
    simp only [fastContainingCell,tail_scan_eq]]
  induction B with
  | zero => simp [scanEndpoints, GridEndpoint.value,
      zeroEndpoint, oneEndpoint, containingCell]
  | succ n ih =>
    have he₁ := congrArg ProfileCell.lower ih
    have he₂ := congrArg ProfileCell.upper ih
    change (scanEndpoints n y).1.value = (containingCell n y).lower at he₁
    change (scanEndpoints n y).2.value = (containingCell n y).upper at he₂
    by_cases hn : n = 0
    · subst n
      simp only [scanEndpoints, ite_true, endpoint_maximum]
      simp [GridEndpoint.value, zeroEndpoint, grid_quotient_eq, containingCell]
    · simp only [scanEndpoints, ite_eq_right hn,
        endpoint_maximum, endpoint_minimum]
      rw [he₁, he₂]
      simp only [containingCell, ite_eq_right hn, GridEndpoint.value,
        grid_quotient_eq, Int.cast_add, Int.cast_one]

end D5.S3.Observer.RationalRouting
