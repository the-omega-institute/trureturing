/- GID: D5/S3/Combinatorics/PatternMatchings/P13Machine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Machine
   mirror-E: none(waiver:normalized-survivor-constraints)
   anchors: []
   utility: none
   digest: Arbitrary-size normalized survivor constraints give explicit ranked-scan transitions. -/

import D5.S3.Combinatorics.PatternMatchings.P13Local

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

/-- Post-closure base states. New openings are counted separately. -/
inductive Base
  | S (m : ℕ)
  | T (a b : ℕ)
  deriving DecidableEq

/-- The number of old survivors. -/
def Base.size : Base → ℕ
  | .S m => m
  | .T a b => a + b

/-- The first-block boundary; a single block has boundary zero. -/
def Base.cut : Base → ℕ
  | .S _ => 0
  | .T a _ => a

/-- Two-block states have both blocks nonempty. -/
def Base.Valid : Base → Prop
  | .S _ => True
  | .T a b => 0 < a ∧ 0 < b

/-- Future precedence: each block decreases, and the older block comes first. -/
def Before (a x y : ℕ) : Prop :=
  (x < a ∧ a ≤ y) ∨ (y < x ∧ (x < a ↔ y < a))

/-- Delete empty blocks from a two-block description. -/
def blocks (a b : ℕ) : Base :=
  if a = 0 then .S b else if b = 0 then .S a else .T a b

/-- A zero-based closing rank is legal by the explicit local transition rules. -/
def Permitted (s : Base) (k r : ℕ) : Prop :=
  r < s.size + k ∧ match s with
  | .S m => m ≤ r + 1
  | .T a _ => r + 1 = a

/-- The new base includes all survivors of the closure, including pending openers. -/
def afterClose (s : Base) (k r : ℕ) : Base :=
  blocks r (s.size + k - r - 1)

/-- Compatibility with every old precedence constraint: an old selected arc
must come first, and every old comparison among survivors must be preserved. -/
def Compatible (s : Base) (k r : ℕ) : Prop :=
  r < s.size + k ∧
  (r < s.size → ∀ j, j < s.size → j ≠ r → Before s.cut r j) ∧
  (∀ x y, x < s.size → y < s.size → x ≠ r → y ≠ r →
    Before s.cut x y → Before r x y)

/-- The explicit S/T rank rules are exactly preservation of all old comparisons. -/
theorem compatible_iff (s : Base) (k r : ℕ) (hs : s.Valid) :
    Compatible s k r ↔ Permitted s k r := by
  cases s with
  | S m =>
    simp only [Compatible, Permitted, Base.size, Base.cut]
    constructor
    · rintro ⟨hr, hfirst, hp⟩
      refine ⟨hr, ?_⟩
      by_contra hm
      have hrm : r < m := by omega
      have hh := hfirst hrm (r + 1) (by omega) (by omega)
      unfold Before at hh
      omega
    · rintro ⟨hr, hm⟩
      refine ⟨hr, ?_, ?_⟩
      · intro hrm j hj hne
        unfold Before
        omega
      · intro x y hx hy hxr hyr hxy
        unfold Before at hxy ⊢
        omega
  | T a b =>
    change 0 < a ∧ 0 < b at hs
    simp only [Compatible, Permitted, Base.size, Base.cut]
    constructor
    · rintro ⟨hr, hfirst, hp⟩
      refine ⟨hr, ?_⟩
      by_cases hold : r < a + b
      · by_cases hra : r < a
        · by_contra he
          have hh := hfirst hold (a - 1) (by omega) (by omega)
          unfold Before at hh
          omega
        · have hh := hfirst hold (a - 1) (by omega) (by omega)
          unfold Before at hh
          omega
      · have hh := hp (a - 1) a (by omega) (by omega) (by omega) (by omega)
          (by unfold Before; omega)
        unfold Before at hh
        omega
    · rintro ⟨hr, ha⟩
      refine ⟨hr, ?_, ?_⟩
      · intro hold j hj hne
        unfold Before
        omega
      · intro x y hx hy hxr hyr hxy
        unfold Before at hxy ⊢
        omega

/-- The old index of a survivor after deleting rank r. -/
def liftRank (r x : ℕ) : ℕ := if x < r then x else x + 1

/-- Deletion preserves the two-block ordering on surviving indices. -/
theorem before_lift (r x y : ℕ) :
    Before r (liftRank r x) (liftRank r y) ↔ Before r x y := by
  unfold Before liftRank
  split_ifs <;> omega

/-- Normalizing empty blocks preserves size, validity and every comparison. -/
theorem blocks_spec (a b : ℕ) :
    (blocks a b).size = a + b ∧ (blocks a b).Valid ∧
    ∀ x y, x < a + b → y < a + b →
      (Before (blocks a b).cut x y ↔ Before a x y) := by
  unfold blocks
  split_ifs with ha hb
  · subst a
    simp [Base.size, Base.Valid, Base.cut]
  · subst b
    simp only [Base.size, Nat.add_zero, Base.Valid, Base.cut, true_and]
    intro x y hx hy
    unfold Before
    omega
  · simp only [Base.size, Base.Valid, Base.cut, true_and]
    exact ⟨⟨by omega, by omega⟩, fun _ _ _ _ => trivial⟩

/-- The transition has the correct survivor height and preserves all prior
comparisons after the actual deletion of its selected rank. -/
theorem transition_spec (s : Base) (k r : ℕ) (hs : s.Valid)
    (hr : Permitted s k r) :
    (afterClose s k r).size + 1 = s.size + k ∧
    (afterClose s k r).Valid ∧
    (∀ x y, x < (afterClose s k r).size → y < (afterClose s k r).size →
      (Before (afterClose s k r).cut x y ↔
        Before r (liftRank r x) (liftRank r y))) ∧
    Compatible s k r := by
  have hb := blocks_spec r (s.size + k - r - 1)
  have hsize : r + (s.size + k - r - 1) + 1 = s.size + k := by
    have := hr.1
    omega
  refine ⟨?_, hb.2.1, ?_, (compatible_iff s k r hs).mpr hr⟩
  · change (blocks r (s.size + k - r - 1)).size + 1 = _
    omega
  · intro x y hx hy
    exact (hb.2.2 x y (by change x < (blocks _ _).size at hx; omega)
      (by change y < (blocks _ _).size at hy; omega)).trans (before_lift r x y).symm

/-- A vertex opens, or closes the zero-based active rank r. -/
inductive Step
  | opening
  | closing (r : ℕ)
  deriving DecidableEq

/-- Independent acceptance by local S/T transitions, with pending openings k.
The empty suffix requires no old or pending survivors. -/
def AcceptFrom : Base → ℕ → List Step → Prop
  | s, k, [] => s.size = 0 ∧ k = 0
  | s, k, .opening :: w => AcceptFrom s (k + 1) w
  | s, k, .closing r :: w => Permitted s k r ∧ AcceptFrom (afterClose s k r) 0 w

/-- Full accepted scans of the 2n vertices, starting with an empty base. -/
def Accepted (n : ℕ) := {w : List Step // w.length = 2 * n ∧ AcceptFrom (.S 0) 0 w}

end D5.S3.Combinatorics.PatternMatchings.P13
