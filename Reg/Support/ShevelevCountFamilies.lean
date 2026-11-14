import D5.S3.Arith.Primes.ShevelevConjectureForty
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.Support.ShevelevCountFamilies
open _root_.D5.S3.Arith.Primes.ShevelevConjectureForty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature (X : Type) : Signature where
  Params := Unit
  State := fun _ => X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation {X : Type} (f : X → ℕ) : Realization (signature X) :=
  realize (signature X) (fun _ _ x => f x) (fun e => nomatch e)

def arena {X : Type} (law : (X → ℕ) → Prop) : Arena where
  signature := signature X
  Law R := law (R.readout () ())

def assemble {X : Type} (f g : X → ℕ) (law : (X → ℕ) → Prop)
    (statement : Prop) (bridge : statement ↔ law f) (h : statement)
    (bad : ¬law g) (dep : ∃ x y, f x ≠ f y) : Registration (arena law) statement where
  actual := observation f
  bridge := bridge
  variation := ⟨bridge.mp h, observation g, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨observation g, ?_, rfl, bad⟩
      intro j hji
      change Unit at i j
      cases i
      cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨x, y, hxy⟩ := dep
    exact ⟨(), x, y, hxy⟩

@[simp] private theorem prime_count_two : Nat.primeCounting 2 = 1 := by decide

private theorem count_varies : count 0 ≠ count 2 := by decide
private theorem real_count_zero : ramanujanCount (0 : ℝ) = 0 := by
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num, ramanujanCount_nat]
  decide
private theorem real_count_two : ramanujanCount (2 : ℝ) = 1 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ramanujanCount_nat]
  decide
private theorem window_thirteen :
    ∀ t : ℕ, 2 * 13 - 1 ≤ t → t ≤ 2 * 13 + 1 → ¬t.Prime := by
  intro t hlo hhi
  interval_cases t <;> norm_num

namespace subtrahend_le
noncomputable def observed : ℕ → ℕ := fun m => Nat.primeCounting m
def law : (ℕ → ℕ) → Prop := fun f => ∀ m, Nat.primeCounting (m / 2) ≤ f m
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 4
  have hc : Nat.primeCounting (4 / 2) = 1 := by decide
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.subtrahend_le)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.subtrahend_le)
    erased_fails dependence
end subtrahend_le

namespace primeCounting_succ
noncomputable def observed : ℕ → ℕ := fun m => Nat.primeCounting (m + 1)
def law : (ℕ → ℕ) → Prop := fun f => ∀ m, f m = Nat.primeCounting m + if (m + 1).Prime then 1 else 0
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 1
  norm_num at hh
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 1, by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_succ)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_succ)
    erased_fails dependence
end primeCounting_succ

namespace count_succ_le
noncomputable def observed : ℕ → ℕ := count
def law : (ℕ → ℕ) → Prop := fun f => ∀ m, count (m + 1) ≤ f m + 1
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 2
  have hc : count (2 + 1) = 2 := by decide
  rw [hc] at hh
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, count_varies⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_succ_le)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_succ_le)
    erased_fails dependence
end count_succ_le

namespace primeCounting_eq_of_no_prime
noncomputable def observed : ℕ → ℕ := Nat.primeCounting
def law : (ℕ → ℕ) → Prop := fun f => ∀ {a b : ℕ}, a ≤ b → (∀ t, a < t → t ≤ b → ¬t.Prime) → f b = Nat.primeCounting a
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := @h 2 2 le_rfl (by intro t ht ht'; omega)
  have hc : Nat.primeCounting 2 = 1 := by decide
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_eq_of_no_prime)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_eq_of_no_prime)
    erased_fails dependence
end primeCounting_eq_of_no_prime

namespace count_before_double_pos
noncomputable def observed : ℕ → ℕ := fun p => count (2 * p - 1)
def law : (ℕ → ℕ) → Prop := fun f => ∀ {p : ℕ}, p.Prime → 1 ≤ f p
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := @h 2 Nat.prime_two
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_before_double_pos)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_before_double_pos)
    erased_fails dependence
end count_before_double_pos

namespace count_window_left
noncomputable def observed : ℕ × ℕ → ℕ := fun z => count (2 * z.2 - z.1)
def law : (ℕ × ℕ → ℕ) → Prop := fun f => ∀ {H p : ℕ}, 1 ≤ H → (∀ t, 2 * p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime) → count (2 * p - 1) ≤ f (H,p)
noncomputable def erased : ℕ × ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := @h 1 13 (by omega) window_thirteen
  have hc : count (2 * 13 - 1) = 4 := by decide
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨(0,0), (1,13), by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_left)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_left)
    erased_fails dependence
end count_window_left

namespace count_window_right
noncomputable def observed : ℕ × ℕ → ℕ := fun z => count (2 * z.2 + z.1)
def law : (ℕ × ℕ → ℕ) → Prop := fun f => ∀ {H p : ℕ}, p.Prime → (∀ t, 2 * p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime) → f (H,p) < count (2 * p - 1)
noncomputable def erased : ℕ × ℕ → ℕ := fun z => count (2 * z.2 - 1)
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := @h 1 13 (by norm_num) window_thirteen
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨(0,0), (0,2), by decide⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_right)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_right)
    erased_fails dependence
end count_window_right

namespace primeCounting_half_floor_le
noncomputable def observed : ℝ → ℕ := fun x => Nat.primeCounting ⌊x⌋₊
def law : (ℝ → ℕ) → Prop := fun f => ∀ x : ℝ, Nat.primeCounting ⌊x / 2⌋₊ ≤ f x
noncomputable def erased : ℝ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 4
  norm_num at hh
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  refine ⟨0, 2, ?_⟩
  norm_num <;> decide
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_half_floor_le)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_half_floor_le)
    erased_fails dependence
end primeCounting_half_floor_le

namespace ramanujanCount_add_half
noncomputable def observed : ℝ → ℕ := ramanujanCount
def law : (ℝ → ℕ) → Prop := fun f => ∀ x : ℝ, f x + Nat.primeCounting ⌊x / 2⌋₊ = Nat.primeCounting ⌊x⌋₊
noncomputable def erased : ℝ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 2
  norm_num at hh
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by rw [real_count_zero, real_count_two]; omega⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_add_half)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_add_half)
    erased_fails dependence
end ramanujanCount_add_half

namespace ramanujanCount_eq_count_floor
noncomputable def observed : ℝ → ℕ := ramanujanCount
def law : (ℝ → ℕ) → Prop := fun f => ∀ x : ℝ, f x = count ⌊x⌋₊
noncomputable def erased : ℝ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 2
  norm_num only [Nat.floor_ofNat] at hh
  have hc : count 2 = 1 := by decide
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by rw [real_count_zero, real_count_two]; omega⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_eq_count_floor)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_eq_count_floor)
    erased_fails dependence
end ramanujanCount_eq_count_floor

namespace ramanujanCount_nat
noncomputable def observed : ℕ → ℕ := fun m => ramanujanCount m
def law : (ℕ → ℕ) → Prop := fun f => ∀ m : ℕ, f m = count m
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  have hh := h 2
  have hc : count 2 = 1 := by decide
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by simpa only [Nat.cast_zero, Nat.cast_ofNat] using
    (show ramanujanCount (0 : ℝ) ≠ ramanujanCount (2 : ℝ) by
      rw [real_count_zero, real_count_two]; omega)⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_nat)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_nat)
    erased_fails dependence
end ramanujanCount_nat

namespace ramanujanSet_nonempty
noncomputable def observed : ℝ → ℕ := ramanujanCount
def law : (ℝ → ℕ) → Prop := fun f => ∀ n : ℕ, ({m : ℕ | 0 < m ∧ ∀ x : ℝ, (m : ℝ) ≤ x → n ≤ f x} : Set ℕ).Nonempty
noncomputable def erased : ℝ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  obtain ⟨m, hm, hcount⟩ := h 1
  have hh := hcount m le_rfl
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by rw [real_count_zero, real_count_two]; omega⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanSet_nonempty)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanSet_nonempty)
    erased_fails dependence
end ramanujanSet_nonempty

namespace labosSet_nonempty
noncomputable def observed : ℕ → ℕ := fun m => ramanujanCount m
def law : (ℕ → ℕ) → Prop := fun f => ∀ n : ℕ, 1 ≤ n → ({m : ℕ | 0 < m ∧ f m = n} : Set ℕ).Nonempty
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  obtain ⟨m, hm, hcount⟩ := h 1 le_rfl
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  exact ⟨0, 2, by simpa only [Nat.cast_zero, Nat.cast_ofNat] using
    (show ramanujanCount (0 : ℝ) ≠ ramanujanCount (2 : ℝ) by
      rw [real_count_zero, real_count_two]; omega)⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.labosSet_nonempty)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.labosSet_nonempty)
    erased_fails dependence
end labosSet_nonempty

namespace exists_separation
noncomputable def observed : ℕ → ℕ := ramanujanPrime
def law : (ℕ → ℕ) → Prop := fun f => ∀ H : ℕ, ∃ n, 1 ≤ n ∧ labosPrime n + H < f n
noncomputable def erased : ℕ → ℕ := fun _ => 0
theorem erased_fails : ¬law erased := by
  intro h
  dsimp only [law, erased] at h
  obtain ⟨n, hn, hbad⟩ := h 0
  omega
theorem dependence : ∃ x y, observed x ≠ observed y := by
  dsimp only [observed]
  obtain ⟨n, _, hsep⟩ := exists_separation (ramanujanPrime 1)
  exact ⟨1, n, by omega⟩
def targetArena : Arena := arena law
noncomputable def evidence : Registration targetArena (type_of% (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.exists_separation)) :=
  assemble observed erased law _ Iff.rfl (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.exists_separation)
    erased_fails dependence
end exists_separation

end Reg.Support.ShevelevCountFamilies
