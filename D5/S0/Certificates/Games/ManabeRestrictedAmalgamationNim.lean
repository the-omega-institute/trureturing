/- GID: D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/ManabeRestrictedAmalgamationNim
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Restricted amalgamation Nim satisfies Manabe's two-part Grundy conjecture. -/

/- result: proof_shape: content; escape_witness: merger_low_bit.
   admission_basis: open-problem-resolution (#19861; Proved)
   Direct frozen dependencies: D5/S0/Certificates/Games/AbukuEnforceNimberDomination.mex
     statement_id: sha256:a5428f0bcf5c5073cd7c6a65f7783e70f736c5a73a3ab996fabd6f18423d8acc.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20798.
   Private theorem rows (proof_shape; consumers; escape_witness):
     add_xor_and: content; merger_low_bit, even_merge_target; add_xor_and.
     disjoint_add: bind-only; merger_correction; none.
     bouton: bind-only; lower_blocks; none.
     move_decreases: bind-only; grundy_eq, grundy_formula; none.
     grundy_eq: bind-only; grundy_formula; none.
     C_swap: bind-only; F_swap; none.
     C_cycle: bind-only; F_cycle; none.
     F_swap: bind-only; exclusion, last_value, H_swap; none.
     F_cycle: bind-only; lower_blocks, exclusion, last_value, H_cycle; none.
     F_div: bind-only; ordinary_exclusion, merger_exclusion, H_swap, H_cycle; none.
     F_mod: bind-only; ordinary_exclusion, merger_exclusion, last_value; none.
     merger_correction: bind-only; merger_low_bit; none.
     xor_half: bind-only; result; none.
     ordinary_exclusion: bind-only; exclusion; none.
     F_two_choices: bind-only; lower_blocks; none.
     lower_blocks: bind-only; reachability; none.
     merger_low_bit: content; merger_exclusion, even_merge_target; merger_low_bit.
     merger_exclusion: content; exclusion; merger_low_bit.
     exclusion: content; grundy_formula; merger_low_bit.
     H_swap: bind-only; last_value; none.
     H_cycle: bind-only; last_value; none.
     odd_target: bind-only; last_value; none.
     even_merge_target: content; last_value; merger_low_bit.
     last_value: content; reachability; merger_low_bit.
     reachability: content; grundy_formula; merger_low_bit.
     grundy_formula: content; exact_formula; merger_low_bit.
     low_value_lt: bind-only; exact_formula, result; none.
     exact_formula: content; result; merger_low_bit.
   Definitions: move, size, grundy, claim; private B, E, C, H, L, F,
     and the private arithmetic decidability instance decidableC.
   The move relation, size, guarded recursion, and claim retain the source
   expressions specified at https://github.com/the-omega-institute/trureturing/issues/19861.
   The existing mex is used directly; no mex definition is introduced here.
   The exact formula is a private step proving the public two-part conjecture.
-/

import D5.S0.Certificates.Games.AbukuEnforceNimberDomination
import Mathlib.Data.Nat.Bitwise
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false


/-! Binding conventions for H. Manabe, "An Amalgamation Nim with Restriction", arXiv:2411.14488v1. Definition 4: a
player either "chooses a pile and removes any number of stones from the pile" or "can replace two piles with a single
pile containing the total number of stones in the original two piles when the numbers of stones in two piles are equal
to or more than 2". Definition 5 lists the options of `(x, y, z)` as the union of the sets (1)–(6). The Grundy number is
the mex of the Grundy numbers of the options (`mex` is the frozen owner
`D5.S0.Certificates.Games.AbukuEnforceNimberDomination.mex`). Section 3, Conjecture 1: "(i) If the Grundy number of a
position (x, y, z) is 2n, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1. (ii) If the Grundy number of a position (x, y, z)
is 2n + 1, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1." -/

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

open D5.S0.Certificates.Games.AbukuEnforceNimberDomination (mex)

/-- Definition 5: `move(x, y, z)`, the union of (1)–(6). -/
def move (x y z : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {q | (∃ u, u < x ∧ q = (u, y, z)) ∨ (∃ v, v < y ∧ q = (x, v, z)) ∨ (∃ w, w < z ∧ q = (x, y, w)) ∨
    (2 ≤ x ∧ 2 ≤ y ∧ (q = (x + y, 0, z) ∨ q = (0, x + y, z))) ∨
    (2 ≤ y ∧ 2 ≤ z ∧ (q = (x, y + z, 0) ∨ q = (x, 0, y + z))) ∨
    (2 ≤ x ∧ 2 ≤ z ∧ (q = (x + z, y, 0) ∨ q = (0, y, x + z)))}

/-- The total number of stones plus the number of nonempty piles; every move lowers it. -/
def size (x y z : ℕ) : ℕ :=
  x + y + z + (if x = 0 then 0 else 1) + (if y = 0 then 0 else 1) + (if z = 0 then 0 else 1)

/-- The Grundy number of `(x, y, z)`: the mex of the Grundy numbers of the positions in `move(x, y, z)`. Every option
has smaller `size`; the `if` only guards the recursion and is inactive on options. -/
noncomputable def grundy (x y z : ℕ) : ℕ :=
  mex {g | ∃ q ∈ move x y z,
    g = if size q.1 q.2.1 q.2.2 < size x y z then grundy q.1 q.2.1 q.2.2 else 0}
termination_by size x y z

/-- Conjecture 1 (i) and (ii). -/
def claim : Prop :=
  ∀ x y z n : ℕ,
    (grundy x y z = 2 * n → x ^^^ y ^^^ z = 2 * n ∨ x ^^^ y ^^^ z = 2 * n + 1) ∧
    (grundy x y z = 2 * n + 1 → x ^^^ y ^^^ z = 2 * n ∨ x ^^^ y ^^^ z = 2 * n + 1)

end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim


namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

private theorem add_xor_and (a b : ℕ) : a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · simp [ha]
    have hi := ih (a / 2) (by omega) (b / 2)
    have ax : a = Nat.bit (a % 2 = 1) (a / 2) := by
      simpa only [Nat.shiftRight_one] using (Nat.bit_decide_mod_two_eq_one_shiftRight_one a).symm
    have bx : b = Nat.bit (b % 2 = 1) (b / 2) := by
      simpa only [Nat.shiftRight_one] using (Nat.bit_decide_mod_two_eq_one_shiftRight_one b).symm
    conv_lhs => rw [ax, bx]
    conv_rhs => rw [ax, bx, Nat.xor_bit, Nat.land_bit]
    cases ha' : decide (a % 2 = 1) <;> cases hb' : decide (b % 2 = 1) <;>
      simp only [ha', hb', Bool.bne_false, Bool.false_bne, Bool.bne_true,
        Bool.true_bne, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and,
        Bool.not_false, Bool.not_true, Nat.bit_false, Nat.bit_true] <;> omega

private theorem disjoint_add (a b c : ℕ) (h : a &&& b = 0) :
    (a + b) &&& c = 0 ↔ a &&& c = 0 ∧ b &&& c = 0 := by
  have ha : a < 2 ^ (a + b) := lt_of_le_of_lt (Nat.le_add_right a b) Nat.lt_two_pow_self
  have hb : b < 2 ^ (a + b) := lt_of_le_of_lt (Nat.le_add_left b a) Nat.lt_two_pow_self
  let x := BitVec.ofNat (a + b) a
  let y := BitVec.ofNat (a + b) b
  have hxy : x &&& y = 0 := by
    simp [x, y, ← BitVec.ofNat_and, h]
  have heq := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero x y hxy)
  rw [BitVec.toNat_add_of_and_eq_zero hxy, BitVec.toNat_or] at heq
  have hs : a + b = a ||| b := by
    simpa [x, y, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq
  rw [hs, Nat.and_or_distrib_right]
  constructor
  · intro he
    have h1 := Nat.left_le_or (n := a &&& c) (m := b &&& c)
    have h2 := Nat.right_le_or (n := a &&& c) (m := b &&& c)
    rw [he] at h1 h2
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1,h2⟩
    simp [h1,h2]

private theorem bouton (a b c r : ℕ) (hr : r < a ^^^ b ^^^ c) :
    (∃ u < a, u ^^^ b ^^^ c = r) ∨
    (∃ v < b, a ^^^ v ^^^ c = r) ∨
    (∃ w < c, a ^^^ b ^^^ w = r) := by
  rcases Nat.lt_xor_cases hr with hab | hc
  · rcases Nat.lt_xor_cases hab with ha | hb
    · left
      refine ⟨r ^^^ c ^^^ b, ha, ?_⟩
      simp [Nat.xor_assoc]
    · right; left
      refine ⟨r ^^^ c ^^^ a, hb, ?_⟩
      rw [Nat.xor_comm (r ^^^ c) a, Nat.xor_xor_cancel_left, Nat.xor_xor_cancel_right]
  · right; right
    refine ⟨r ^^^ (a ^^^ b), hc, ?_⟩
    simp [Nat.xor_comm, Nat.xor_left_comm]

end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim
open D5.S0.Certificates.Games.AbukuEnforceNimberDomination (mex)

private theorem move_decreases {x y z : ℕ} {q : ℕ × ℕ × ℕ} (hq : q ∈ move x y z) :
    size q.1 q.2.1 q.2.2 < size x y z := by
  rcases hq with ⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩ | ⟨w,hw,rfl⟩ |
    ⟨hx,hy,rfl | rfl⟩ | ⟨hy,hz,rfl | rfl⟩ | ⟨hx,hz,rfl | rfl⟩ <;>
    simp only [size] <;> split_ifs <;> omega

private theorem grundy_eq (x y z : ℕ) :
    grundy x y z = mex {g | ∃ q ∈ move x y z, g = grundy q.1 q.2.1 q.2.2} := by
  rw [grundy]
  congr 1
  ext g
  constructor <;> rintro ⟨q,hq,hg⟩ <;>
    exact ⟨q,hq,by simpa only [ite_eq_left (move_decreases hq)] using hg⟩

private def B (a b c : ℕ) : Prop :=
    (0 < a ∧ 0 < b ∧ a &&& b = 0) ∨
    (0 < a ∧ 0 < c ∧ a &&& c = 0) ∨
    (0 < b ∧ 0 < c ∧ b &&& c = 0)
private def E (a b c : ℕ) : Prop :=
    0 < a ∧ 0 < b ∧ 0 < c ∧ a &&& b = 0 ∧ a &&& c = 0 ∧ b &&& c = 0
private def C (a b c : ℕ) : Prop := B a b c ∧ ¬ E a b c
private instance decidableC (a b c : ℕ) : Decidable (C a b c) := by unfold C B E; infer_instance
private def H (x y z : ℕ) : ℕ := x/2 ^^^ y/2 ^^^ z/2
private def L (x y z : ℕ) : ℕ := (x+y+z+(if C (x/2) (y/2) (z/2) then 1 else 0))%2
private def F (x y z : ℕ) : ℕ := 2 * H x y z + L x y z

private theorem C_swap (a b c : ℕ) : C a b c ↔ C b a c := by
  simp only [C, B, E, Nat.and_comm b a]
  tauto
private theorem C_cycle (a b c : ℕ) : C a b c ↔ C b c a := by
  simp only [C, B, E, Nat.and_comm b a, Nat.and_comm c a]
  tauto
private theorem F_swap (x y z : ℕ) : F x y z = F y x z := by
  simp only [F,H,L, C_swap (x/2) (y/2) (z/2), Nat.xor_comm (x/2) (y/2), Nat.add_comm x y]
private theorem F_cycle (x y z : ℕ) : F x y z = F y z x := by
  simp only [F,H,L, C_cycle (x/2) (y/2) (z/2)]
  congr 2
  · simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]
  · omega

private theorem F_div (x y z : ℕ) : F x y z / 2 = H x y z := by
  simpa only [F, L, Nat.mod_div_self, Nat.add_zero] using
    (Nat.mul_add_div (by decide : 0 < 2) (H x y z) (L x y z))
private theorem F_mod (x y z : ℕ) : F x y z % 2 = L x y z := by
  simpa only [F, L, Nat.mod_mod] using
    (Nat.mul_add_mod_self_left 2 (H x y z) (L x y z))

private theorem merger_correction (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a &&& b = 0) :
    (C a b c ↔ ¬ E a b c) ∧ (C (a+b) 0 c ↔ E a b c) := by
  have hs : 0 < a+b := by exact Nat.add_pos_right a hb
  constructor
  · simp [C,B,ha,hb,hab]
  · simp [C,B,E,ha,hb,hab,hs,disjoint_add a b c hab]

private theorem xor_half (x y z : ℕ) : (x ^^^ y ^^^ z)/2 = H x y z := by
  simp only [Nat.xor_div_two,H]

end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

private theorem ordinary_exclusion (x y z u : ℕ) (hu : u < x) : F u y z ≠ F x y z := by
  intro he
  have hh : H u y z = H x y z := by
    simpa only [F_div] using congrArg (fun n : ℕ => n/2) he
  have hux : u/2 = x/2 := by
    simpa only [H,Nat.xor_left_inj] using hh
  have hm : L u y z = L x y z := by
    simpa only [F_mod] using congrArg (fun n : ℕ => n%2) he
  simp only [L,hux] at hm
  omega

private theorem F_two_choices (b y z r : ℕ) (hh : b ^^^ y/2 ^^^ z/2 = r) :
    (F (2*b) y z = 2*r ∧ F (2*b+1) y z = 2*r+1) ∨
    (F (2*b) y z = 2*r+1 ∧ F (2*b+1) y z = 2*r) := by
  have h0 : H (2*b) y z = r := by simpa [H] using hh
  have h1 : H (2*b+1) y z = r := by
    simp only [H,show (2*b+1)/2=b by simpa using (Nat.mul_add_div (by decide : 0 < 2) b 1)]
    exact hh
  have hc : (2*b)/2 = (2*b+1)/2 := by
    rw [Nat.mul_div_cancel_left b (by decide : 0 < 2), Nat.mul_add_div (by decide : 0 < 2)] <;> rfl
  unfold F L
  rw [h0,h1,hc]
  omega

private theorem lower_blocks (x y z k : ℕ) (hk : k < 2 * H x y z) :
    ∃ q ∈ move x y z, F q.1 q.2.1 q.2.2 = k := by
  have hr : k/2 < H x y z := by exact Nat.div_lt_of_lt_mul hk
  rcases bouton (x/2) (y/2) (z/2) (k/2) hr with
    ⟨u,hu,he⟩ | ⟨v,hv,he⟩ | ⟨w,hw,he⟩
  · have h0 : 2*u < x := by omega
    have h1 : 2*u+1 < x := by omega
    rcases F_two_choices u y z (k/2) he with h | h
    · by_cases hp : k%2=0
      · exact ⟨(2*u,y,z),Or.inl ⟨_,h0,rfl⟩,by dsimp; omega⟩
      · exact ⟨(2*u+1,y,z),Or.inl ⟨_,h1,rfl⟩,by dsimp; omega⟩
    · by_cases hp : k%2=0
      · exact ⟨(2*u+1,y,z),Or.inl ⟨_,h1,rfl⟩,by dsimp; omega⟩
      · exact ⟨(2*u,y,z),Or.inl ⟨_,h0,rfl⟩,by dsimp; omega⟩
  · have he' : v ^^^ z/2 ^^^ x/2 = k/2 := by
      rw [← he]
      simp [Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm]
    have h0 : 2*v < y := by omega
    have h1 : 2*v+1 < y := by omega
    have hswap0 : F x (2*v) z = F (2*v) z x := F_cycle _ _ _
    have hswap1 : F x (2*v+1) z = F (2*v+1) z x := F_cycle _ _ _
    rcases F_two_choices v z x (k/2) he' with h | h
    · by_cases hp : k%2=0
      · exact ⟨(x,2*v,z),Or.inr (Or.inl ⟨_,h0,rfl⟩),by dsimp; omega⟩
      · exact ⟨(x,2*v+1,z),Or.inr (Or.inl ⟨_,h1,rfl⟩),by dsimp; omega⟩
    · by_cases hp : k%2=0
      · exact ⟨(x,2*v+1,z),Or.inr (Or.inl ⟨_,h1,rfl⟩),by dsimp; omega⟩
      · exact ⟨(x,2*v,z),Or.inr (Or.inl ⟨_,h0,rfl⟩),by dsimp; omega⟩
  · have he' : w ^^^ x/2 ^^^ y/2 = k/2 := by
      rw [← he]
      simp [Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm]
    have h0 : 2*w < z := by omega
    have h1 : 2*w+1 < z := by omega
    have hswap0 : F x y (2*w) = F (2*w) x y := (F_cycle _ _ _).symm
    have hswap1 : F x y (2*w+1) = F (2*w+1) x y := (F_cycle _ _ _).symm
    rcases F_two_choices w x y (k/2) he' with h | h
    · by_cases hp : k%2=0
      · exact ⟨(x,y,2*w),Or.inr (Or.inr (Or.inl ⟨_,h0,rfl⟩)),by dsimp; omega⟩
      · exact ⟨(x,y,2*w+1),Or.inr (Or.inr (Or.inl ⟨_,h1,rfl⟩)),by dsimp; omega⟩
    · by_cases hp : k%2=0
      · exact ⟨(x,y,2*w+1),Or.inr (Or.inr (Or.inl ⟨_,h1,rfl⟩)),by dsimp; omega⟩
      · exact ⟨(x,y,2*w),Or.inr (Or.inr (Or.inl ⟨_,h0,rfl⟩)),by dsimp; omega⟩
end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

private theorem merger_low_bit (x y z : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hh : H (x+y) 0 z = H x y z) :
    L (x+y) 0 z ≠ L x y z := by
  have hs : (x+y)/2 = x/2 ^^^ y/2 := by
    simpa only [H, Nat.zero_div, Nat.xor_zero, Nat.xor_left_inj] using hh
  have ha := add_xor_and (x/2) (y/2)
  have hab : x/2 &&& y/2 = 0 := by omega
  have hs' : (x+y)/2 = x/2+y/2 := by omega
  have hc := merger_correction (x/2) (y/2) (z/2) (by omega) (by omega) hab
  intro he
  simp only [L,Nat.zero_add,Nat.add_zero,Nat.zero_div,hs',hc.1,hc.2] at he
  by_cases hee : E (x/2) (y/2) (z/2) <;> simp_all only [not_true_eq_false,
    not_false_eq_true,ite_true,ite_false] <;> omega

private theorem merger_exclusion (x y z : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    F (x+y) 0 z ≠ F x y z := by
  intro he
  have hh : H (x+y) 0 z = H x y z := by
    simpa only [F_div] using congrArg (fun n : ℕ => n/2) he
  have hm : L (x+y) 0 z = L x y z := by
    simpa only [F_mod] using congrArg (fun n : ℕ => n%2) he
  exact merger_low_bit x y z hx hy hh hm

private theorem exclusion (x y z : ℕ) {q : ℕ × ℕ × ℕ} (hq : q ∈ move x y z) :
    F q.1 q.2.1 q.2.2 ≠ F x y z := by
  rcases hq with ⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩ | ⟨w,hw,rfl⟩ |
    ⟨hx,hy,rfl | rfl⟩ | ⟨hy,hz,rfl | rfl⟩ | ⟨hx,hz,rfl | rfl⟩
  · exact ordinary_exclusion x y z u hu
  · simpa only [F_swap x v z,F_swap x y z] using ordinary_exclusion y x z v hv
  · rw [← F_cycle w x y, ← F_cycle z x y]
    exact ordinary_exclusion z x y w hw
  · exact merger_exclusion x y z hx hy
  · simpa only [F_swap 0 (x+y) z] using merger_exclusion x y z hx hy
  · simpa only [← F_cycle x y z, ← F_cycle x (y+z) 0] using merger_exclusion y z x hy hz
  · have hf : F x 0 (y+z) = F (y+z) 0 x := by
      rw [F_cycle, F_swap]
    rw [hf,F_cycle x y z]
    exact merger_exclusion y z x hy hz
  · have hf : F (x+z) y 0 = F (x+z) 0 y := by
      rw [F_cycle,F_swap,← F_cycle]
    rw [hf,F_swap x y z, F_cycle y x z]
    exact merger_exclusion x z y hx hz
  · have hf : F 0 y (x+z) = F (x+z) 0 y := (F_cycle _ _ _).symm
    rw [hf,F_swap x y z, F_cycle y x z]
    exact merger_exclusion x z y hx hz
end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

private theorem H_swap (x y z : ℕ) : H x y z = H y x z := by
  simpa only [F_div] using congrArg (fun n : ℕ => n/2) (F_swap x y z)
private theorem H_cycle (x y z : ℕ) : H x y z = H y z x := by
  simpa only [F_div] using congrArg (fun n : ℕ => n/2) (F_cycle x y z)

private theorem odd_target (x y z : ℕ) (hx : x%2=1) (hl : L x y z=1) :
    x-1 < x ∧ F (x-1) y z = 2 * H x y z := by
  have he : (x-1)/2=x/2 := by omega
  constructor
  · omega
  · have hh : H (x-1) y z = H x y z := by simp only [H,he]
    unfold F
    rw [hh]
    simp only [L,he] at hl ⊢
    omega

private theorem even_merge_target (x y z : ℕ) (hx : 2≤x) (hy : 2≤y)
    (hxe : x%2=0) (hye : y%2=0) (hab : x/2 &&& y/2 = 0) (hl : L x y z=1) :
    F (x+y) 0 z = 2 * H x y z := by
  have hs : (x+y)/2=x/2 ^^^ y/2 := by
    have ha := add_xor_and (x/2) (y/2)
    rw [hab] at ha
    omega
  have hh : H (x+y) 0 z = H x y z := by simp [H,hs]
  have hn := merger_low_bit x y z hx hy hh
  have hlt : L (x+y) 0 z < 2 := by exact Nat.mod_lt _ (by decide)
  unfold F
  rw [hh]
  omega

private theorem last_value (x y z : ℕ) (hl : L x y z = 1) :
    ∃ q ∈ move x y z, F q.1 q.2.1 q.2.2 = 2 * H x y z := by
  by_cases hx : x%2=1
  · have ho := odd_target x y z hx hl
    exact ⟨(x-1,y,z), Or.inl ⟨_,ho.1,rfl⟩, ho.2⟩
  by_cases hy : y%2=1
  · have hl' : L y x z = 1 := by
      have he := congrArg (fun n : ℕ => n%2) (F_swap x y z)
      simp only [F_mod] at he
      omega
    have ho := odd_target y x z hy hl'
    refine ⟨(x,y-1,z), Or.inr (Or.inl ⟨_,ho.1,rfl⟩), ?_⟩
    dsimp
    rw [F_swap,H_swap]
    exact ho.2
  by_cases hz : z%2=1
  · have hl' : L z x y = 1 := by
      have he := congrArg (fun n : ℕ => n%2) (F_cycle z x y)
      simp only [F_mod] at he
      omega
    have ho := odd_target z x y hz hl'
    refine ⟨(x,y,z-1), Or.inr (Or.inr (Or.inl ⟨_,ho.1,rfl⟩)), ?_⟩
    dsimp
    rw [← F_cycle (z-1) x y, ← H_cycle z x y]
    exact ho.2
  have hxe : x%2=0 := by exact Nat.mod_two_ne_one.mp hx
  have hye : y%2=0 := by exact Nat.mod_two_ne_one.mp hy
  have hze : z%2=0 := by exact Nat.mod_two_ne_one.mp hz
  have hc : C (x/2) (y/2) (z/2) := by
    by_contra hn
    simp only [L,ite_eq_right hn] at hl
    omega
  rcases hc.1 with ⟨ha,hb,hab⟩ | ⟨ha,hc,hac⟩ | ⟨hb,hc,hbc⟩
  · have ha' : 2≤x := by omega
    have hb' : 2≤y := by omega
    exact ⟨(x+y,0,z), Or.inr (Or.inr (Or.inr (Or.inl ⟨ha',hb',Or.inl rfl⟩))),
      even_merge_target x y z ha' hb' hxe hye hab hl⟩
  · have ha' : 2≤x := by omega
    have hc' : 2≤z := by omega
    have hs : F x z y = F x y z := by rw [F_swap, F_cycle]
    have hls : L x z y = 1 := by
      have hm := congrArg (fun n : ℕ => n%2) hs
      simp only [F_mod] at hm
      omega
    have ho := even_merge_target x z y ha' hc' hxe hze hac hls
    refine ⟨(0,y,x+z), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨ha',hc',Or.inr rfl⟩)))), ?_⟩
    dsimp
    rw [← F_cycle (x+z) 0 y]
    have hh : H x z y=H x y z := by simpa only [F_div] using congrArg (fun n : ℕ=>n/2) hs
    omega
  · have hb' : 2≤y := by omega
    have hc' : 2≤z := by omega
    have hls : L y z x=1 := by
      have hm := congrArg (fun n : ℕ=>n%2) (F_cycle x y z)
      simp only [F_mod] at hm
      omega
    have ho := even_merge_target y z x hb' hc' hye hze hbc hls
    refine ⟨(x,y+z,0), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hb',hc',Or.inl rfl⟩)))), ?_⟩
    dsimp
    rw [F_cycle x (y+z) 0, H_cycle x y z]
    exact ho

private theorem reachability (x y z k : ℕ) (hk : k < F x y z) :
    ∃ q ∈ move x y z, F q.1 q.2.1 q.2.2 = k := by
  by_cases h : k < 2 * H x y z
  · exact lower_blocks x y z k h
  · have hlt : L x y z < 2 := by exact Nat.mod_lt _ (by decide)
    have hl : L x y z = 1 := by unfold F at hk; omega
    have he : k=2*H x y z := by unfold F at hk; omega
    rw [he]
    exact last_value x y z hl
end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim

namespace D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim
open D5.S0.Certificates.Games.AbukuEnforceNimberDomination (mex)

private theorem grundy_formula (x y z : ℕ) : grundy x y z = F x y z := by
  induction hn : size x y z using Nat.strong_induction_on generalizing x y z with
  | h n ih =>
    rw [grundy_eq]
    have heq : {g | ∃ q ∈ move x y z, g = grundy q.1 q.2.1 q.2.2} =
        {g | ∃ q ∈ move x y z, g = F q.1 q.2.1 q.2.2} := by
      ext g
      constructor <;> rintro ⟨q,hq,hg⟩ <;>
        have hi := ih (size q.1 q.2.1 q.2.2) (hn ▸ move_decreases hq)
          q.1 q.2.1 q.2.2 rfl
      · exact ⟨q,hq,hg.trans hi⟩
      · exact ⟨q,hq,hg.trans hi.symm⟩
    rw [heq]
    have hnot : F x y z ∉ {g | ∃ q ∈ move x y z, g = F q.1 q.2.1 q.2.2} := by
      rintro ⟨q,hq,he⟩
      exact exclusion x y z hq he.symm
    change sInf _ = F x y z
    refine (csInf_eq_iff ⟨_,hnot⟩ _).2 ⟨hnot,?_⟩
    intro k hk
    by_contra hn
    obtain ⟨q,hq,he⟩ := reachability x y z k (by omega)
    exact hk ⟨q,hq,he.symm⟩

private theorem low_value_lt (x y z : ℕ) :
    (x%2 ^^^ y%2 ^^^ z%2) ^^^ (if C (x/2) (y/2) (z/2) then 1 else 0) < 2 := by
  have hp : x%2 ^^^ y%2 ^^^ z%2 < 2^1 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by omega) (by omega)) (by omega)
  have hd : (if C (x/2) (y/2) (z/2) then 1 else 0) < 2^1 := by
    split_ifs <;> omega
  exact Nat.xor_lt_two_pow hp hd

private theorem exact_formula (x y z : ℕ) :
    grundy x y z = 2 * H x y z +
      ((x%2 ^^^ y%2 ^^^ z%2) ^^^ (if C (x/2) (y/2) (z/2) then 1 else 0)) := by
  have hb := low_value_lt x y z
  have hxy := Nat.xor_mod_two_eq (m:=x%2) (n:=y%2)
  have hxyz := Nat.xor_mod_two_eq (m:=x%2 ^^^ y%2) (n:=z%2)
  have hp : x%2 ^^^ y%2 < 2^1 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hp' : x%2 ^^^ y%2 ^^^ z%2 < 2^1 := Nat.xor_lt_two_pow hp (by omega)
  have hd := Nat.xor_mod_two_eq (m:=x%2 ^^^ y%2 ^^^ z%2)
    (n:=if C (x/2) (y/2) (z/2) then 1 else 0)
  rw [grundy_formula]
  unfold F L
  omega

theorem result : D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim.claim := by
  intro x y z n
  have hv := exact_formula x y z
  have hb := low_value_lt x y z
  have hh : grundy x y z / 2 = (x ^^^ y ^^^ z)/2 := by
    rw [xor_half]
    omega
  constructor <;> intro hg <;> rw [hg] at hh <;> omega

end D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim
