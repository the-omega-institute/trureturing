/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Exact dyadic mod-ten phases shared by direct small-c2 and quarter-step. -/
import Mathlib.Tactic

/-! Shared private phase proofs, with no arithmetic
feasibility premise and no bounded exponent enumeration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen

private theorem pow2mod10 (d : ℕ) :
    2^d % 10 = if d=0 then 1 else if d%4=0 then 6
      else if d%4=1 then 2 else if d%4=2 then 4 else 8 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have hm := Nat.mod_lt d (by decide : 0<4)
    have hm' := Nat.mod_lt (d+1) (by decide : 0<4)
    split_ifs <;> norm_num at * <;> omega

private theorem phase_cover (d : ℕ) (hd : 3≤d) :
    d=3 ∨ (∃ T : ℕ, 2^d=16+10*T) ∨ (∃ T : ℕ, 2^d=32+10*T) ∨
      (∃ T : ℕ, 2^d=64+10*T) ∨ (∃ T : ℕ, 2^d=128+10*T) := by
  by_cases he : d=3
  · exact Or.inl he
  have hd4 : 4≤d := by omega
  have hm := pow2mod10 d
  have hq := Nat.mod_lt d (by decide : 0<4)
  have phases : d%4=0 ∨ d%4=1 ∨ d%4=2 ∨ d%4=3 := by omega
  rcases phases with h0|h1|h2|h3
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 4≤d by omega)
    have hh : 2^d%10=6 := by simpa [show d≠0 by omega,h0] using hm
    right; left; refine ⟨(2^d-16)/10, ?_⟩
    norm_num at hp
    have := Nat.mod_add_div (2^d-16) 10
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 5≤d by omega)
    have hh : 2^d%10=2 := by simpa [show d≠0 by omega,h1] using hm
    right; right; left; refine ⟨(2^d-32)/10, ?_⟩
    norm_num at hp
    have := Nat.mod_add_div (2^d-32) 10
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 6≤d by omega)
    have hh : 2^d%10=4 := by simpa [show d≠0 by omega,h2] using hm
    right; right; right; left; refine ⟨(2^d-64)/10, ?_⟩
    norm_num at hp
    have := Nat.mod_add_div (2^d-64) 10
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 7≤d by omega)
    have hh : 2^d%10=8 := by simpa [show d≠0 by omega,h3] using hm
    right; right; right; right; refine ⟨(2^d-128)/10, ?_⟩
    norm_num at hp
    have := Nat.mod_add_div (2^d-128) 10
    omega

private theorem quarter_phase_cover (d : ℕ) (hd : 3≤d) :
    (∃ T : ℕ, 2^d=8+10*T) ∨ (∃ T : ℕ, 2^d=16+10*T) ∨
    (∃ T : ℕ, 2^d=32+10*T) ∨ (∃ T : ℕ, 2^d=64+10*T) := by
  rcases phase_cover d hd with he|he|he|he|he
  · left
    refine ⟨0,?_⟩
    rw [he]
    norm_num
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr he))
  · obtain ⟨T,hT⟩ := he
    left
    refine ⟨T+12,?_⟩
    omega

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen
