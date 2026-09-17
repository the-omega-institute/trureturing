/- GID: D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas, mathlib/module/Mathlib.Data.Nat.Prime.Basic]
   utility: none
   digest: A square that remains square after prepending one and appending twenty-five ends in 00 or 56. -/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic

/-!
# Squares with a prefixed one and suffixed twenty-five

For a positive natural number `x`, `(Nat.digits 10 x).length` is its number of
base-ten digits. Thus `10 ^ (d + 2) + 100 * x + 25`, with that value of `d`,
is literally the base-ten number obtained by prepending `1` to `x` and
appending `25`.

The proof of Chai Wah Wu's OEIS A249621 conjecture first writes the resulting
square root as `5 * u`. Removing the leading power of ten modulo `10000` and
cancelling `25` gives `u^2 = 4*z^2 + 1` modulo `400`. Complete residue checks
modulo `25` and modulo `8` then force `z^2` to be `0` or `56` modulo `100`.
-/

namespace D5.S1.Digit.Admissibility.SquarePrependOneAppendTwentyFive

/-- Literal membership in OEIS A249621: `x` is a square and the number formed
by prepending `1` and appending `25` in base ten is also a square. -/
def IsMember (x : ℕ) : Prop :=
  (∃ z : ℕ, x = z ^ 2) ∧
    ∃ y : ℕ,
      y ^ 2 = 10 ^ ((Nat.digits 10 x).length + 2) + 100 * x + 25

private theorem square_mod_hundred_of_mod_four_hundred (z u : ℕ)
    (h : u ^ 2 ≡ 4 * z ^ 2 + 1 [MOD 400]) :
    z ^ 2 % 100 = 0 ∨ z ^ 2 % 100 = 56 := by
  have h25 := h.of_dvd (by norm_num : 25 ∣ 400)
  have h8 := h.of_dvd (by norm_num : 8 ∣ 400)
  have hz25 : z ^ 2 % 25 = 0 ∨ z ^ 2 % 25 = 6 := by
    have hzlt := Nat.mod_lt z (by norm_num : 0 < 25)
    have hult := Nat.mod_lt u (by norm_num : 0 < 25)
    rw [Nat.ModEq] at h25
    interval_cases hz : z % 25 <;>
      interval_cases hu : u % 25 <;>
      norm_num [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, hz, hu] at h25 <;>
      norm_num [Nat.pow_mod, hz]
  have hz2 : z % 2 = 0 := by
    have hzlt := Nat.mod_lt z (by norm_num : 0 < 8)
    have hult := Nat.mod_lt u (by norm_num : 0 < 8)
    rw [Nat.ModEq] at h8
    interval_cases hz : z % 8 <;>
      interval_cases hu : u % 8 <;>
      norm_num [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, hz, hu] at h8 <;>
      rw [← Nat.mod_mod_of_dvd z (by norm_num : 2 ∣ 8), hz]
  have hz25eq : z % 25 = z % 100 % 25 :=
    (Nat.mod_mod_of_dvd z (by norm_num : 25 ∣ 100)).symm
  have hz2eq : z % 2 = z % 100 % 2 :=
    (Nat.mod_mod_of_dvd z (by norm_num : 2 ∣ 100)).symm
  have hz100lt := Nat.mod_lt z (by norm_num : 0 < 100)
  interval_cases hz : z % 100 <;>
    norm_num [hz] at hz25eq hz2eq <;>
    simp_all [Nat.pow_mod]

/-- Wu's A249621 conjecture: every positive member ends in `00` or `56`. -/
theorem wu_a249621 :
    ∀ x : ℕ, 0 < x → IsMember x → x % 100 = 0 ∨ x % 100 = 56 := by
  intro x hx hmember
  rcases hmember with ⟨⟨z, rfl⟩, y, hy⟩
  have hd : 2 ≤ (Nat.digits 10 (z ^ 2)).length := by
    by_contra h
    have hlen : (Nat.digits 10 (z ^ 2)).length ≤ 1 := by omega
    have hzsq_lt : z ^ 2 < 10 :=
      (Nat.digits_length_le_iff (b := 10) (k := 1) (by norm_num) (z ^ 2)).mp hlen
    have hzlt : z < 4 := by nlinarith
    have hdpos : 0 < (Nat.digits 10 (z ^ 2)).length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
    have hdigit : (Nat.digits 10 (z ^ 2)).length = 1 := by omega
    interval_cases z
    · omega
    all_goals
      norm_num [hdigit] at hy
      have hylt : y < 45 := by nlinarith
      interval_cases y <;> norm_num at hy
  have hy5sq : 5 ∣ y ^ 2 := by
    rw [Nat.dvd_iff_mod_eq_zero, hy]
    simp [Nat.add_mod, Nat.mul_mod, pow_succ]
  have hy5 : 5 ∣ y :=
    (show Nat.Prime 5 by decide).dvd_of_dvd_pow hy5sq
  obtain ⟨u, rfl⟩ := hy5
  have hpow : 10000 ∣ 10 ^ ((Nat.digits 10 (z ^ 2)).length + 2) := by
    change 10 ^ 4 ∣ 10 ^ ((Nat.digits 10 (z ^ 2)).length + 2)
    exact pow_dvd_pow 10 (by omega)
  have hyMod :
      (5 * u) ^ 2 ≡
        10 ^ ((Nat.digits 10 (z ^ 2)).length + 2) + 100 * z ^ 2 + 25
          [MOD 10000] := by
    simpa [Nat.ModEq] using congrArg (fun n : ℕ => n % 10000) hy
  have hdrop :
      10 ^ ((Nat.digits 10 (z ^ 2)).length + 2) + 100 * z ^ 2 + 25 ≡
        100 * z ^ 2 + 25 [MOD 10000] := by
    simpa [Nat.add_assoc] using
      hpow.modEq_zero_nat.add
        (Nat.ModEq.rfl : 100 * z ^ 2 + 25 ≡ 100 * z ^ 2 + 25 [MOD 10000])
  have hfactor : 25 * u ^ 2 ≡ 25 * (4 * z ^ 2 + 1) [MOD 10000] := by
    convert hyMod.trans hdrop using 1 <;> ring
  have h400 : u ^ 2 ≡ 4 * z ^ 2 + 1 [MOD 400] :=
    Nat.ModEq.mul_left_cancel' (c := 25) (m := 400) (by norm_num) hfactor
  exact square_mod_hundred_of_mod_four_hundred z u h400

#print axioms IsMember
#print axioms wu_a249621

end D5.S1.Digit.Admissibility.SquarePrependOneAppendTwentyFive
