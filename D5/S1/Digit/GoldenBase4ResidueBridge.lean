/- GID: D5/S1/Digit/GoldenBase4ResidueBridge
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4ResidueBridge
   mirror-E: none(waiver:base-four-residue-coordinate)
   anchors: []
   digest: The mod-5 and mod-7 residues of 4^n recover the exponent modulo six, while 4^n itself is the pure prime-2 axis point 2^(2n). -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/- This module records only the elementary arithmetic bridge used by the
   powers-only DFAO research. It does not identify the Zeckendorf word of 4^n
   with the Zeckendorf word of its prime-axis exponent 2n, and it introduces no
   Euler-product or Euler-Mascheroni premise. The analytic statement that every
   admissible leading Zeckendorf block occurs with positive frequency inside
   each fixed exponent residue class comes from Chang--Miller and is not
   postulated here. Proof scripts were logically reviewed; Lean was not run in
   this authoring session. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4ResidueBridge

/-- The two odd-prime residues that jointly encode an exponent class mod six. -/
def powerResidueCode (r : Fin 6) : ZMod 5 × ZMod 7 :=
  ((4 : ZMod 5) ^ r.val, (4 : ZMod 7) ^ r.val)

/-- The six residue pairs are pairwise distinct. -/
theorem powerResidueCode_injective : Function.Injective powerResidueCode := by
  intro a b h
  fin_cases a <;> fin_cases b <;> norm_num [powerResidueCode] at h ⊢

/-- Six exponent steps are invisible modulo five. -/
theorem four_pow_mod_five_add_six (n : Nat) :
    (4 : ZMod 5) ^ (n + 6) = (4 : ZMod 5) ^ n := by
  rw [pow_add]
  norm_num

/-- Six exponent steps are invisible modulo seven. -/
theorem four_pow_mod_seven_add_six (n : Nat) :
    (4 : ZMod 7) ^ (n + 6) = (4 : ZMod 7) ^ n := by
  rw [pow_add]
  norm_num

/-- Modulo five, a power depends only on the exponent modulo six. The period
   two is deliberately embedded in the common period six used with modulus 7. -/
theorem four_pow_mod_five_reduce_six (n : Nat) :
    (4 : ZMod 5) ^ n = (4 : ZMod 5) ^ (n % 6) := by
  have hn : n = n % 6 + 6 * (n / 6) := by
    omega
  conv_lhs => rw [hn]
  rw [pow_add, pow_mul]
  norm_num

/-- Modulo seven, a power depends only on the exponent modulo six. The genuine
   period three is deliberately embedded in the common period six. -/
theorem four_pow_mod_seven_reduce_six (n : Nat) :
    (4 : ZMod 7) ^ n = (4 : ZMod 7) ^ (n % 6) := by
  have hn : n = n % 6 + 6 * (n / 6) := by
    omega
  conv_lhs => rw [hn]
  rw [pow_add, pow_mul]
  norm_num

/-- The actual power residues are exactly the finite code of n mod six. -/
theorem power_residues_eq_code (n : Nat) :
    ((4 : ZMod 5) ^ n, (4 : ZMod 7) ^ n) =
      powerResidueCode ⟨n % 6, Nat.mod_lt _ (by omega)⟩ := by
  apply Prod.ext
  · exact four_pow_mod_five_reduce_six n
  · exact four_pow_mod_seven_reduce_six n

/-- Equality of the mod-5 and mod-7 power residues forces equality of exponent
   classes modulo six. -/
theorem mod_six_of_equal_power_residues {m n : Nat}
    (h5 : (4 : ZMod 5) ^ m = (4 : ZMod 5) ^ n)
    (h7 : (4 : ZMod 7) ^ m = (4 : ZMod 7) ^ n) :
    m % 6 = n % 6 := by
  let rm : Fin 6 := ⟨m % 6, Nat.mod_lt _ (by omega)⟩
  let rn : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by omega)⟩
  have hp : ((4 : ZMod 5) ^ m, (4 : ZMod 7) ^ m) =
      ((4 : ZMod 5) ^ n, (4 : ZMod 7) ^ n) := by
    exact Prod.ext h5 h7
  have hc : powerResidueCode rm = powerResidueCode rn := by
    rw [← power_residues_eq_code m, ← power_residues_eq_code n]
    exact hp
  have hr := congrArg Fin.val (powerResidueCode_injective hc)
  simpa [rm, rn] using hr

/-- Modulo three carries no exponent information for base-four powers. -/
theorem four_pow_mod_three (n : Nat) : (4 : ZMod 3) ^ n = 1 := by
  norm_num

/-- On the prime-factorization side, 4^n is a pure prime-2 axis point whose
   exponent is 2n. This is distinct from the Zeckendorf encoding of the integer
   4^n read by the DFAO. -/
theorem four_pow_eq_two_pow_even (n : Nat) :
    4 ^ n = 2 ^ (2 * n) := by
  calc
    4 ^ n = (2 ^ 2) ^ n := by norm_num
    _ = 2 ^ (2 * n) := by rw [← pow_mul]

#print axioms powerResidueCode_injective
#print axioms mod_six_of_equal_power_residues
#print axioms four_pow_eq_two_pow_even

end D5.S1.Digit.GoldenBase4ResidueBridge
