/- SOURCE_ONLY_UNCOMPILED.
Shared arithmetic witnesses for the prime-symbol source families.
Static source preparation only; formal verification remains pending.
-/
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
namespace Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

theorem weight_two_pos : 0 < primeWeight 2 := by
  unfold primeWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

theorem indices_two : primeIndices 2 = ∅ := by decide

end Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
