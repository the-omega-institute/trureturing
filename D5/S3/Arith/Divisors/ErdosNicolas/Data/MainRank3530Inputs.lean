/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530Inputs
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530Inputs.chunk_checked
   digest: Complete divisor-table and lower-corner inputs for the largest rank leaf. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts02
import D5.S3.Arith.Divisors.ErdosNicolas.BoxChecker

/-! Opaque checks retain the exact original indexed-rank computation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.MainRank3530Inputs

/-- Exact original lower corner. -/
def lo : Fin 7 → ℕ := ![9, 2, 2, 1, 1, 1, 0]

/-- Exact original upper corner. -/
def hi : Fin 7 → ℕ := ![17, 3, 3, 2, 1, 1, 0]

/-- Full divisor count of this original upper corner. -/
def count : ℕ := 3456

/-- Balanced packed readout of the full sorted divisor sequence. -/
def readout : ℕ → ℕ := RankReadouts02.rankReadout3530

theorem chunk_checked :
    (decide (0 < mainScale) && checkFactors (exponentFactors boxPrimes lo) &&
      checkDivisors (exponentValue boxPrimes hi) (exponentFactors boxPrimes hi)
        ((List.range count).map readout)) = true := by
  decide +kernel

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.MainRank3530Inputs
