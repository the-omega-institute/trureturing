/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/MainRank3530.chunk_checked
   digest: Largest indexed rank certificate assembled from exact opaque row sums. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Inputs
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainRank3530Part06

/-! Opaque checks retain the exact original indexed-rank computation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.MainRank3530

attribute [local irreducible] rankIndexUpper rankIndexRange rankIndexChunks
  checkExponentBoxTree checkExponentBoxLeaf checkDivisors checkFactors

/-- The original lower endpoint. -/
abbrev lo : Fin 7 → ℕ := MainRank3530Inputs.lo

/-- The original upper endpoint. -/
abbrev hi : Fin 7 → ℕ := MainRank3530Inputs.hi

/-- The original leaf, with its original rank parameter and full divisor count. -/
def certificate : MainTree :=
  .leaf (.rankIndexed 1 MainRank3530Inputs.count MainRank3530Inputs.readout)

private theorem upper_checked :
    rankIndexUpper mainScale 1 MainRank3530Inputs.count MainRank3530Inputs.readout =
      2993299203491 := by
  rw [rankIndexUpper_chunks mainScale 1 MainRank3530Inputs.count
    MainRank3530Inputs.readout [512, 512, 512, 512, 512, 512, 384] (by decide +kernel)]
  simp only [rankIndexChunks, Nat.reduceAdd, MainRank3530Part00.chunk_checked,
    MainRank3530Part01.chunk_checked, MainRank3530Part02.chunk_checked,
    MainRank3530Part03.chunk_checked, MainRank3530Part04.chunk_checked,
    MainRank3530Part05.chunk_checked, MainRank3530Part06.chunk_checked]

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := by
  unfold certificate
  have h := MainRank3530Inputs.chunk_checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hu : rankIndexUpper mainScale 1 MainRank3530Inputs.count
      MainRank3530Inputs.readout < mainScale * factorTau (exponentFactors boxPrimes lo) := by
    rw [upper_checked]
    decide +kernel
  exact check_rankIndexed_of_checks boxPrimes lo hi MainRank3530Inputs.readout
    h.1.1 h.1.2 h.2 hu

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.MainRank3530
