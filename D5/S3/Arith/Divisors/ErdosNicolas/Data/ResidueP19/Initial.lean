/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Initial
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Initial.initial_checked
   digest: Exact rounded initial vector for the nineteen residue tree. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTreeChecker

/-! The complete initial vector is checked independently of all terminal arithmetic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueP19

def initialVector (r : ℕ) : ℕ :=
  if r < 19 then
    if r < 9 then
      if r < 4 then
        if r < 2 then
          if r < 1 then 0 else 79538796038
        else
          if r < 3 then 38870256127 else 25457674971
      else
        if r < 6 then
          if r < 5 then 18904629957 else 15137900477
        else
          if r < 7 then
            12807399769
          else
            if r < 8 then 11344260670 else 10476755687
    else
      if r < 14 then
        if r < 11 then
          if r < 10 then 10071075382 else 10071075382
        else
          if r < 12 then
            10476755687
          else
            if r < 13 then 11344260670 else 12807399769
      else
        if r < 16 then
          if r < 15 then 15137900477 else 18904629957
        else
          if r < 17 then
            25457674971
          else
            if r < 18 then 38870256127 else 79538796038
  else 0

theorem initial_checked :
    checkResidueInitial 19 2 4294967296 initialVector = true := by decide +kernel

#print axioms initial_checked

end D5.S3.Arith.ErdosNicolas.Data.ResidueP19
