import LeanInformationAuditRegAnalysis.AuricFib.Census

open LeanInformationAudit.AuricFib
open D5.S3.ConceptDynamics.InformationEscape

/-- Actual empty/singleton finite arenas do not manufacture a zero-denominator rate. -/
def main : IO UInt32 := do
  for n in [0, 1, 2, 5] do
    let arena := Arena.ofFintype (Fin n)
    let actual := pairRate (some arena.card) 0
    if n < 2 then
      unless actual.isNone do throw <| IO.userError "[FAIL] DegeneratePairRate"
    else
      unless actual == some (LeanInformationAudit.exactRateJson 0 (n * (n-1))) do
        throw <| IO.userError "[FAIL] OrderedPairDenominator"
  unless (pairRate none 0).isNone do throw <| IO.userError "[FAIL] UnboundedPairRate"
  IO.println "[PASS] DegenerateAndUnboundedPairRate"
  return 0
