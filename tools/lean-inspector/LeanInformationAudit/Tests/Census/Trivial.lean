import LeanInformationAudit.Tests.SealOvercomplete
import LeanInformationAudit.Census.Query
open Lean Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.SealOvercomplete
namespace LeanInformationAudit.Tests.Census.Trivial
theorem nondegenerate : arena.toArena.Nondegenerate := by decide
def enumeration : Arena.StateEnumeration arena.toArena where
  states := [(false, false), (false, true), (true, false), (true, true)]
  nodup := by change ([(false, false), (false, true), (true, false), (true, true)] : List (Bool × Bool)).Nodup; decide
  complete := by change ([(false, false), (false, true), (true, false), (true, true)] : List (Bool × Bool)).toFinset = Finset.univ; decide
/-- info: three certified trivial members roundtrip -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let index ← CensusQuery.indexScope env.header.mainModule
  let mut entries := #[]
  for name in [``fstTheorem, ``idTheorem, ``sndTheorem] do
    let key : StatementKey := ⟨name, theoremStatementIdentity env name⟩
    let row ← CensusQuery.assess index "fixture-head" key
    unless row.className == "trivial_in_catalog" do throwError "expected trivial classification"
    let entry := ⟨key, row⟩
    unless (parseRow (dispositionRowJson entry)).toOption == some entry do
      throwError "trivial wire roundtrip"
    entries := entries.push entry
  let counts := count ⟨"fixture-head", entries⟩
  unless counts.accounted == 3 && counts.certified == 3 &&
      counts.fields.lookup "trivial_in_catalog" == some 3 do throwError "trivial accounting"
  logInfo "three certified trivial members roundtrip"
end LeanInformationAudit.Tests.Census.Trivial
