import LeanInformationAuditRegAnalysis.SearchReduction.CertificateSyntax
import Lean.LibrarySuggestions.MePo
import Lean.LibrarySuggestions.SineQuaNon

namespace LeanInformationAudit.SearchReduction
open Lean Meta

initialize certificateNominations : IO.Ref (Array CertificateNomination) ← IO.mkRef #[]
initialize edgeCertificateNominations : IO.Ref (Array (Name × CertificateNomination)) ← IO.mkRef #[]

/-- Canonical order is independent of producer order, repeated nominations
and producer scores. Provenance is carried separately from acceptance. -/
def nominationCertificates (pool : Array CertificateNomination) : Array ObviousCertificate :=
  ((pool.map (·.certificate)).toList.eraseDups.toArray).qsort
    (fun a b => a.render < b.render)

def canonicalCertificateBindings (bindings : Array (Name × CertificateNomination)) :
    Array (Name × String) :=
  ((bindings.map fun (owner, n) => (owner, n.certificate.render)).toList.eraseDups.toArray).qsort
    (fun a b => reprStr a < reprStr b)

/-- LLM adapters accept names and a frozen producer label only. No LLM is
invoked here and a missing nomination supplies no negative evidence. -/
def nominateNames (names : Array Name) (provenance : String) : Array CertificateNomination :=
  names.map fun name => ⟨.lookup name, provenance⟩

/-- Lean's existing premise selectors are untrusted optional producers.
The caller bounds this computation; their names still pass primary recall,
the single-candidate replayer, source isolation, kernel and axiom checks. -/
def coreCertificateNominations (target : Expr) (types : List Expr)
    (maximum : Nat := 8) : MetaM (Array CertificateNomination) := do
  let type := types.foldr (fun t body => mkForall `_premise .default t body) target
  let root ← mkFreshExprMVar type
  let mut goal := root.mvarId!
  while (← goal.withContext <| withReducible <| whnf (← goal.getType)).isForall do
    let (_, next) ← goal.intro1
    goal := next
  let mepo ← LibrarySuggestions.mepoSelector false 0.6 2.4 goal {maxSuggestions := maximum}
  let sine ← LibrarySuggestions.sineQuaNonSelector 1.5 goal {maxSuggestions := maximum}
  return nominateNames (mepo.map (·.name)) "Lean.LibrarySuggestions.MePo" ++
    nominateNames (sine.map (·.name)) "Lean.LibrarySuggestions.SineQuaNon"

end LeanInformationAudit.SearchReduction
