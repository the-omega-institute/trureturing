import LeanInformationAudit.Projection.ProjectionValidation

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection.Mutations

def baseline : KernelProjectionRecord := {
  nodes := #[
    { key := "top", generators := #[], escapeCount := 2, relationCertificate := ``True.intro },
    { key := "bottom", generators := #[``True.intro], escapeCount := 0,
      relationCertificate := ``Eq.refl }]
  edges := #[{
    source := "top", target := "bottom", theoremName := ``True.intro,
    isCover := true, captureCount := 2, certificate := ``Eq.refl }]
  collapsedAdditions := #[{
    atNode := "bottom", theoremName := ``True.intro,
    equalityCertificate := ``Eq.refl }]
  leaveOneOut := #[{
    theoremName := ``True.intro, node := "top", uniqueCaptureCount := 2,
    certificate := ``Eq.refl }]
  denominator := 2 }

def check (candidate : KernelProjectionRecord) : Elab.Command.CommandElabM Unit := do
  match validateProjectionSnapshot `Root `Catalog baseline candidate with
  | .ok () => pure ()
  | .error message => throwError message

run_cmd check baseline

/-- error: IE-C039 InvalidGeneratedKernelNode root=Root catalog=Catalog node=alias reason=duplicate-extensional-node -/
#guard_msgs in
run_cmd check { baseline with nodes := baseline.nodes.push { baseline.nodes[0]! with key := "alias" } }

/-- error: IE-C039 InvalidGeneratedKernelNode root=Root catalog=Catalog node=top reason=representative-mismatch -/
#guard_msgs in
run_cmd check { baseline with nodes := baseline.nodes.modify 0 fun row =>
  { row with generators := #[``Eq.refl] } }

/-- error: IE-C040 InvalidGeneratorTransition root=Root catalog=Catalog from=top to=bottom theorem=True.intro reason=cover-classification-mismatch -/
#guard_msgs in
run_cmd check { baseline with edges := baseline.edges.modify 0 fun row => { row with isCover := false } }

/-- error: IE-C040 InvalidGeneratorTransition root=Root catalog=Catalog from=top to=bottom theorem=True.intro reason=missing-certified-transition -/
#guard_msgs in
run_cmd check { baseline with edges := #[] }

/-- error: IE-C040 InvalidGeneratorTransition root=Root catalog=Catalog from=bottom to=bottom theorem=True.intro reason=missing-collapsed-addition -/
#guard_msgs in
run_cmd check { baseline with collapsedAdditions := #[] }

/-- error: IE-C041 IncompleteKernelProjectionBoundary root=Root catalog=Catalog missing=["top"] -/
#guard_msgs in
run_cmd check { baseline with nodes := #[baseline.nodes[1]!] }

/-- error: IE-C041 IncompleteKernelProjectionBoundary root=Root catalog=Catalog missing=["bottom","top"] -/
#guard_msgs in
run_cmd check { baseline with nodes := #[], edges := #[], collapsedAdditions := #[], leaveOneOut := #[] }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=node:top:escape_count expected=2 actual=3 -/
#guard_msgs in
run_cmd check { baseline with nodes := baseline.nodes.modify 0 fun row => { row with escapeCount := 3 } }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=edge:top:bottom:True.intro:capture_count expected=2 actual=1 -/
#guard_msgs in
run_cmd check { baseline with edges := baseline.edges.modify 0 fun row => { row with captureCount := 1 } }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=verdict expected="irredundant" actual="redundant" -/
#guard_msgs in
run_cmd check { baseline with verdict := "redundant" }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=complete_lattice_materialized expected=false actual=true -/
#guard_msgs in
run_cmd check { baseline with completeLatticeMaterialized := true }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=redundant_indices expected=[] actual=["True.intro"] -/
#guard_msgs in
run_cmd check { baseline with redundantIndices := #[``True.intro] }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=denominator expected=2 actual=3 -/
#guard_msgs in
run_cmd check { baseline with denominator := 3 }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=refinement_matrix expected=[] actual=[{"coarser":"True.intro","comparison":"equal","counterexample":null,"finer":"True.intro","proof":null}] -/
#guard_msgs in
run_cmd check { baseline with refinementMatrix := #[{
  finer := ``True.intro, coarser := ``True.intro, comparison := "equal",
  proofName := none, counterexample := none }] }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=multiplicity_spectrum expected=[] actual=[{"certificate":"Eq.refl","count":2,"k":0,"rate":{"denominator":2,"numerator":2}}] -/
#guard_msgs in
run_cmd check { baseline with multiplicitySpectrum := #[{
  k := 0, count := 2, certificate := ``Eq.refl }] }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=overlap_matrix expected=[] actual=[{"certificate":"Eq.refl","count":2,"left":"True.intro","rate":{"denominator":2,"numerator":2},"right":"True.intro"}] -/
#guard_msgs in
run_cmd check { baseline with overlapMatrix := #[{
  left := ``True.intro, right := ``True.intro, count := 2, certificate := ``Eq.refl }] }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=Root catalog=Catalog component=certified_chains expected=[] actual=[{"chain_id":"a","generators":["True.intro"],"increments":[2],"nodes":["top","bottom"],"partition_certificate":"Eq.refl","step_certificates":["Eq.refl"],"step_classes":["strict"],"terminal_escape_count":0}] -/
#guard_msgs in
run_cmd check { baseline with certifiedChains := #[{
  chainId := "a", nodes := #["top", "bottom"], generators := #[``True.intro],
  stepClasses := #["strict"], increments := #[2], stepCertificates := #[``Eq.refl],
  terminalEscapeCount := 0, partitionCertificate := ``Eq.refl }] }

#print axioms baseline
#print axioms check

/-- error: IE-C043 KernelProjectionUsedForAdmission consumer=gate field=ascii root=Root catalog=Catalog -/
#guard_msgs in
run_cmd do
  match rejectProjectionAdmission `gate "ascii" `Root `Catalog with
  | .ok () => pure ()
  | .error message => throwError message

end LeanInformationAudit.Tests.Projection.Mutations
