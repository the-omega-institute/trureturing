import LeanInformationAudit.Projection.ProjectionCounts

open LeanInformationAudit D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

namespace LeanInformationAudit.Tests.Projection.ReflectedBridge

private abbrev arena : Arena := Arena.ofFintype Bool
private abbrev catalog : Catalog arena := Catalog.ofVector ![{
  primitives := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    atom := fun _ => ⟨.cut, cutKernel (id : Bool → Bool)⟩ }
  Statement := True
  proof := True.intro }]
private def nodes : Fin 2 → catalog.GeneratedKernel :=
  ![catalog.generatedKernel {}, catalog.generatedKernel {0}]
private def table : ReflectedRefinementTable 2 := ![![true, false], ![true, true]]

example : reflectedRefinesChecker nodes table = true := by decide
example : reflectedRefinesChecker nodes (fun _ _ => true) = false := by decide
example : reflectedRefinesChecker nodes ![![false, false], ![true, true]] = false := by decide
example : nodes 1 < nodes 0 :=
  reflectedStrict_sound nodes table (by decide) 1 0 (by decide) (by decide)

example : projectionOverlapCount catalog 0 0 = 2 := by decide
example : projectionSpectrum catalog 0 = 0 := by decide
example : projectionSpectrum catalog 1 = 2 := by decide
example : (nodes 0).edgeCaptureCount (nodes 1) = 2 := by
  rw [projectionEdgeCount_eq _ _ (le_of_lt
    (reflectedStrict_sound nodes table (by decide) 1 0 (by decide) (by decide)))]
  decide

#print axioms reflectedRefines_sound
#print axioms reflectedStrict_sound
#print axioms ProjectionReadout.kernel_eq
#print axioms projectionReadoutUnit_eq

end LeanInformationAudit.Tests.Projection.ReflectedBridge
