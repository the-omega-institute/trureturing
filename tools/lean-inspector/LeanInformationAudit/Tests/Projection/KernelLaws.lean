import LeanInformationAudit.Projection.ProjectionKernel

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT
open LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

abbrev arena : Arena := Arena.ofFintype (Bool × Bool)

def unit (readout : Bool × Bool → Bool × Bool) : TheoremUnit arena where
  primitives := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    atom := fun _ => ⟨.cut, cutKernel readout⟩ }
  Statement := True
  proof := trivial

def aFst := unit (fun p => (p.1, false))
def bSnd := unit (fun p => (false, p.2))
def cId := unit id

abbrev catalog : Catalog arena := Catalog.ofVector ![aFst, bSnd, cId]

example : catalog.generatedKernel ({2} : Finset (Fin 3)) =
    catalog.generatedKernel {0, 1} := by decide

example : projectionCover catalog ∅ (catalog.generatedKernel {0}) := by decide
example : projectionCover catalog {0} (catalog.generatedKernel {0, 1}) := by decide
example : ¬projectionCover catalog ∅ (catalog.generatedKernel {2}) := by decide

#print axioms projection_cover_iff

end LeanInformationAudit.Tests.Projection
