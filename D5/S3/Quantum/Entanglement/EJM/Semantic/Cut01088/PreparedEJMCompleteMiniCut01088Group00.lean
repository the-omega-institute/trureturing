/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group00
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group00
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group00.bound
   digest: Actual original factor tables are grouped and normalized by exact finite integer equalities. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor28
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group00
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group00
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal1868 (e 13) (e 15) (e 16)
def table (x13 x15 x16 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (523550395 + PreparedEJMCompleteMiniCut01088Tables.normal1868 x13 x15 x16)

set_option trace.profiler true in
theorem normalization : ∀ (x13 x15 x16 : Fin 4),
    table x13 x15 x16 = PreparedEJMCompleteMiniCut01088Factor28.table x13 x15 x16 := by
  intro x13 x15 x16
  exact PreparedEJMCompleteMiniCut01137Group00.normalization x13 x15 x16

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 15) (e 16)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Factor28.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have combined := PreparedEJMCompleteMiniCut01088Factor28.bound e hp
  change PreparedEJMCompleteMiniCut01088Factor28.table (e 13) (e 15) (e 16) ≤ PreparedEJMCompleteMiniCut01088Factor28.score e at combined
  rw [← normalization (e 13) (e 15) (e 16)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group00
