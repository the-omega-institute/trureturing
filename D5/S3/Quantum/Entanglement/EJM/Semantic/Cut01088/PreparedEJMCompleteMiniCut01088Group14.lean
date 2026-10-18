/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group14
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group14
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group14.bound
   digest: Actual original factor tables are grouped and normalized by exact finite integer equalities. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor26
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group14
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal1878 (e 14) (e 17) (e 19)
def table (x14 x17 x19 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (435715267 + PreparedEJMCompleteMiniCut01088Tables.normal1878 x14 x17 x19)

set_option trace.profiler true in
theorem normalization : ∀ (x14 x17 x19 : Fin 4),
    table x14 x17 x19 = PreparedEJMCompleteMiniCut01088Factor26.table x14 x17 x19 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 17) (e 19)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Factor26.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have combined := PreparedEJMCompleteMiniCut01088Factor26.bound e hp
  change PreparedEJMCompleteMiniCut01088Factor26.table (e 14) (e 17) (e 19) ≤ PreparedEJMCompleteMiniCut01088Factor26.score e at combined
  rw [← normalization (e 14) (e 17) (e 19)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group14
