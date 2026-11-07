/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group05
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group05
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group05.bound
   digest: Actual original factor tables are grouped and normalized by exact finite integer equalities. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor25
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group05
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16190 (e 13) (e 16) (e 18)
def table (x13 x16 x18 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (206732689 + PreparedEJMCompleteMiniCut01137Tables.normal16190 x13 x16 x18)

set_option trace.profiler true in
theorem normalization : ∀ (x13 x16 x18 : Fin 4),
    table x13 x16 x18 = PreparedEJMCompleteMiniCut01137Factor25.table x13 x16 x18 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 16) (e 18)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Factor25.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have combined := PreparedEJMCompleteMiniCut01137Factor25.bound e hp
  change PreparedEJMCompleteMiniCut01137Factor25.table (e 13) (e 16) (e 18) ≤ PreparedEJMCompleteMiniCut01137Factor25.score e at combined
  rw [← normalization (e 13) (e 16) (e 18)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group05
