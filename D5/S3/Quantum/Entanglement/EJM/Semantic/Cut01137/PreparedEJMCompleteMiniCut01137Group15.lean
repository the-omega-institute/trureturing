/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group15
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group15
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Group15.bound
   digest: Actual original factor tables are grouped and normalized by exact finite integer equalities. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor16
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor19
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor20
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor22
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group15
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16273 (e 13) (e 15) (e 17) (e 19)
def table (x13 x15 x17 x19 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (1014620754 + PreparedEJMCompleteMiniCut01137Tables.normal16273 x13 x15 x17 x19)

set_option trace.profiler true in
theorem normalization : ∀ (x13 x15 x17 x19 : Fin 4),
    table x13 x15 x17 x19 = PreparedEJMCompleteMiniCut01137Factor16.table x13 x15 x17 x19 + PreparedEJMCompleteMiniCut01137Factor19.table x13 x15 x17 x19 + PreparedEJMCompleteMiniCut01137Factor20.table x13 x15 x17 x19 + PreparedEJMCompleteMiniCut01137Factor22.table x13 x15 x17 x19 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 15) (e 17) (e 19)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Factor16.score e + PreparedEJMCompleteMiniCut01137Factor19.score e + PreparedEJMCompleteMiniCut01137Factor20.score e + PreparedEJMCompleteMiniCut01137Factor22.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have combined := add_le_add (add_le_add (add_le_add (PreparedEJMCompleteMiniCut01137Factor16.bound e hp) (PreparedEJMCompleteMiniCut01137Factor19.bound e hp)) (PreparedEJMCompleteMiniCut01137Factor20.bound e hp)) (PreparedEJMCompleteMiniCut01137Factor22.bound e hp)
  change PreparedEJMCompleteMiniCut01137Factor16.table (e 13) (e 15) (e 17) (e 19) + PreparedEJMCompleteMiniCut01137Factor19.table (e 13) (e 15) (e 17) (e 19) + PreparedEJMCompleteMiniCut01137Factor20.table (e 13) (e 15) (e 17) (e 19) + PreparedEJMCompleteMiniCut01137Factor22.table (e 13) (e 15) (e 17) (e 19) ≤ PreparedEJMCompleteMiniCut01137Factor16.score e + PreparedEJMCompleteMiniCut01137Factor19.score e + PreparedEJMCompleteMiniCut01137Factor20.score e + PreparedEJMCompleteMiniCut01137Factor22.score e at combined
  rw [← normalization (e 13) (e 15) (e 17) (e 19)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group15
