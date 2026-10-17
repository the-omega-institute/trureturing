/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group06
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group06
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Group06.bound
   digest: Actual original factor tables are grouped and normalized by exact finite integer equalities. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor17
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor18
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor21
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Factor23
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group06
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal15475 (e 14) (e 16) (e 18)
def table (x14 x16 x18 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (388671222 + PreparedEJMCompleteMiniCut01088Tables.normal15475 x14 x16 x18)

set_option trace.profiler true in
theorem normalization : ∀ (x14 x16 x18 : Fin 4),
    table x14 x16 x18 = PreparedEJMCompleteMiniCut01088Factor17.table x14 x16 x18 + PreparedEJMCompleteMiniCut01088Factor18.table x14 x16 x18 + PreparedEJMCompleteMiniCut01088Factor21.table x14 x16 x18 + PreparedEJMCompleteMiniCut01088Factor23.table x14 x16 x18 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 16) (e 18)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Factor17.score e + PreparedEJMCompleteMiniCut01088Factor18.score e + PreparedEJMCompleteMiniCut01088Factor21.score e + PreparedEJMCompleteMiniCut01088Factor23.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have combined := add_le_add (add_le_add (add_le_add (PreparedEJMCompleteMiniCut01088Factor17.bound e hp) (PreparedEJMCompleteMiniCut01088Factor18.bound e hp)) (PreparedEJMCompleteMiniCut01088Factor21.bound e hp)) (PreparedEJMCompleteMiniCut01088Factor23.bound e hp)
  change PreparedEJMCompleteMiniCut01088Factor17.table (e 14) (e 16) (e 18) + PreparedEJMCompleteMiniCut01088Factor18.table (e 14) (e 16) (e 18) + PreparedEJMCompleteMiniCut01088Factor21.table (e 14) (e 16) (e 18) + PreparedEJMCompleteMiniCut01088Factor23.table (e 14) (e 16) (e 18) ≤ PreparedEJMCompleteMiniCut01088Factor17.score e + PreparedEJMCompleteMiniCut01088Factor18.score e + PreparedEJMCompleteMiniCut01088Factor21.score e + PreparedEJMCompleteMiniCut01088Factor23.score e at combined
  rw [← normalization (e 14) (e 16) (e 18)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group06
