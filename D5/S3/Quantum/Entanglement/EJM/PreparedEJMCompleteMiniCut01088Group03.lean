/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor11
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor12
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group03
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal15474 (e 14) (e 15) (e 16) (e 17)
def table (x14 x15 x16 x17 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (175158175 + PreparedEJMCompleteMiniCut01088Tables.normal15474 x14 x15 x16 x17)

set_option trace.profiler true in
theorem normalization : ∀ (x14 x15 x16 x17 : Fin 4),
    table x14 x15 x16 x17 = PreparedEJMCompleteMiniCut01088Factor11.table x14 x15 x16 x17 + PreparedEJMCompleteMiniCut01088Factor12.table x14 x15 x16 x17 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 15) (e 16) (e 17)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Factor11.score e + PreparedEJMCompleteMiniCut01088Factor12.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have combined := add_le_add (PreparedEJMCompleteMiniCut01088Factor11.bound e hp) (PreparedEJMCompleteMiniCut01088Factor12.bound e hp)
  change PreparedEJMCompleteMiniCut01088Factor11.table (e 14) (e 15) (e 16) (e 17) + PreparedEJMCompleteMiniCut01088Factor12.table (e 14) (e 15) (e 16) (e 17) ≤ PreparedEJMCompleteMiniCut01088Factor11.score e + PreparedEJMCompleteMiniCut01088Factor12.score e at combined
  rw [← normalization (e 14) (e 15) (e 16) (e 17)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group03
