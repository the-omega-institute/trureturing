/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor02
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor06
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group12
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def normalizedAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16294 (e 15) (e 16) (e 19)
def table (x15 x16 x19 : Fin 4) : ℤ :=
  (6987435 : ℤ) * (1612129572 + PreparedEJMCompleteMiniCut01137Tables.normal16294 x15 x16 x19)

set_option trace.profiler true in
theorem normalization : ∀ (x15 x16 x19 : Fin 4),
    table x15 x16 x19 = PreparedEJMCompleteMiniCut01137Factor02.table x15 x16 x19 + PreparedEJMCompleteMiniCut01137Factor06.table x15 x16 x19 := by
  decide +kernel

def lowerAt (e : Assignment) : ℤ := table (e 15) (e 16) (e 19)
def score (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Factor02.score e + PreparedEJMCompleteMiniCut01137Factor06.score e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have combined := add_le_add (PreparedEJMCompleteMiniCut01137Factor02.bound e hp) (PreparedEJMCompleteMiniCut01137Factor06.bound e hp)
  change PreparedEJMCompleteMiniCut01137Factor02.table (e 15) (e 16) (e 19) + PreparedEJMCompleteMiniCut01137Factor06.table (e 15) (e 16) (e 19) ≤ PreparedEJMCompleteMiniCut01137Factor02.score e + PreparedEJMCompleteMiniCut01137Factor06.score e at combined
  rw [← normalization (e 15) (e 16) (e 19)] at combined
  exact combined

#print axioms normalization
#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group12
