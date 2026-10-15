/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Merge34
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Root
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open scoped BigOperators

private theorem component_sum (e : Event (Fin 20) (Fin 4)) :
    TransientEJMAnchor13674Merge34.score e = D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  simp only [TransientEJMAnchor13674Factor00.score, TransientEJMAnchor13674Factor01.score, TransientEJMAnchor13674Factor02.score, TransientEJMAnchor13674Factor03.score, TransientEJMAnchor13674Factor04.score, TransientEJMAnchor13674Factor05.score, TransientEJMAnchor13674Factor06.score, TransientEJMAnchor13674Factor07.score, TransientEJMAnchor13674Factor08.score, TransientEJMAnchor13674Factor09.score, TransientEJMAnchor13674Factor10.score, TransientEJMAnchor13674Factor11.score, TransientEJMAnchor13674Factor12.score, TransientEJMAnchor13674Factor13.score, TransientEJMAnchor13674Factor14.score, TransientEJMAnchor13674Factor15.score, TransientEJMAnchor13674Factor16.score, TransientEJMAnchor13674Factor17.score, TransientEJMAnchor13674Factor18.score, TransientEJMAnchor13674Factor19.score, TransientEJMAnchor13674Factor20.score, TransientEJMAnchor13674Factor21.score, TransientEJMAnchor13674Factor22.score, TransientEJMAnchor13674Factor23.score, TransientEJMAnchor13674Factor24.score, TransientEJMAnchor13674Factor25.score, TransientEJMAnchor13674Factor26.score, TransientEJMAnchor13674Factor27.score, TransientEJMAnchor13674Factor28.score, TransientEJMAnchor13674Factor29.score, TransientEJMAnchor13674Factor30.score, TransientEJMAnchor13674Factor31.score, TransientEJMAnchor13674Group00.score, TransientEJMAnchor13674Group01.score, TransientEJMAnchor13674Group02.score, TransientEJMAnchor13674Group03.score, TransientEJMAnchor13674Group04.score, TransientEJMAnchor13674Group05.score, TransientEJMAnchor13674Group06.score, TransientEJMAnchor13674Group07.score, TransientEJMAnchor13674Group08.score, TransientEJMAnchor13674Group09.score, TransientEJMAnchor13674Group10.score, TransientEJMAnchor13674Group11.score, TransientEJMAnchor13674Group12.score, TransientEJMAnchor13674Group13.score, TransientEJMAnchor13674Group14.score, TransientEJMAnchor13674Group15.score, TransientEJMAnchor13674Group16.score, TransientEJMAnchor13674Group17.score, TransientEJMAnchor13674Merge18.score, TransientEJMAnchor13674Merge19.score, TransientEJMAnchor13674Merge20.score, TransientEJMAnchor13674Merge21.score, TransientEJMAnchor13674Merge22.score, TransientEJMAnchor13674Merge23.score, TransientEJMAnchor13674Merge24.score, TransientEJMAnchor13674Merge25.score, TransientEJMAnchor13674Merge26.score, TransientEJMAnchor13674Merge27.score, TransientEJMAnchor13674Merge28.score, TransientEJMAnchor13674Merge29.score, TransientEJMAnchor13674Merge30.score, TransientEJMAnchor13674Merge31.score, TransientEJMAnchor13674Merge32.score, TransientEJMAnchor13674Merge33.score, TransientEJMAnchor13674Merge34.score,
    D5.S3.Quantum.Entanglement.EJMInflationScore.score, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  ac_rfl

set_option trace.profiler true in
private theorem final_minimum : ∀ (x13 x14 x15 x16 x17 x18 x19 : Fin 4),
    (6987435 : ℤ) ≤ TransientEJMAnchor13674Merge34.table x13 x14 x15 x16 x17 x18 x19 := by
  decide +kernel

set_option trace.profiler true in
theorem actual_prefix_score_lower_bound :
    ∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial 13 4) e →
      (6987435 : ℤ) ≤ D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  intro e hp
  rw [← component_sum e]
  exact (final_minimum (e 13) (e 14) (e 15) (e 16) (e 17) (e 18) (e 19)).trans (TransientEJMAnchor13674Merge34.bound e hp)

#print axioms actual_prefix_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Root
