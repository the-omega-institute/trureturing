/- Prepared anonymous exact-use fragments for the local terminal-table proof.
These examples are transient source, not new canonical mathematical wrappers.
They have not been compiled. Their scalar equalities remain explicit proof
obligations; association comes only from the structural prefix/update proofs.
No actual terminal-table receipt or global root acceptance is asserted here. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TransientPrefixAssociationConsumerExamples
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Compatible)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
  (AssociatedCache step_associated triangle_valid_lower singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (step)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore
  (lhsTriangle lhsSingleton triangleBlock singletonBlock)

/-- An arbitrary future scope coordinate can be filled without a DAG split. -/
example (depth code : ℕ) (within : depth ≤ 20) (g : Fin 20)
    (future : depth ≤ g.val) (a : Fin 4) :
    AssociatedCache (step (prefixCache depth code) g a)
      (Function.update (prefixPartial depth code) g (some a)) := by
  exact step_associated _ _ (prefix_associated depth code within) g a
    (prefixPartial_future_none depth code within g future)

/-- A scalar table entry is enough once the actual triangle cache is associated. -/
example (depth code : ℕ) (within : depth ≤ 20) (k : Fin 16)
    (tableLower : ℤ)
    (readout : ((prefixCache depth code).triangle k).row.lower = tableLower)
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (prefixPartial depth code) e) :
    tableLower ≤ triangleBlock F1 k e := by
  have associated := prefix_associated depth code within
  have compatible : Compatible ((prefixPartial depth code) ∘ lhsTriangle k)
      (e ∘ lhsTriangle k) := by
    intro i a ha
    exact hp (lhsTriangle k i) a ha
  have bound := triangle_valid_lower ((prefixCache depth code).triangle k)
    ((prefixPartial depth code) ∘ lhsTriangle k) (e ∘ lhsTriangle k)
    (associated.1 k) compatible
  change ((prefixCache depth code).triangle k).row.lower ≤ triangleBlock F1 k e at bound
  rw [readout] at bound
  exact bound

/-- The same interface retains the original singleton block and its actual lower. -/
example (depth code : ℕ) (within : depth ≤ 20) (k : Fin 16)
    (tableLower : ℤ)
    (readout : ((prefixCache depth code).singleton k).row.lower = tableLower)
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (prefixPartial depth code) e) :
    tableLower ≤ singletonBlock F2 k e := by
  have associated := prefix_associated depth code within
  have compatible : Compatible ((prefixPartial depth code) ∘ lhsSingleton k)
      (e ∘ lhsSingleton k) := by
    intro i a ha
    exact hp (lhsSingleton k i) a ha
  have bound := singleton_valid_lower ((prefixCache depth code).singleton k)
    ((prefixPartial depth code) ∘ lhsSingleton k) (e ∘ lhsSingleton k)
    (associated.2 k) compatible
  change ((prefixCache depth code).singleton k).row.lower ≤ singletonBlock F2 k e at bound
  rw [readout] at bound
  exact bound

end TransientPrefixAssociationConsumerExamples
