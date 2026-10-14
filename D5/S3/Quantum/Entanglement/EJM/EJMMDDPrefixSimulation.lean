/- GID: D5/S3/Quantum/Entanglement/EJM/EJMMDDPrefixSimulation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMMDDPrefixSimulation
   mirror-E: none(waiver:actual-value-diagram-certificate)
   anchors: []
   utility: none
   digest: Exhaustive indexed prefix receipts recover the complete actual-cache simulation for the literal EJM diagrams. -/

/- WIP for the same EJM certificate. The numerical premises below range over
every prefix, but their complete concrete kernel receipts are still required.
These conditional consumers do not assert that the premises have passed. -/

import Mathlib.Algebra.BigOperators.Fin
import D5.S3.Quantum.Entanglement.EJM.EJMMDDData
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMDDPrefixSimulation
open D5.S0.Certificates.FiniteMDDCacheSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMMDDData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState

/-- Eight literal branch choices retain the actual updated triangle cache.
The remaining two coordinates and their terminal readouts are fully checked. -/
def trianglePrefixCheck (code : Fin (4 ^ 8)) : Bool :=
  let reached := followPrefix triangleNodes triangleStep 8 triangleRoot
    (initial.triangle 0) (finFunctionFinEquiv.symm code)
  checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
    3 reached.1 reached.2

/-- Seven literal branch choices retain the actual updated singleton cache. -/
def singletonPrefixCheck (code : Fin (4 ^ 7)) : Bool :=
  let reached := followPrefix singletonNodes singletonStep 7 singletonRoot
    (initial.singleton 0) (finFunctionFinEquiv.symm code)
  checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
    3 reached.1 reached.2

/-- The existing explicit radix equivalence ensures every eight-value prefix
is covered. Checking the literal diagram shape alone cannot supply this premise. -/
theorem triangle_simulation_of_prefixes
    (accepted : ∀ code, trianglePrefixCheck code = true) :
    checkSimulation triangleNodes triangleStep (fun current => current.row.lower)
      11 triangleRoot (initial.triangle 0) = true := by
  apply checked_prefixes triangleNodes triangleStep (fun current => current.row.lower)
    (0 : Fin 4) 8 2 triangleRoot (initial.triangle 0)
  intro path
  simpa only [trianglePrefixCheck, Equiv.symm_apply_apply] using
    accepted (finFunctionFinEquiv path)

theorem singleton_simulation_of_prefixes
    (accepted : ∀ code, singletonPrefixCheck code = true) :
    checkSimulation singletonNodes singletonStep (fun current => current.row.lower)
      10 singletonRoot (initial.singleton 0) = true := by
  apply checked_prefixes singletonNodes singletonStep (fun current => current.row.lower)
    (0 : Fin 4) 7 2 singletonRoot (initial.singleton 0)
  intro path
  simpa only [singletonPrefixCheck, Equiv.symm_apply_apply] using
    accepted (finFunctionFinEquiv path)

#print axioms triangle_simulation_of_prefixes
#print axioms singleton_simulation_of_prefixes

end D5.S3.Quantum.Entanglement.EJM.EJMMDDPrefixSimulation
