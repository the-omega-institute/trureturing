/- Transient benchmark of an actual leaf, excluded from delivered source.
The first bound leaf of .ejm-proof-data/rounded32/cover.bin is tag 1 at byte
offset 20. Its root-to-leaf path assigns actual nodes 0 through 19 to zero.
No artificial branch shape or claimed numerical minimum is introduced here.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

set_option maxHeartbeats 4000000 in
set_option trace.profiler true in
example : D5.S0.Certificates.FiniteSymmetryDAGReplay.check
    D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData.nodes lower
    D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry.dominates scale 1
    (0 : Fin D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData.Size)
    (fun _ => some (0 : Fin 4)) = true := by decide +kernel
