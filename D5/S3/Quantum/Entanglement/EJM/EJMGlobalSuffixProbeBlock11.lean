/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock11
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock11
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock11
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache451 : Cache :=
  step cache450 ⟨17, by decide⟩ 0
private def partial451 : Partial (Fin 20) (Fin 4) :=
  Function.update partial450 ⟨17, by decide⟩ (some 0)

private def cache452 : Cache :=
  step cache450 ⟨17, by decide⟩ 1
private def partial452 : Partial (Fin 20) (Fin 4) :=
  Function.update partial450 ⟨17, by decide⟩ (some 1)

private def cache453 : Cache :=
  step cache452 ⟨18, by decide⟩ 0
private def partial453 : Partial (Fin 20) (Fin 4) :=
  Function.update partial452 ⟨18, by decide⟩ (some 0)

private def cache454 : Cache :=
  step cache452 ⟨18, by decide⟩ 1
private def partial454 : Partial (Fin 20) (Fin 4) :=
  Function.update partial452 ⟨18, by decide⟩ (some 1)

private def cache455 : Cache :=
  step cache452 ⟨18, by decide⟩ 2
private def partial455 : Partial (Fin 20) (Fin 4) :=
  Function.update partial452 ⟨18, by decide⟩ (some 2)

private def cache456 : Cache :=
  step cache455 ⟨19, by decide⟩ 0
private def partial456 : Partial (Fin 20) (Fin 4) :=
  Function.update partial455 ⟨19, by decide⟩ (some 0)

private def cache457 : Cache :=
  step cache455 ⟨19, by decide⟩ 1
private def partial457 : Partial (Fin 20) (Fin 4) :=
  Function.update partial455 ⟨19, by decide⟩ (some 1)

private def cache458 : Cache :=
  step cache455 ⟨19, by decide⟩ 2
private def partial458 : Partial (Fin 20) (Fin 4) :=
  Function.update partial455 ⟨19, by decide⟩ (some 2)

private def cache459 : Cache :=
  step cache455 ⟨19, by decide⟩ 3
private def partial459 : Partial (Fin 20) (Fin 4) :=
  Function.update partial455 ⟨19, by decide⟩ (some 3)

private def cache460 : Cache :=
  step cache452 ⟨18, by decide⟩ 3
private def partial460 : Partial (Fin 20) (Fin 4) :=
  Function.update partial452 ⟨18, by decide⟩ (some 3)

private def cache461 : Cache :=
  step cache460 ⟨19, by decide⟩ 0
private def partial461 : Partial (Fin 20) (Fin 4) :=
  Function.update partial460 ⟨19, by decide⟩ (some 0)

private def cache462 : Cache :=
  step cache460 ⟨19, by decide⟩ 1
private def partial462 : Partial (Fin 20) (Fin 4) :=
  Function.update partial460 ⟨19, by decide⟩ (some 1)

private def cache463 : Cache :=
  step cache460 ⟨19, by decide⟩ 2
private def partial463 : Partial (Fin 20) (Fin 4) :=
  Function.update partial460 ⟨19, by decide⟩ (some 2)

private def cache464 : Cache :=
  step cache460 ⟨19, by decide⟩ 3
private def partial464 : Partial (Fin 20) (Fin 4) :=
  Function.update partial460 ⟨19, by decide⟩ (some 3)

private def cache465 : Cache :=
  step cache450 ⟨17, by decide⟩ 2
private def partial465 : Partial (Fin 20) (Fin 4) :=
  Function.update partial450 ⟨17, by decide⟩ (some 2)

private def cache466 : Cache :=
  step cache465 ⟨18, by decide⟩ 0
private def partial466 : Partial (Fin 20) (Fin 4) :=
  Function.update partial465 ⟨18, by decide⟩ (some 0)

private def cache467 : Cache :=
  step cache465 ⟨18, by decide⟩ 1
private def partial467 : Partial (Fin 20) (Fin 4) :=
  Function.update partial465 ⟨18, by decide⟩ (some 1)

private def cache468 : Cache :=
  step cache465 ⟨18, by decide⟩ 2
private def partial468 : Partial (Fin 20) (Fin 4) :=
  Function.update partial465 ⟨18, by decide⟩ (some 2)

private def cache469 : Cache :=
  step cache465 ⟨18, by decide⟩ 3
private def partial469 : Partial (Fin 20) (Fin 4) :=
  Function.update partial465 ⟨18, by decide⟩ (some 3)

private def cache470 : Cache :=
  step cache450 ⟨17, by decide⟩ 3
private def partial470 : Partial (Fin 20) (Fin 4) :=
  Function.update partial450 ⟨17, by decide⟩ (some 3)

private def cache471 : Cache :=
  step cache470 ⟨18, by decide⟩ 0
private def partial471 : Partial (Fin 20) (Fin 4) :=
  Function.update partial470 ⟨18, by decide⟩ (some 0)

private def cache472 : Cache :=
  step cache471 ⟨19, by decide⟩ 0
private def partial472 : Partial (Fin 20) (Fin 4) :=
  Function.update partial471 ⟨19, by decide⟩ (some 0)

private def cache473 : Cache :=
  step cache471 ⟨19, by decide⟩ 1
private def partial473 : Partial (Fin 20) (Fin 4) :=
  Function.update partial471 ⟨19, by decide⟩ (some 1)

private def cache474 : Cache :=
  step cache471 ⟨19, by decide⟩ 2
private def partial474 : Partial (Fin 20) (Fin 4) :=
  Function.update partial471 ⟨19, by decide⟩ (some 2)

private def cache475 : Cache :=
  step cache471 ⟨19, by decide⟩ 3
private def partial475 : Partial (Fin 20) (Fin 4) :=
  Function.update partial471 ⟨19, by decide⟩ (some 3)

private def cache476 : Cache :=
  step cache470 ⟨18, by decide⟩ 1
private def partial476 : Partial (Fin 20) (Fin 4) :=
  Function.update partial470 ⟨18, by decide⟩ (some 1)

private def cache477 : Cache :=
  step cache476 ⟨19, by decide⟩ 0
private def partial477 : Partial (Fin 20) (Fin 4) :=
  Function.update partial476 ⟨19, by decide⟩ (some 0)

private def cache478 : Cache :=
  step cache476 ⟨19, by decide⟩ 1
private def partial478 : Partial (Fin 20) (Fin 4) :=
  Function.update partial476 ⟨19, by decide⟩ (some 1)

private def cache479 : Cache :=
  step cache476 ⟨19, by decide⟩ 2
private def partial479 : Partial (Fin 20) (Fin 4) :=
  Function.update partial476 ⟨19, by decide⟩ (some 2)

private def cache480 : Cache :=
  step cache476 ⟨19, by decide⟩ 3
private def partial480 : Partial (Fin 20) (Fin 4) :=
  Function.update partial476 ⟨19, by decide⟩ (some 3)

private def cache481 : Cache :=
  step cache470 ⟨18, by decide⟩ 2
private def partial481 : Partial (Fin 20) (Fin 4) :=
  Function.update partial470 ⟨18, by decide⟩ (some 2)

private def cache482 : Cache :=
  step cache481 ⟨19, by decide⟩ 0
private def partial482 : Partial (Fin 20) (Fin 4) :=
  Function.update partial481 ⟨19, by decide⟩ (some 0)

private def cache483 : Cache :=
  step cache481 ⟨19, by decide⟩ 1
private def partial483 : Partial (Fin 20) (Fin 4) :=
  Function.update partial481 ⟨19, by decide⟩ (some 1)

private def cache484 : Cache :=
  step cache481 ⟨19, by decide⟩ 2
private def partial484 : Partial (Fin 20) (Fin 4) :=
  Function.update partial481 ⟨19, by decide⟩ (some 2)

private def cache485 : Cache :=
  step cache481 ⟨19, by decide⟩ 3
private def partial485 : Partial (Fin 20) (Fin 4) :=
  Function.update partial481 ⟨19, by decide⟩ (some 3)

private def cache486 : Cache :=
  step cache470 ⟨18, by decide⟩ 3
private def partial486 : Partial (Fin 20) (Fin 4) :=
  Function.update partial470 ⟨18, by decide⟩ (some 3)

private def cache488 : Cache :=
  step cache487 ⟨17, by decide⟩ 0
private def partial488 : Partial (Fin 20) (Fin 4) :=
  Function.update partial487 ⟨17, by decide⟩ (some 0)

private def cache489 : Cache :=
  step cache487 ⟨17, by decide⟩ 1
private def partial489 : Partial (Fin 20) (Fin 4) :=
  Function.update partial487 ⟨17, by decide⟩ (some 1)

private def cache490 : Cache :=
  step cache489 ⟨18, by decide⟩ 0
private def partial490 : Partial (Fin 20) (Fin 4) :=
  Function.update partial489 ⟨18, by decide⟩ (some 0)

private def cache491 : Cache :=
  step cache489 ⟨18, by decide⟩ 1
private def partial491 : Partial (Fin 20) (Fin 4) :=
  Function.update partial489 ⟨18, by decide⟩ (some 1)

private def cache492 : Cache :=
  step cache491 ⟨19, by decide⟩ 0
private def partial492 : Partial (Fin 20) (Fin 4) :=
  Function.update partial491 ⟨19, by decide⟩ (some 0)

private def cache493 : Cache :=
  step cache491 ⟨19, by decide⟩ 1
private def partial493 : Partial (Fin 20) (Fin 4) :=
  Function.update partial491 ⟨19, by decide⟩ (some 1)

private def cache494 : Cache :=
  step cache491 ⟨19, by decide⟩ 2
private def partial494 : Partial (Fin 20) (Fin 4) :=
  Function.update partial491 ⟨19, by decide⟩ (some 2)

private def cache495 : Cache :=
  step cache491 ⟨19, by decide⟩ 3
private def partial495 : Partial (Fin 20) (Fin 4) :=
  Function.update partial491 ⟨19, by decide⟩ (some 3)

private def cache496 : Cache :=
  step cache489 ⟨18, by decide⟩ 2
private def partial496 : Partial (Fin 20) (Fin 4) :=
  Function.update partial489 ⟨18, by decide⟩ (some 2)

private def cache497 : Cache :=
  step cache496 ⟨19, by decide⟩ 0
private def partial497 : Partial (Fin 20) (Fin 4) :=
  Function.update partial496 ⟨19, by decide⟩ (some 0)

private def cache498 : Cache :=
  step cache496 ⟨19, by decide⟩ 1
private def partial498 : Partial (Fin 20) (Fin 4) :=
  Function.update partial496 ⟨19, by decide⟩ (some 1)

private def cache499 : Cache :=
  step cache496 ⟨19, by decide⟩ 2
private def partial499 : Partial (Fin 20) (Fin 4) :=
  Function.update partial496 ⟨19, by decide⟩ (some 2)

private def cache500 : Cache :=
  step cache496 ⟨19, by decide⟩ 3
private def partial500 : Partial (Fin 20) (Fin 4) :=
  Function.update partial496 ⟨19, by decide⟩ (some 3)

private def cache501 : Cache :=
  step cache489 ⟨18, by decide⟩ 3
private def partial501 : Partial (Fin 20) (Fin 4) :=
  Function.update partial489 ⟨18, by decide⟩ (some 3)

private def cache502 : Cache :=
  step cache501 ⟨19, by decide⟩ 0
private def partial502 : Partial (Fin 20) (Fin 4) :=
  Function.update partial501 ⟨19, by decide⟩ (some 0)

private def cache503 : Cache :=
  step cache501 ⟨19, by decide⟩ 1
private def partial503 : Partial (Fin 20) (Fin 4) :=
  Function.update partial501 ⟨19, by decide⟩ (some 1)

private def cache504 : Cache :=
  step cache501 ⟨19, by decide⟩ 2
private def partial504 : Partial (Fin 20) (Fin 4) :=
  Function.update partial501 ⟨19, by decide⟩ (some 2)

private def cache505 : Cache :=
  step cache501 ⟨19, by decide⟩ 3
private def partial505 : Partial (Fin 20) (Fin 4) :=
  Function.update partial501 ⟨19, by decide⟩ (some 3)

private def cache506 : Cache :=
  step cache487 ⟨17, by decide⟩ 2
private def partial506 : Partial (Fin 20) (Fin 4) :=
  Function.update partial487 ⟨17, by decide⟩ (some 2)

private def cache507 : Cache :=
  step cache506 ⟨18, by decide⟩ 0
private def partial507 : Partial (Fin 20) (Fin 4) :=
  Function.update partial506 ⟨18, by decide⟩ (some 0)

private def cache508 : Cache :=
  step cache506 ⟨18, by decide⟩ 1
private def partial508 : Partial (Fin 20) (Fin 4) :=
  Function.update partial506 ⟨18, by decide⟩ (some 1)

private def cache509 : Cache :=
  step cache506 ⟨18, by decide⟩ 2
private def partial509 : Partial (Fin 20) (Fin 4) :=
  Function.update partial506 ⟨18, by decide⟩ (some 2)

private def cache510 : Cache :=
  step cache506 ⟨18, by decide⟩ 3
private def partial510 : Partial (Fin 20) (Fin 4) :=
  Function.update partial506 ⟨18, by decide⟩ (some 3)

private def cache511 : Cache :=
  step cache487 ⟨17, by decide⟩ 3
private def partial511 : Partial (Fin 20) (Fin 4) :=
  Function.update partial487 ⟨17, by decide⟩ (some 3)

private def cache512 : Cache :=
  step cache511 ⟨18, by decide⟩ 0
private def partial512 : Partial (Fin 20) (Fin 4) :=
  Function.update partial511 ⟨18, by decide⟩ (some 0)

private def cache513 : Cache :=
  step cache512 ⟨19, by decide⟩ 0
private def partial513 : Partial (Fin 20) (Fin 4) :=
  Function.update partial512 ⟨19, by decide⟩ (some 0)

private def cache514 : Cache :=
  step cache512 ⟨19, by decide⟩ 1
private def partial514 : Partial (Fin 20) (Fin 4) :=
  Function.update partial512 ⟨19, by decide⟩ (some 1)

private def cache515 : Cache :=
  step cache512 ⟨19, by decide⟩ 2
private def partial515 : Partial (Fin 20) (Fin 4) :=
  Function.update partial512 ⟨19, by decide⟩ (some 2)

private def cache516 : Cache :=
  step cache512 ⟨19, by decide⟩ 3
private def partial516 : Partial (Fin 20) (Fin 4) :=
  Function.update partial512 ⟨19, by decide⟩ (some 3)

private def cache517 : Cache :=
  step cache511 ⟨18, by decide⟩ 1
private def partial517 : Partial (Fin 20) (Fin 4) :=
  Function.update partial511 ⟨18, by decide⟩ (some 1)

private def cache518 : Cache :=
  step cache517 ⟨19, by decide⟩ 0
private def partial518 : Partial (Fin 20) (Fin 4) :=
  Function.update partial517 ⟨19, by decide⟩ (some 0)

private def cache519 : Cache :=
  step cache517 ⟨19, by decide⟩ 1
private def partial519 : Partial (Fin 20) (Fin 4) :=
  Function.update partial517 ⟨19, by decide⟩ (some 1)

private def cache520 : Cache :=
  step cache517 ⟨19, by decide⟩ 2
private def partial520 : Partial (Fin 20) (Fin 4) :=
  Function.update partial517 ⟨19, by decide⟩ (some 2)

private def cache521 : Cache :=
  step cache517 ⟨19, by decide⟩ 3
private def partial521 : Partial (Fin 20) (Fin 4) :=
  Function.update partial517 ⟨19, by decide⟩ (some 3)

private def cache522 : Cache :=
  step cache511 ⟨18, by decide⟩ 2
private def partial522 : Partial (Fin 20) (Fin 4) :=
  Function.update partial511 ⟨18, by decide⟩ (some 2)

private def cache523 : Cache :=
  step cache522 ⟨19, by decide⟩ 0
private def partial523 : Partial (Fin 20) (Fin 4) :=
  Function.update partial522 ⟨19, by decide⟩ (some 0)

private def cache524 : Cache :=
  step cache522 ⟨19, by decide⟩ 1
private def partial524 : Partial (Fin 20) (Fin 4) :=
  Function.update partial522 ⟨19, by decide⟩ (some 1)

private def cache525 : Cache :=
  step cache522 ⟨19, by decide⟩ 2
private def partial525 : Partial (Fin 20) (Fin 4) :=
  Function.update partial522 ⟨19, by decide⟩ (some 2)

private def cache526 : Cache :=
  step cache522 ⟨19, by decide⟩ 3
private def partial526 : Partial (Fin 20) (Fin 4) :=
  Function.update partial522 ⟨19, by decide⟩ (some 3)

private def cache527 : Cache :=
  step cache511 ⟨18, by decide⟩ 3
private def partial527 : Partial (Fin 20) (Fin 4) :=
  Function.update partial511 ⟨18, by decide⟩ (some 3)

private def cache532 : Cache :=
  step cache531 ⟨17, by decide⟩ 0
private def partial532 : Partial (Fin 20) (Fin 4) :=
  Function.update partial531 ⟨17, by decide⟩ (some 0)

private def cache533 : Cache :=
  step cache531 ⟨17, by decide⟩ 1
private def partial533 : Partial (Fin 20) (Fin 4) :=
  Function.update partial531 ⟨17, by decide⟩ (some 1)

private def cache534 : Cache :=
  step cache533 ⟨18, by decide⟩ 0
private def partial534 : Partial (Fin 20) (Fin 4) :=
  Function.update partial533 ⟨18, by decide⟩ (some 0)

private def cache535 : Cache :=
  step cache533 ⟨18, by decide⟩ 1
private def partial535 : Partial (Fin 20) (Fin 4) :=
  Function.update partial533 ⟨18, by decide⟩ (some 1)

private def cache536 : Cache :=
  step cache533 ⟨18, by decide⟩ 2
private def partial536 : Partial (Fin 20) (Fin 4) :=
  Function.update partial533 ⟨18, by decide⟩ (some 2)

private def cache537 : Cache :=
  step cache536 ⟨19, by decide⟩ 0
private def partial537 : Partial (Fin 20) (Fin 4) :=
  Function.update partial536 ⟨19, by decide⟩ (some 0)

private def cache538 : Cache :=
  step cache536 ⟨19, by decide⟩ 1
private def partial538 : Partial (Fin 20) (Fin 4) :=
  Function.update partial536 ⟨19, by decide⟩ (some 1)

private def cache539 : Cache :=
  step cache536 ⟨19, by decide⟩ 2
private def partial539 : Partial (Fin 20) (Fin 4) :=
  Function.update partial536 ⟨19, by decide⟩ (some 2)

private def cache540 : Cache :=
  step cache536 ⟨19, by decide⟩ 3
private def partial540 : Partial (Fin 20) (Fin 4) :=
  Function.update partial536 ⟨19, by decide⟩ (some 3)

private def cache541 : Cache :=
  step cache533 ⟨18, by decide⟩ 3
private def partial541 : Partial (Fin 20) (Fin 4) :=
  Function.update partial533 ⟨18, by decide⟩ (some 3)

private def cache542 : Cache :=
  step cache541 ⟨19, by decide⟩ 0
private def partial542 : Partial (Fin 20) (Fin 4) :=
  Function.update partial541 ⟨19, by decide⟩ (some 0)

private def cache543 : Cache :=
  step cache541 ⟨19, by decide⟩ 1
private def partial543 : Partial (Fin 20) (Fin 4) :=
  Function.update partial541 ⟨19, by decide⟩ (some 1)

private def cache544 : Cache :=
  step cache541 ⟨19, by decide⟩ 2
private def partial544 : Partial (Fin 20) (Fin 4) :=
  Function.update partial541 ⟨19, by decide⟩ (some 2)

private def cache545 : Cache :=
  step cache541 ⟨19, by decide⟩ 3
private def partial545 : Partial (Fin 20) (Fin 4) :=
  Function.update partial541 ⟨19, by decide⟩ (some 3)

private def cache546 : Cache :=
  step cache531 ⟨17, by decide⟩ 2
private def partial546 : Partial (Fin 20) (Fin 4) :=
  Function.update partial531 ⟨17, by decide⟩ (some 2)

private def cache547 : Cache :=
  step cache546 ⟨18, by decide⟩ 0
private def partial547 : Partial (Fin 20) (Fin 4) :=
  Function.update partial546 ⟨18, by decide⟩ (some 0)

private def cache548 : Cache :=
  step cache546 ⟨18, by decide⟩ 1
private def partial548 : Partial (Fin 20) (Fin 4) :=
  Function.update partial546 ⟨18, by decide⟩ (some 1)

private def cache549 : Cache :=
  step cache546 ⟨18, by decide⟩ 2
private def partial549 : Partial (Fin 20) (Fin 4) :=
  Function.update partial546 ⟨18, by decide⟩ (some 2)

private def cache550 : Cache :=
  step cache546 ⟨18, by decide⟩ 3
private def partial550 : Partial (Fin 20) (Fin 4) :=
  Function.update partial546 ⟨18, by decide⟩ (some 3)

private def cache551 : Cache :=
  step cache531 ⟨17, by decide⟩ 3
private def partial551 : Partial (Fin 20) (Fin 4) :=
  Function.update partial531 ⟨17, by decide⟩ (some 3)

private def cache552 : Cache :=
  step cache551 ⟨18, by decide⟩ 0
private def partial552 : Partial (Fin 20) (Fin 4) :=
  Function.update partial551 ⟨18, by decide⟩ (some 0)

private def cache553 : Cache :=
  step cache552 ⟨19, by decide⟩ 0
private def partial553 : Partial (Fin 20) (Fin 4) :=
  Function.update partial552 ⟨19, by decide⟩ (some 0)

private def cache554 : Cache :=
  step cache552 ⟨19, by decide⟩ 1
private def partial554 : Partial (Fin 20) (Fin 4) :=
  Function.update partial552 ⟨19, by decide⟩ (some 1)

private def cache555 : Cache :=
  step cache552 ⟨19, by decide⟩ 2
private def partial555 : Partial (Fin 20) (Fin 4) :=
  Function.update partial552 ⟨19, by decide⟩ (some 2)

private def cache556 : Cache :=
  step cache552 ⟨19, by decide⟩ 3
private def partial556 : Partial (Fin 20) (Fin 4) :=
  Function.update partial552 ⟨19, by decide⟩ (some 3)

private def cache557 : Cache :=
  step cache551 ⟨18, by decide⟩ 1
private def partial557 : Partial (Fin 20) (Fin 4) :=
  Function.update partial551 ⟨18, by decide⟩ (some 1)

private def cache558 : Cache :=
  step cache557 ⟨19, by decide⟩ 0
private def partial558 : Partial (Fin 20) (Fin 4) :=
  Function.update partial557 ⟨19, by decide⟩ (some 0)

private def cache559 : Cache :=
  step cache557 ⟨19, by decide⟩ 1
private def partial559 : Partial (Fin 20) (Fin 4) :=
  Function.update partial557 ⟨19, by decide⟩ (some 1)

private def cache560 : Cache :=
  step cache557 ⟨19, by decide⟩ 2
private def partial560 : Partial (Fin 20) (Fin 4) :=
  Function.update partial557 ⟨19, by decide⟩ (some 2)

private def cache561 : Cache :=
  step cache557 ⟨19, by decide⟩ 3
private def partial561 : Partial (Fin 20) (Fin 4) :=
  Function.update partial557 ⟨19, by decide⟩ (some 3)

private def cache562 : Cache :=
  step cache551 ⟨18, by decide⟩ 2
private def partial562 : Partial (Fin 20) (Fin 4) :=
  Function.update partial551 ⟨18, by decide⟩ (some 2)

private def cache563 : Cache :=
  step cache562 ⟨19, by decide⟩ 0
private def partial563 : Partial (Fin 20) (Fin 4) :=
  Function.update partial562 ⟨19, by decide⟩ (some 0)

private def cache564 : Cache :=
  step cache562 ⟨19, by decide⟩ 1
private def partial564 : Partial (Fin 20) (Fin 4) :=
  Function.update partial562 ⟨19, by decide⟩ (some 1)

private def cache565 : Cache :=
  step cache562 ⟨19, by decide⟩ 2
private def partial565 : Partial (Fin 20) (Fin 4) :=
  Function.update partial562 ⟨19, by decide⟩ (some 2)

private def cache566 : Cache :=
  step cache562 ⟨19, by decide⟩ 3
private def partial566 : Partial (Fin 20) (Fin 4) :=
  Function.update partial562 ⟨19, by decide⟩ (some 3)

private def cache567 : Cache :=
  step cache551 ⟨18, by decide⟩ 3
private def partial567 : Partial (Fin 20) (Fin 4) :=
  Function.update partial551 ⟨18, by decide⟩ (some 3)

private def cache568 : Cache :=
  step cache567 ⟨19, by decide⟩ 0
private def partial568 : Partial (Fin 20) (Fin 4) :=
  Function.update partial567 ⟨19, by decide⟩ (some 0)

private def cache569 : Cache :=
  step cache567 ⟨19, by decide⟩ 1
private def partial569 : Partial (Fin 20) (Fin 4) :=
  Function.update partial567 ⟨19, by decide⟩ (some 1)

private def cache570 : Cache :=
  step cache567 ⟨19, by decide⟩ 2
private def partial570 : Partial (Fin 20) (Fin 4) :=
  Function.update partial567 ⟨19, by decide⟩ (some 2)

private def cache571 : Cache :=
  step cache567 ⟨19, by decide⟩ 3
private def partial571 : Partial (Fin 20) (Fin 4) :=
  Function.update partial567 ⟨19, by decide⟩ (some 3)

private def cache573 : Cache :=
  step cache572 ⟨17, by decide⟩ 0
private def partial573 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 0)

private def cache574 : Cache :=
  step cache572 ⟨17, by decide⟩ 1
private def partial574 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 1)

private def cache575 : Cache :=
  step cache574 ⟨18, by decide⟩ 0
private def partial575 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 0)

private def cache576 : Cache :=
  step cache574 ⟨18, by decide⟩ 1
private def partial576 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 1)

private def cache577 : Cache :=
  step cache576 ⟨19, by decide⟩ 0
private def partial577 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 0)

private def cache578 : Cache :=
  step cache576 ⟨19, by decide⟩ 1
private def partial578 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 1)

private def cache579 : Cache :=
  step cache576 ⟨19, by decide⟩ 2
private def partial579 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 2)

private def cache580 : Cache :=
  step cache576 ⟨19, by decide⟩ 3
private def partial580 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 3)

private def cache581 : Cache :=
  step cache574 ⟨18, by decide⟩ 2
private def partial581 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 2)

private def cache582 : Cache :=
  step cache581 ⟨19, by decide⟩ 0
private def partial582 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 0)

private def cache583 : Cache :=
  step cache581 ⟨19, by decide⟩ 1
private def partial583 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 1)

private def cache584 : Cache :=
  step cache581 ⟨19, by decide⟩ 2
private def partial584 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 2)

private def cache585 : Cache :=
  step cache581 ⟨19, by decide⟩ 3
private def partial585 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 3)

private def cache586 : Cache :=
  step cache574 ⟨18, by decide⟩ 3
private def partial586 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 3)

private def cache587 : Cache :=
  step cache586 ⟨19, by decide⟩ 0
private def partial587 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 0)

private def cache588 : Cache :=
  step cache586 ⟨19, by decide⟩ 1
private def partial588 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 1)

private def cache589 : Cache :=
  step cache586 ⟨19, by decide⟩ 2
private def partial589 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 2)

private def cache590 : Cache :=
  step cache586 ⟨19, by decide⟩ 3
private def partial590 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 3)

private def cache591 : Cache :=
  step cache572 ⟨17, by decide⟩ 2
private def partial591 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 2)

private def cache592 : Cache :=
  step cache591 ⟨18, by decide⟩ 0
private def partial592 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 0)

private def cache593 : Cache :=
  step cache591 ⟨18, by decide⟩ 1
private def partial593 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 1)

private def cache594 : Cache :=
  step cache593 ⟨19, by decide⟩ 0
private def partial594 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 0)

private def cache595 : Cache :=
  step cache593 ⟨19, by decide⟩ 1
private def partial595 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 1)

private def cache596 : Cache :=
  step cache593 ⟨19, by decide⟩ 2
private def partial596 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 2)

private def cache597 : Cache :=
  step cache593 ⟨19, by decide⟩ 3
private def partial597 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 3)

private def cache598 : Cache :=
  step cache591 ⟨18, by decide⟩ 2
private def partial598 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 2)

private def cache599 : Cache :=
  step cache591 ⟨18, by decide⟩ 3
private def partial599 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 3)

private def cache600 : Cache :=
  step cache599 ⟨19, by decide⟩ 0
private def partial600 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 0)

private def cache601 : Cache :=
  step cache599 ⟨19, by decide⟩ 1
private def partial601 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 1)

private def cache602 : Cache :=
  step cache599 ⟨19, by decide⟩ 2
private def partial602 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 2)

private def cache603 : Cache :=
  step cache599 ⟨19, by decide⟩ 3
private def partial603 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 3)

private def cache604 : Cache :=
  step cache572 ⟨17, by decide⟩ 3
private def partial604 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 3)

private def cache605 : Cache :=
  step cache604 ⟨18, by decide⟩ 0
private def partial605 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 0)

private def cache606 : Cache :=
  step cache605 ⟨19, by decide⟩ 0
private def partial606 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 0)

private def cache607 : Cache :=
  step cache605 ⟨19, by decide⟩ 1
private def partial607 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 1)

private def cache608 : Cache :=
  step cache605 ⟨19, by decide⟩ 2
private def partial608 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 2)

private def cache609 : Cache :=
  step cache605 ⟨19, by decide⟩ 3
private def partial609 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 3)

private def cache610 : Cache :=
  step cache604 ⟨18, by decide⟩ 1
private def partial610 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 1)

private def cache611 : Cache :=
  step cache610 ⟨19, by decide⟩ 0
private def partial611 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 0)

private def cache612 : Cache :=
  step cache610 ⟨19, by decide⟩ 1
private def partial612 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 1)

private def cache613 : Cache :=
  step cache610 ⟨19, by decide⟩ 2
private def partial613 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 2)

private def cache614 : Cache :=
  step cache610 ⟨19, by decide⟩ 3
private def partial614 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 3)

private def cache615 : Cache :=
  step cache604 ⟨18, by decide⟩ 2
private def partial615 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 2)

private def cache616 : Cache :=
  step cache615 ⟨19, by decide⟩ 0
private def partial616 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 0)

private def cache617 : Cache :=
  step cache615 ⟨19, by decide⟩ 1
private def partial617 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 1)

private def cache618 : Cache :=
  step cache615 ⟨19, by decide⟩ 2
private def partial618 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 2)

private def cache619 : Cache :=
  step cache615 ⟨19, by decide⟩ 3
private def partial619 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 3)

private def cache620 : Cache :=
  step cache604 ⟨18, by decide⟩ 3
private def partial620 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 3)

private def cache621 : Cache :=
  step cache620 ⟨19, by decide⟩ 0
private def partial621 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 0)

private def cache622 : Cache :=
  step cache620 ⟨19, by decide⟩ 1
private def partial622 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 1)

private def cache623 : Cache :=
  step cache620 ⟨19, by decide⟩ 2
private def partial623 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 2)

private def cache624 : Cache :=
  step cache620 ⟨19, by decide⟩ 3
private def partial624 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 3)

private theorem receipt624 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨624, by decide⟩ cache624 partial624 = true := by
  decide +kernel

private theorem receipt623 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨623, by decide⟩ cache623 partial623 = true := by
  decide +kernel

private theorem receipt622 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨622, by decide⟩ cache622 partial622 = true := by
  decide +kernel

private theorem receipt621 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨621, by decide⟩ cache621 partial621 = true := by
  decide +kernel

private theorem receipt620 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨620, by decide⟩ cache620 partial620 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![621,622,623,624])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1372525063589299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt621
  · exact receipt622
  · exact receipt623
  · exact receipt624

private theorem receipt619 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨619, by decide⟩ cache619 partial619 = true := by
  decide +kernel

private theorem receipt618 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨618, by decide⟩ cache618 partial618 = true := by
  decide +kernel

private theorem receipt617 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨617, by decide⟩ cache617 partial617 = true := by
  decide +kernel

private theorem receipt616 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨616, by decide⟩ cache616 partial616 = true := by
  decide +kernel

private theorem receipt615 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨615, by decide⟩ cache615 partial615 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![616,617,618,619])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1361527262301459 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt616
  · exact receipt617
  · exact receipt618
  · exact receipt619

private theorem receipt614 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨614, by decide⟩ cache614 partial614 = true := by
  decide +kernel

private theorem receipt613 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨613, by decide⟩ cache613 partial613 = true := by
  decide +kernel

private theorem receipt612 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨612, by decide⟩ cache612 partial612 = true := by
  decide +kernel

private theorem receipt611 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨611, by decide⟩ cache611 partial611 = true := by
  decide +kernel

private theorem receipt610 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨610, by decide⟩ cache610 partial610 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![611,612,613,614])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1350529461013619 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt611
  · exact receipt612
  · exact receipt613
  · exact receipt614

private theorem receipt609 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨609, by decide⟩ cache609 partial609 = true := by
  decide +kernel

private theorem receipt608 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨608, by decide⟩ cache608 partial608 = true := by
  decide +kernel

private theorem receipt607 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨607, by decide⟩ cache607 partial607 = true := by
  decide +kernel

private theorem receipt606 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨606, by decide⟩ cache606 partial606 = true := by
  decide +kernel

private theorem receipt605 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨605, by decide⟩ cache605 partial605 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![606,607,608,609])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1339531659725779 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt606
  · exact receipt607
  · exact receipt608
  · exact receipt609

private theorem receipt604 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨604, by decide⟩ cache604 partial604 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![605,610,615,620])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1363724674026418 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt605
  · exact receipt610
  · exact receipt615
  · exact receipt620

private theorem receipt603 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨603, by decide⟩ cache603 partial603 = true := by
  decide +kernel

private theorem receipt602 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨602, by decide⟩ cache602 partial602 = true := by
  decide +kernel

private theorem receipt601 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨601, by decide⟩ cache601 partial601 = true := by
  decide +kernel

private theorem receipt600 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨600, by decide⟩ cache600 partial600 = true := by
  decide +kernel

private theorem receipt599 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨599, by decide⟩ cache599 partial599 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![600,601,602,603])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1326334298180371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt600
  · exact receipt601
  · exact receipt602
  · exact receipt603

private theorem receipt598 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨598, by decide⟩ cache598 partial598 = true := by
  decide +kernel

private theorem receipt597 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨597, by decide⟩ cache597 partial597 = true := by
  decide +kernel

private theorem receipt596 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨596, by decide⟩ cache596 partial596 = true := by
  decide +kernel

private theorem receipt595 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨595, by decide⟩ cache595 partial595 = true := by
  decide +kernel

private theorem receipt594 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨594, by decide⟩ cache594 partial594 = true := by
  decide +kernel

private theorem receipt593 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨593, by decide⟩ cache593 partial593 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![594,595,596,597])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1313136936634963 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt594
  · exact receipt595
  · exact receipt596
  · exact receipt597

private theorem receipt592 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨592, by decide⟩ cache592 partial592 = true := by
  decide +kernel

private theorem receipt591 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨591, by decide⟩ cache591 partial591 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![592,593,598,599])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1317536056625682 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt592
  · exact receipt593
  · exact receipt598
  · exact receipt599

private theorem receipt590 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨590, by decide⟩ cache590 partial590 = true := by
  decide +kernel

private theorem receipt589 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨589, by decide⟩ cache589 partial589 = true := by
  decide +kernel

private theorem receipt588 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨588, by decide⟩ cache588 partial588 = true := by
  decide +kernel

private theorem receipt587 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨587, by decide⟩ cache587 partial587 = true := by
  decide +kernel

private theorem receipt586 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨586, by decide⟩ cache586 partial586 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![587,588,589,590])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1297740014831987 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt587
  · exact receipt588
  · exact receipt589
  · exact receipt590

private theorem receipt585 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨585, by decide⟩ cache585 partial585 = true := by
  decide +kernel

private theorem receipt584 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨584, by decide⟩ cache584 partial584 = true := by
  decide +kernel

private theorem receipt583 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨583, by decide⟩ cache583 partial583 = true := by
  decide +kernel

private theorem receipt582 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨582, by decide⟩ cache582 partial582 = true := by
  decide +kernel

private theorem receipt581 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨581, by decide⟩ cache581 partial581 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![582,583,584,585])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1286742213544147 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt582
  · exact receipt583
  · exact receipt584
  · exact receipt585

private theorem receipt580 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨580, by decide⟩ cache580 partial580 = true := by
  decide +kernel

private theorem receipt579 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨579, by decide⟩ cache579 partial579 = true := by
  decide +kernel

private theorem receipt578 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨578, by decide⟩ cache578 partial578 = true := by
  decide +kernel

private theorem receipt577 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨577, by decide⟩ cache577 partial577 = true := by
  decide +kernel

private theorem receipt576 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨576, by decide⟩ cache576 partial576 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![577,578,579,580])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1275744412256307 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt577
  · exact receipt578
  · exact receipt579
  · exact receipt580

private theorem receipt575 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨575, by decide⟩ cache575 partial575 = true := by
  decide +kernel

private theorem receipt574 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨574, by decide⟩ cache574 partial574 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![575,576,581,586])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1288939625269234 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt575
  · exact receipt576
  · exact receipt581
  · exact receipt586

private theorem receipt573 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨573, by decide⟩ cache573 partial573 = true := by
  decide +kernel

theorem receipt572 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨572, by decide⟩ cache572 partial572 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![573,574,591,604])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1328527412316081 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt573
  · exact receipt574
  · exact receipt591
  · exact receipt604

private theorem receipt571 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨571, by decide⟩ cache571 partial571 = true := by
  decide +kernel

private theorem receipt570 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨570, by decide⟩ cache570 partial570 = true := by
  decide +kernel

private theorem receipt569 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨569, by decide⟩ cache569 partial569 = true := by
  decide +kernel

private theorem receipt568 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨568, by decide⟩ cache568 partial568 = true := by
  decide +kernel

private theorem receipt567 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨567, by decide⟩ cache567 partial567 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![568,569,570,571])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1255948369938195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt568
  · exact receipt569
  · exact receipt570
  · exact receipt571

private theorem receipt566 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨566, by decide⟩ cache566 partial566 = true := by
  decide +kernel

private theorem receipt565 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨565, by decide⟩ cache565 partial565 = true := by
  decide +kernel

private theorem receipt564 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨564, by decide⟩ cache564 partial564 = true := by
  decide +kernel

private theorem receipt563 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨563, by decide⟩ cache563 partial563 = true := by
  decide +kernel

private theorem receipt562 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨562, by decide⟩ cache562 partial562 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![563,564,565,566])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1244950568650355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt563
  · exact receipt564
  · exact receipt565
  · exact receipt566

private theorem receipt561 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨561, by decide⟩ cache561 partial561 = true := by
  decide +kernel

private theorem receipt560 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨560, by decide⟩ cache560 partial560 = true := by
  decide +kernel

private theorem receipt559 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨559, by decide⟩ cache559 partial559 = true := by
  decide +kernel

private theorem receipt558 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨558, by decide⟩ cache558 partial558 = true := by
  decide +kernel

private theorem receipt557 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨557, by decide⟩ cache557 partial557 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![558,559,560,561])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1233952767362515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt558
  · exact receipt559
  · exact receipt560
  · exact receipt561

private theorem receipt556 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨556, by decide⟩ cache556 partial556 = true := by
  decide +kernel

private theorem receipt555 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨555, by decide⟩ cache555 partial555 = true := by
  decide +kernel

private theorem receipt554 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨554, by decide⟩ cache554 partial554 = true := by
  decide +kernel

private theorem receipt553 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨553, by decide⟩ cache553 partial553 = true := by
  decide +kernel

private theorem receipt552 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨552, by decide⟩ cache552 partial552 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![553,554,555,556])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1222954966074675 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt553
  · exact receipt554
  · exact receipt555
  · exact receipt556

private theorem receipt551 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨551, by decide⟩ cache551 partial551 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![552,557,562,567])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1247147980375314 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt552
  · exact receipt557
  · exact receipt562
  · exact receipt567

private theorem receipt550 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨550, by decide⟩ cache550 partial550 = true := by
  decide +kernel

private theorem receipt549 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨549, by decide⟩ cache549 partial549 = true := by
  decide +kernel

private theorem receipt548 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨548, by decide⟩ cache548 partial548 = true := by
  decide +kernel

private theorem receipt547 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨547, by decide⟩ cache547 partial547 = true := by
  decide +kernel

private theorem receipt546 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨546, by decide⟩ cache546 partial546 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![547,548,549,550])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1209757604529266 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt547
  · exact receipt548
  · exact receipt549
  · exact receipt550

private theorem receipt545 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨545, by decide⟩ cache545 partial545 = true := by
  decide +kernel

private theorem receipt544 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨544, by decide⟩ cache544 partial544 = true := by
  decide +kernel

private theorem receipt543 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨543, by decide⟩ cache543 partial543 = true := by
  decide +kernel

private theorem receipt542 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨542, by decide⟩ cache542 partial542 = true := by
  decide +kernel

private theorem receipt541 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨541, by decide⟩ cache541 partial541 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![542,543,544,545])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1198759803241427 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt542
  · exact receipt543
  · exact receipt544
  · exact receipt545

private theorem receipt540 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨540, by decide⟩ cache540 partial540 = true := by
  decide +kernel

private theorem receipt539 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨539, by decide⟩ cache539 partial539 = true := by
  decide +kernel

private theorem receipt538 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨538, by decide⟩ cache538 partial538 = true := by
  decide +kernel

private theorem receipt537 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨537, by decide⟩ cache537 partial537 = true := by
  decide +kernel

private theorem receipt536 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨536, by decide⟩ cache536 partial536 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![537,538,539,540])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1187762001953587 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt537
  · exact receipt538
  · exact receipt539
  · exact receipt540

private theorem receipt535 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨535, by decide⟩ cache535 partial535 = true := by
  decide +kernel

private theorem receipt534 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨534, by decide⟩ cache534 partial534 = true := by
  decide +kernel

private theorem receipt533 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨533, by decide⟩ cache533 partial533 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![534,535,536,541])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1189959414203090 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt534
  · exact receipt535
  · exact receipt536
  · exact receipt541

private theorem receipt532 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨532, by decide⟩ cache532 partial532 = true := by
  decide +kernel

theorem receipt531 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨531, by decide⟩ cache531 partial531 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![532,533,546,551])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1211955015205521 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt532
  · exact receipt533
  · exact receipt546
  · exact receipt551

theorem receipt530 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨530, by decide⟩ cache530 partial530 = true := by
  decide +kernel

theorem receipt529 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨529, by decide⟩ cache529 partial529 = true := by
  decide +kernel

private theorem receipt527 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨527, by decide⟩ cache527 partial527 = true := by
  decide +kernel

private theorem receipt526 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨526, by decide⟩ cache526 partial526 = true := by
  decide +kernel

private theorem receipt525 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨525, by decide⟩ cache525 partial525 = true := by
  decide +kernel

private theorem receipt524 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨524, by decide⟩ cache524 partial524 = true := by
  decide +kernel

private theorem receipt523 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨523, by decide⟩ cache523 partial523 = true := by
  decide +kernel

private theorem receipt522 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨522, by decide⟩ cache522 partial522 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![523,524,525,526])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1156968158347635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt523
  · exact receipt524
  · exact receipt525
  · exact receipt526

private theorem receipt521 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨521, by decide⟩ cache521 partial521 = true := by
  decide +kernel

private theorem receipt520 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨520, by decide⟩ cache520 partial520 = true := by
  decide +kernel

private theorem receipt519 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨519, by decide⟩ cache519 partial519 = true := by
  decide +kernel

private theorem receipt518 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨518, by decide⟩ cache518 partial518 = true := by
  decide +kernel

private theorem receipt517 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨517, by decide⟩ cache517 partial517 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![518,519,520,521])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1145970357059795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt518
  · exact receipt519
  · exact receipt520
  · exact receipt521

private theorem receipt516 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨516, by decide⟩ cache516 partial516 = true := by
  decide +kernel

private theorem receipt515 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨515, by decide⟩ cache515 partial515 = true := by
  decide +kernel

private theorem receipt514 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨514, by decide⟩ cache514 partial514 = true := by
  decide +kernel

private theorem receipt513 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨513, by decide⟩ cache513 partial513 = true := by
  decide +kernel

private theorem receipt512 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨512, by decide⟩ cache512 partial512 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![513,514,515,516])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1134972555771955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt513
  · exact receipt514
  · exact receipt515
  · exact receipt516

#print axioms receipt512

private theorem receipt511 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨511, by decide⟩ cache511 partial511 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![512,517,522,527])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1159165570072594 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt512
  · exact receipt517
  · exact receipt522
  · exact receipt527

private theorem receipt510 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨510, by decide⟩ cache510 partial510 = true := by
  decide +kernel

private theorem receipt509 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨509, by decide⟩ cache509 partial509 = true := by
  decide +kernel

private theorem receipt508 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨508, by decide⟩ cache508 partial508 = true := by
  decide +kernel

private theorem receipt507 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨507, by decide⟩ cache507 partial507 = true := by
  decide +kernel

private theorem receipt506 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨506, by decide⟩ cache506 partial506 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![507,508,509,510])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1121775194226546 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt507
  · exact receipt508
  · exact receipt509
  · exact receipt510

private theorem receipt505 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨505, by decide⟩ cache505 partial505 = true := by
  decide +kernel

private theorem receipt504 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨504, by decide⟩ cache504 partial504 = true := by
  decide +kernel

private theorem receipt503 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨503, by decide⟩ cache503 partial503 = true := by
  decide +kernel

private theorem receipt502 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨502, by decide⟩ cache502 partial502 = true := by
  decide +kernel

private theorem receipt501 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨501, by decide⟩ cache501 partial501 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![502,503,504,505])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1110777392938707 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt502
  · exact receipt503
  · exact receipt504
  · exact receipt505

private theorem receipt500 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨500, by decide⟩ cache500 partial500 = true := by
  decide +kernel

private theorem receipt499 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨499, by decide⟩ cache499 partial499 = true := by
  decide +kernel

private theorem receipt498 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨498, by decide⟩ cache498 partial498 = true := by
  decide +kernel

private theorem receipt497 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨497, by decide⟩ cache497 partial497 = true := by
  decide +kernel

private theorem receipt496 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨496, by decide⟩ cache496 partial496 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![497,498,499,500])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1099779591650867 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt497
  · exact receipt498
  · exact receipt499
  · exact receipt500

private theorem receipt495 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨495, by decide⟩ cache495 partial495 = true := by
  decide +kernel

private theorem receipt494 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨494, by decide⟩ cache494 partial494 = true := by
  decide +kernel

private theorem receipt493 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨493, by decide⟩ cache493 partial493 = true := by
  decide +kernel

private theorem receipt492 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨492, by decide⟩ cache492 partial492 = true := by
  decide +kernel

private theorem receipt491 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨491, by decide⟩ cache491 partial491 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![492,493,494,495])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1088781790363027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt492
  · exact receipt493
  · exact receipt494
  · exact receipt495

private theorem receipt490 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨490, by decide⟩ cache490 partial490 = true := by
  decide +kernel

private theorem receipt489 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨489, by decide⟩ cache489 partial489 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![490,491,496,501])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1101977003375954 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt490
  · exact receipt491
  · exact receipt496
  · exact receipt501

private theorem receipt488 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨488, by decide⟩ cache488 partial488 = true := by
  decide +kernel

theorem receipt487 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨487, by decide⟩ cache487 partial487 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![488,489,506,511])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1123972604378385 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt488
  · exact receipt489
  · exact receipt506
  · exact receipt511

private theorem receipt486 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨486, by decide⟩ cache486 partial486 = true := by
  decide +kernel

private theorem receipt485 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨485, by decide⟩ cache485 partial485 = true := by
  decide +kernel

private theorem receipt484 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨484, by decide⟩ cache484 partial484 = true := by
  decide +kernel

private theorem receipt483 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨483, by decide⟩ cache483 partial483 = true := by
  decide +kernel

private theorem receipt482 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨482, by decide⟩ cache482 partial482 = true := by
  decide +kernel

private theorem receipt481 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨481, by decide⟩ cache481 partial481 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![482,483,484,485])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1066786187787347 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt482
  · exact receipt483
  · exact receipt484
  · exact receipt485

private theorem receipt480 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨480, by decide⟩ cache480 partial480 = true := by
  decide +kernel

private theorem receipt479 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨479, by decide⟩ cache479 partial479 = true := by
  decide +kernel

private theorem receipt478 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨478, by decide⟩ cache478 partial478 = true := by
  decide +kernel

private theorem receipt477 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨477, by decide⟩ cache477 partial477 = true := by
  decide +kernel

private theorem receipt476 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨476, by decide⟩ cache476 partial476 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![477,478,479,480])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1055788386499507 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt477
  · exact receipt478
  · exact receipt479
  · exact receipt480

private theorem receipt475 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨475, by decide⟩ cache475 partial475 = true := by
  decide +kernel

private theorem receipt474 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨474, by decide⟩ cache474 partial474 = true := by
  decide +kernel

private theorem receipt473 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨473, by decide⟩ cache473 partial473 = true := by
  decide +kernel

private theorem receipt472 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨472, by decide⟩ cache472 partial472 = true := by
  decide +kernel

private theorem receipt471 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨471, by decide⟩ cache471 partial471 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![472,473,474,475])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1044790585211667 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt472
  · exact receipt473
  · exact receipt474
  · exact receipt475

private theorem receipt470 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨470, by decide⟩ cache470 partial470 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![471,476,481,486])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1068983599512306 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt471
  · exact receipt476
  · exact receipt481
  · exact receipt486

private theorem receipt469 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨469, by decide⟩ cache469 partial469 = true := by
  decide +kernel

private theorem receipt468 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨468, by decide⟩ cache468 partial468 = true := by
  decide +kernel

private theorem receipt467 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨467, by decide⟩ cache467 partial467 = true := by
  decide +kernel

private theorem receipt466 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨466, by decide⟩ cache466 partial466 = true := by
  decide +kernel

private theorem receipt465 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨465, by decide⟩ cache465 partial465 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![466,467,468,469])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1031593223666258 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt466
  · exact receipt467
  · exact receipt468
  · exact receipt469

private theorem receipt464 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨464, by decide⟩ cache464 partial464 = true := by
  decide +kernel

private theorem receipt463 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨463, by decide⟩ cache463 partial463 = true := by
  decide +kernel

private theorem receipt462 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨462, by decide⟩ cache462 partial462 = true := by
  decide +kernel

private theorem receipt461 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨461, by decide⟩ cache461 partial461 = true := by
  decide +kernel

private theorem receipt460 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨460, by decide⟩ cache460 partial460 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![461,462,463,464])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1020595422378419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt461
  · exact receipt462
  · exact receipt463
  · exact receipt464

private theorem receipt459 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨459, by decide⟩ cache459 partial459 = true := by
  decide +kernel

private theorem receipt458 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨458, by decide⟩ cache458 partial458 = true := by
  decide +kernel

private theorem receipt457 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨457, by decide⟩ cache457 partial457 = true := by
  decide +kernel

private theorem receipt456 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨456, by decide⟩ cache456 partial456 = true := by
  decide +kernel

private theorem receipt455 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨455, by decide⟩ cache455 partial455 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![456,457,458,459])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1009597621090579 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt456
  · exact receipt457
  · exact receipt458
  · exact receipt459

private theorem receipt454 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨454, by decide⟩ cache454 partial454 = true := by
  decide +kernel

private theorem receipt453 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨453, by decide⟩ cache453 partial453 = true := by
  decide +kernel

private theorem receipt452 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨452, by decide⟩ cache452 partial452 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![453,454,455,460])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1011795033340082 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt453
  · exact receipt454
  · exact receipt455
  · exact receipt460

private theorem receipt451 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨451, by decide⟩ cache451 partial451 = true := by
  decide +kernel

theorem receipt450 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨450, by decide⟩ cache450 partial450 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![451,452,465,470])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1033790634342513 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt451
  · exact receipt452
  · exact receipt465
  · exact receipt470

theorem receipt449 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨449, by decide⟩ cache449 partial449 = true := by
  decide +kernel

theorem receipt448 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨448, by decide⟩ cache448 partial448 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock11
