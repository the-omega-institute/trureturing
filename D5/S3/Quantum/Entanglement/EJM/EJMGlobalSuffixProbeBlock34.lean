/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock34
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock34
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock34
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

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


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock34
