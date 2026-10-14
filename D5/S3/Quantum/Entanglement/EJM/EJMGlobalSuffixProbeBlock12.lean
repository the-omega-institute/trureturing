/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock12
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock12
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1467 : Cache :=
  step cache1466 ⟨17, by decide⟩ 0
private def partial1467 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1466 ⟨17, by decide⟩ (some 0)

private def cache1468 : Cache :=
  step cache1466 ⟨17, by decide⟩ 1
private def partial1468 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1466 ⟨17, by decide⟩ (some 1)

private def cache1469 : Cache :=
  step cache1468 ⟨18, by decide⟩ 0
private def partial1469 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1468 ⟨18, by decide⟩ (some 0)

private def cache1470 : Cache :=
  step cache1468 ⟨18, by decide⟩ 1
private def partial1470 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1468 ⟨18, by decide⟩ (some 1)

private def cache1471 : Cache :=
  step cache1470 ⟨19, by decide⟩ 0
private def partial1471 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1470 ⟨19, by decide⟩ (some 0)

private def cache1472 : Cache :=
  step cache1470 ⟨19, by decide⟩ 1
private def partial1472 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1470 ⟨19, by decide⟩ (some 1)

private def cache1473 : Cache :=
  step cache1470 ⟨19, by decide⟩ 2
private def partial1473 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1470 ⟨19, by decide⟩ (some 2)

private def cache1474 : Cache :=
  step cache1470 ⟨19, by decide⟩ 3
private def partial1474 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1470 ⟨19, by decide⟩ (some 3)

private def cache1475 : Cache :=
  step cache1468 ⟨18, by decide⟩ 2
private def partial1475 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1468 ⟨18, by decide⟩ (some 2)

private def cache1476 : Cache :=
  step cache1468 ⟨18, by decide⟩ 3
private def partial1476 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1468 ⟨18, by decide⟩ (some 3)

private def cache1477 : Cache :=
  step cache1466 ⟨17, by decide⟩ 2
private def partial1477 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1466 ⟨17, by decide⟩ (some 2)

private def cache1478 : Cache :=
  step cache1477 ⟨18, by decide⟩ 0
private def partial1478 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1477 ⟨18, by decide⟩ (some 0)

private def cache1479 : Cache :=
  step cache1478 ⟨19, by decide⟩ 0
private def partial1479 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1478 ⟨19, by decide⟩ (some 0)

private def cache1480 : Cache :=
  step cache1478 ⟨19, by decide⟩ 1
private def partial1480 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1478 ⟨19, by decide⟩ (some 1)

private def cache1481 : Cache :=
  step cache1478 ⟨19, by decide⟩ 2
private def partial1481 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1478 ⟨19, by decide⟩ (some 2)

private def cache1482 : Cache :=
  step cache1478 ⟨19, by decide⟩ 3
private def partial1482 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1478 ⟨19, by decide⟩ (some 3)

private def cache1483 : Cache :=
  step cache1477 ⟨18, by decide⟩ 1
private def partial1483 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1477 ⟨18, by decide⟩ (some 1)

private def cache1484 : Cache :=
  step cache1483 ⟨19, by decide⟩ 0
private def partial1484 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1483 ⟨19, by decide⟩ (some 0)

private def cache1485 : Cache :=
  step cache1483 ⟨19, by decide⟩ 1
private def partial1485 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1483 ⟨19, by decide⟩ (some 1)

private def cache1486 : Cache :=
  step cache1483 ⟨19, by decide⟩ 2
private def partial1486 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1483 ⟨19, by decide⟩ (some 2)

private def cache1487 : Cache :=
  step cache1483 ⟨19, by decide⟩ 3
private def partial1487 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1483 ⟨19, by decide⟩ (some 3)

private def cache1488 : Cache :=
  step cache1477 ⟨18, by decide⟩ 2
private def partial1488 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1477 ⟨18, by decide⟩ (some 2)

private def cache1489 : Cache :=
  step cache1477 ⟨18, by decide⟩ 3
private def partial1489 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1477 ⟨18, by decide⟩ (some 3)

private def cache1490 : Cache :=
  step cache1489 ⟨19, by decide⟩ 0
private def partial1490 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1489 ⟨19, by decide⟩ (some 0)

private def cache1491 : Cache :=
  step cache1489 ⟨19, by decide⟩ 1
private def partial1491 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1489 ⟨19, by decide⟩ (some 1)

private def cache1492 : Cache :=
  step cache1489 ⟨19, by decide⟩ 2
private def partial1492 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1489 ⟨19, by decide⟩ (some 2)

private def cache1493 : Cache :=
  step cache1489 ⟨19, by decide⟩ 3
private def partial1493 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1489 ⟨19, by decide⟩ (some 3)

private def cache1494 : Cache :=
  step cache1466 ⟨17, by decide⟩ 3
private def partial1494 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1466 ⟨17, by decide⟩ (some 3)

private def cache1495 : Cache :=
  step cache1494 ⟨18, by decide⟩ 0
private def partial1495 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1494 ⟨18, by decide⟩ (some 0)

private def cache1496 : Cache :=
  step cache1495 ⟨19, by decide⟩ 0
private def partial1496 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1495 ⟨19, by decide⟩ (some 0)

private def cache1497 : Cache :=
  step cache1495 ⟨19, by decide⟩ 1
private def partial1497 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1495 ⟨19, by decide⟩ (some 1)

private def cache1498 : Cache :=
  step cache1495 ⟨19, by decide⟩ 2
private def partial1498 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1495 ⟨19, by decide⟩ (some 2)

private def cache1499 : Cache :=
  step cache1495 ⟨19, by decide⟩ 3
private def partial1499 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1495 ⟨19, by decide⟩ (some 3)

private def cache1500 : Cache :=
  step cache1494 ⟨18, by decide⟩ 1
private def partial1500 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1494 ⟨18, by decide⟩ (some 1)

private def cache1501 : Cache :=
  step cache1500 ⟨19, by decide⟩ 0
private def partial1501 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1500 ⟨19, by decide⟩ (some 0)

private def cache1502 : Cache :=
  step cache1500 ⟨19, by decide⟩ 1
private def partial1502 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1500 ⟨19, by decide⟩ (some 1)

private def cache1503 : Cache :=
  step cache1500 ⟨19, by decide⟩ 2
private def partial1503 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1500 ⟨19, by decide⟩ (some 2)

private def cache1504 : Cache :=
  step cache1500 ⟨19, by decide⟩ 3
private def partial1504 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1500 ⟨19, by decide⟩ (some 3)

private def cache1505 : Cache :=
  step cache1494 ⟨18, by decide⟩ 2
private def partial1505 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1494 ⟨18, by decide⟩ (some 2)

private def cache1506 : Cache :=
  step cache1494 ⟨18, by decide⟩ 3
private def partial1506 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1494 ⟨18, by decide⟩ (some 3)

private theorem receipt1506 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1506, by decide⟩ cache1506 partial1506 = true := by
  decide +kernel

private theorem receipt1505 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1505, by decide⟩ cache1505 partial1505 = true := by
  decide +kernel

private theorem receipt1504 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1504, by decide⟩ cache1504 partial1504 = true := by
  decide +kernel

private theorem receipt1503 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1503, by decide⟩ cache1503 partial1503 = true := by
  decide +kernel

private theorem receipt1502 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1502, by decide⟩ cache1502 partial1502 = true := by
  decide +kernel

private theorem receipt1501 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1501, by decide⟩ cache1501 partial1501 = true := by
  decide +kernel

private theorem receipt1500 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1500, by decide⟩ cache1500 partial1500 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1501,1502,1503,1504])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3308138090249139 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1501
  · exact receipt1502
  · exact receipt1503
  · exact receipt1504

private theorem receipt1499 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1499, by decide⟩ cache1499 partial1499 = true := by
  decide +kernel

private theorem receipt1498 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1498, by decide⟩ cache1498 partial1498 = true := by
  decide +kernel

private theorem receipt1497 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1497, by decide⟩ cache1497 partial1497 = true := by
  decide +kernel

private theorem receipt1496 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1496, by decide⟩ cache1496 partial1496 = true := by
  decide +kernel

private theorem receipt1495 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1495, by decide⟩ cache1495 partial1495 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1496,1497,1498,1499])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3297140288961299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1496
  · exact receipt1497
  · exact receipt1498
  · exact receipt1499

private theorem receipt1494 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1494, by decide⟩ cache1494 partial1494 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1495,1500,1505,1506])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3312537210239730 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1495
  · exact receipt1500
  · exact receipt1505
  · exact receipt1506

private theorem receipt1493 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1493, by decide⟩ cache1493 partial1493 = true := by
  decide +kernel

private theorem receipt1492 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1492, by decide⟩ cache1492 partial1492 = true := by
  decide +kernel

private theorem receipt1491 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1491, by decide⟩ cache1491 partial1491 = true := by
  decide +kernel

private theorem receipt1490 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1490, by decide⟩ cache1490 partial1490 = true := by
  decide +kernel

private theorem receipt1489 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1489, by decide⟩ cache1489 partial1489 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1490,1491,1492,1493])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3283942927415891 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1490
  · exact receipt1491
  · exact receipt1492
  · exact receipt1493

private theorem receipt1488 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1488, by decide⟩ cache1488 partial1488 = true := by
  decide +kernel

private theorem receipt1487 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1487, by decide⟩ cache1487 partial1487 = true := by
  decide +kernel

private theorem receipt1486 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1486, by decide⟩ cache1486 partial1486 = true := by
  decide +kernel

private theorem receipt1485 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1485, by decide⟩ cache1485 partial1485 = true := by
  decide +kernel

private theorem receipt1484 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1484, by decide⟩ cache1484 partial1484 = true := by
  decide +kernel

private theorem receipt1483 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1483, by decide⟩ cache1483 partial1483 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1484,1485,1486,1487])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3270745565870483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1484
  · exact receipt1485
  · exact receipt1486
  · exact receipt1487

private theorem receipt1482 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1482, by decide⟩ cache1482 partial1482 = true := by
  decide +kernel

private theorem receipt1481 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1481, by decide⟩ cache1481 partial1481 = true := by
  decide +kernel

private theorem receipt1480 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1480, by decide⟩ cache1480 partial1480 = true := by
  decide +kernel

private theorem receipt1479 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1479, by decide⟩ cache1479 partial1479 = true := by
  decide +kernel

private theorem receipt1478 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1478, by decide⟩ cache1478 partial1478 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1479,1480,1481,1482])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3259747764582643 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1479
  · exact receipt1480
  · exact receipt1481
  · exact receipt1482

private theorem receipt1477 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1477, by decide⟩ cache1477 partial1477 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1478,1483,1488,1489])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3275144685861074 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1478
  · exact receipt1483
  · exact receipt1488
  · exact receipt1489

private theorem receipt1476 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1476, by decide⟩ cache1476 partial1476 = true := by
  decide +kernel

private theorem receipt1475 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1475, by decide⟩ cache1475 partial1475 = true := by
  decide +kernel

private theorem receipt1474 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1474, by decide⟩ cache1474 partial1474 = true := by
  decide +kernel

private theorem receipt1473 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1473, by decide⟩ cache1473 partial1473 = true := by
  decide +kernel

private theorem receipt1472 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1472, by decide⟩ cache1472 partial1472 = true := by
  decide +kernel

private theorem receipt1471 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1471, by decide⟩ cache1471 partial1471 = true := by
  decide +kernel

private theorem receipt1470 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1470, by decide⟩ cache1470 partial1470 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1471,1472,1473,1474])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3242151282522099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1471
  · exact receipt1472
  · exact receipt1473
  · exact receipt1474

private theorem receipt1469 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1469, by decide⟩ cache1469 partial1469 = true := by
  decide +kernel

private theorem receipt1468 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1468, by decide⟩ cache1468 partial1468 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1469,1470,1475,1476])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3246550402512818 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1469
  · exact receipt1470
  · exact receipt1475
  · exact receipt1476

private theorem receipt1467 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1467, by decide⟩ cache1467 partial1467 = true := by
  decide +kernel

theorem receipt1466 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1466, by decide⟩ cache1466 partial1466 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1467,1468,1477,1494])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3286133894592369 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1467
  · exact receipt1468
  · exact receipt1477
  · exact receipt1494


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock12
