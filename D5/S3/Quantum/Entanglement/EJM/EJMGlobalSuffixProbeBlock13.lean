/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock13
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock13
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1402 : Cache :=
  step cache1401 ⟨17, by decide⟩ 0
private def partial1402 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 0)

private def cache1403 : Cache :=
  step cache1401 ⟨17, by decide⟩ 1
private def partial1403 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 1)

private def cache1404 : Cache :=
  step cache1403 ⟨18, by decide⟩ 0
private def partial1404 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 0)

private def cache1405 : Cache :=
  step cache1403 ⟨18, by decide⟩ 1
private def partial1405 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 1)

private def cache1406 : Cache :=
  step cache1405 ⟨19, by decide⟩ 0
private def partial1406 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 0)

private def cache1407 : Cache :=
  step cache1405 ⟨19, by decide⟩ 1
private def partial1407 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 1)

private def cache1408 : Cache :=
  step cache1405 ⟨19, by decide⟩ 2
private def partial1408 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 2)

private def cache1409 : Cache :=
  step cache1405 ⟨19, by decide⟩ 3
private def partial1409 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1405 ⟨19, by decide⟩ (some 3)

private def cache1410 : Cache :=
  step cache1403 ⟨18, by decide⟩ 2
private def partial1410 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 2)

private def cache1411 : Cache :=
  step cache1403 ⟨18, by decide⟩ 3
private def partial1411 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1403 ⟨18, by decide⟩ (some 3)

private def cache1412 : Cache :=
  step cache1411 ⟨19, by decide⟩ 0
private def partial1412 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 0)

private def cache1413 : Cache :=
  step cache1411 ⟨19, by decide⟩ 1
private def partial1413 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 1)

private def cache1414 : Cache :=
  step cache1411 ⟨19, by decide⟩ 2
private def partial1414 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 2)

private def cache1415 : Cache :=
  step cache1411 ⟨19, by decide⟩ 3
private def partial1415 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1411 ⟨19, by decide⟩ (some 3)

private def cache1416 : Cache :=
  step cache1401 ⟨17, by decide⟩ 2
private def partial1416 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 2)

private def cache1417 : Cache :=
  step cache1416 ⟨18, by decide⟩ 0
private def partial1417 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 0)

private def cache1418 : Cache :=
  step cache1417 ⟨19, by decide⟩ 0
private def partial1418 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 0)

private def cache1419 : Cache :=
  step cache1417 ⟨19, by decide⟩ 1
private def partial1419 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 1)

private def cache1420 : Cache :=
  step cache1417 ⟨19, by decide⟩ 2
private def partial1420 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 2)

private def cache1421 : Cache :=
  step cache1417 ⟨19, by decide⟩ 3
private def partial1421 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1417 ⟨19, by decide⟩ (some 3)

private def cache1422 : Cache :=
  step cache1416 ⟨18, by decide⟩ 1
private def partial1422 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 1)

private def cache1423 : Cache :=
  step cache1422 ⟨19, by decide⟩ 0
private def partial1423 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 0)

private def cache1424 : Cache :=
  step cache1422 ⟨19, by decide⟩ 1
private def partial1424 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 1)

private def cache1425 : Cache :=
  step cache1422 ⟨19, by decide⟩ 2
private def partial1425 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 2)

private def cache1426 : Cache :=
  step cache1422 ⟨19, by decide⟩ 3
private def partial1426 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1422 ⟨19, by decide⟩ (some 3)

private def cache1427 : Cache :=
  step cache1416 ⟨18, by decide⟩ 2
private def partial1427 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 2)

private def cache1428 : Cache :=
  step cache1416 ⟨18, by decide⟩ 3
private def partial1428 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1416 ⟨18, by decide⟩ (some 3)

private def cache1429 : Cache :=
  step cache1428 ⟨19, by decide⟩ 0
private def partial1429 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 0)

private def cache1430 : Cache :=
  step cache1428 ⟨19, by decide⟩ 1
private def partial1430 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 1)

private def cache1431 : Cache :=
  step cache1428 ⟨19, by decide⟩ 2
private def partial1431 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 2)

private def cache1432 : Cache :=
  step cache1428 ⟨19, by decide⟩ 3
private def partial1432 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1428 ⟨19, by decide⟩ (some 3)

private def cache1433 : Cache :=
  step cache1401 ⟨17, by decide⟩ 3
private def partial1433 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1401 ⟨17, by decide⟩ (some 3)

private def cache1434 : Cache :=
  step cache1433 ⟨18, by decide⟩ 0
private def partial1434 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 0)

private def cache1435 : Cache :=
  step cache1433 ⟨18, by decide⟩ 1
private def partial1435 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 1)

private def cache1436 : Cache :=
  step cache1433 ⟨18, by decide⟩ 2
private def partial1436 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 2)

private def cache1437 : Cache :=
  step cache1433 ⟨18, by decide⟩ 3
private def partial1437 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1433 ⟨18, by decide⟩ (some 3)

private def cache1442 : Cache :=
  step cache1441 ⟨17, by decide⟩ 0
private def partial1442 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 0)

private def cache1443 : Cache :=
  step cache1441 ⟨17, by decide⟩ 1
private def partial1443 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 1)

private def cache1444 : Cache :=
  step cache1441 ⟨17, by decide⟩ 2
private def partial1444 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 2)

private def cache1445 : Cache :=
  step cache1444 ⟨18, by decide⟩ 0
private def partial1445 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 0)

private def cache1446 : Cache :=
  step cache1444 ⟨18, by decide⟩ 1
private def partial1446 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 1)

private def cache1447 : Cache :=
  step cache1444 ⟨18, by decide⟩ 2
private def partial1447 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 2)

private def cache1448 : Cache :=
  step cache1444 ⟨18, by decide⟩ 3
private def partial1448 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1444 ⟨18, by decide⟩ (some 3)

private def cache1449 : Cache :=
  step cache1448 ⟨19, by decide⟩ 0
private def partial1449 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 0)

private def cache1450 : Cache :=
  step cache1448 ⟨19, by decide⟩ 1
private def partial1450 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 1)

private def cache1451 : Cache :=
  step cache1448 ⟨19, by decide⟩ 2
private def partial1451 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 2)

private def cache1452 : Cache :=
  step cache1448 ⟨19, by decide⟩ 3
private def partial1452 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1448 ⟨19, by decide⟩ (some 3)

private def cache1453 : Cache :=
  step cache1441 ⟨17, by decide⟩ 3
private def partial1453 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1441 ⟨17, by decide⟩ (some 3)

private def cache1454 : Cache :=
  step cache1453 ⟨18, by decide⟩ 0
private def partial1454 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 0)

private def cache1455 : Cache :=
  step cache1454 ⟨19, by decide⟩ 0
private def partial1455 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 0)

private def cache1456 : Cache :=
  step cache1454 ⟨19, by decide⟩ 1
private def partial1456 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 1)

private def cache1457 : Cache :=
  step cache1454 ⟨19, by decide⟩ 2
private def partial1457 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 2)

private def cache1458 : Cache :=
  step cache1454 ⟨19, by decide⟩ 3
private def partial1458 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1454 ⟨19, by decide⟩ (some 3)

private def cache1459 : Cache :=
  step cache1453 ⟨18, by decide⟩ 1
private def partial1459 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 1)

private def cache1460 : Cache :=
  step cache1459 ⟨19, by decide⟩ 0
private def partial1460 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 0)

private def cache1461 : Cache :=
  step cache1459 ⟨19, by decide⟩ 1
private def partial1461 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 1)

private def cache1462 : Cache :=
  step cache1459 ⟨19, by decide⟩ 2
private def partial1462 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 2)

private def cache1463 : Cache :=
  step cache1459 ⟨19, by decide⟩ 3
private def partial1463 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1459 ⟨19, by decide⟩ (some 3)

private def cache1464 : Cache :=
  step cache1453 ⟨18, by decide⟩ 2
private def partial1464 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 2)

private def cache1465 : Cache :=
  step cache1453 ⟨18, by decide⟩ 3
private def partial1465 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1453 ⟨18, by decide⟩ (some 3)

private theorem receipt1465 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1465, by decide⟩ cache1465 partial1465 = true := by
  decide +kernel

private theorem receipt1464 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1464, by decide⟩ cache1464 partial1464 = true := by
  decide +kernel

private theorem receipt1463 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1463, by decide⟩ cache1463 partial1463 = true := by
  decide +kernel

private theorem receipt1462 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1462, by decide⟩ cache1462 partial1462 = true := by
  decide +kernel

private theorem receipt1461 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1461, by decide⟩ cache1461 partial1461 = true := by
  decide +kernel

private theorem receipt1460 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1460, by decide⟩ cache1460 partial1460 = true := by
  decide +kernel

private theorem receipt1459 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1459, by decide⟩ cache1459 partial1459 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1460,1461,1462,1463])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3217956119688851 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1460
  · exact receipt1461
  · exact receipt1462
  · exact receipt1463

private theorem receipt1458 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1458, by decide⟩ cache1458 partial1458 = true := by
  decide +kernel

private theorem receipt1457 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1457, by decide⟩ cache1457 partial1457 = true := by
  decide +kernel

private theorem receipt1456 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1456, by decide⟩ cache1456 partial1456 = true := by
  decide +kernel

private theorem receipt1455 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1455, by decide⟩ cache1455 partial1455 = true := by
  decide +kernel

private theorem receipt1454 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1454, by decide⟩ cache1454 partial1454 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1455,1456,1457,1458])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3206958318401011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1455
  · exact receipt1456
  · exact receipt1457
  · exact receipt1458

private theorem receipt1453 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1453, by decide⟩ cache1453 partial1453 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1454,1459,1464,1465])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3222355239679442 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1454
  · exact receipt1459
  · exact receipt1464
  · exact receipt1465

private theorem receipt1452 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1452, by decide⟩ cache1452 partial1452 = true := by
  decide +kernel

private theorem receipt1451 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1451, by decide⟩ cache1451 partial1451 = true := by
  decide +kernel

private theorem receipt1450 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1450, by decide⟩ cache1450 partial1450 = true := by
  decide +kernel

private theorem receipt1449 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1449, by decide⟩ cache1449 partial1449 = true := by
  decide +kernel

private theorem receipt1448 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1448, by decide⟩ cache1448 partial1448 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1449,1450,1451,1452])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3193760956855603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1449
  · exact receipt1450
  · exact receipt1451
  · exact receipt1452

private theorem receipt1447 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1447, by decide⟩ cache1447 partial1447 = true := by
  decide +kernel

private theorem receipt1446 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1446, by decide⟩ cache1446 partial1446 = true := by
  decide +kernel

private theorem receipt1445 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1445, by decide⟩ cache1445 partial1445 = true := by
  decide +kernel

private theorem receipt1444 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1444, by decide⟩ cache1444 partial1444 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1445,1446,1447,1448])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3184962715825330 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1445
  · exact receipt1446
  · exact receipt1447
  · exact receipt1448

private theorem receipt1443 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1443, by decide⟩ cache1443 partial1443 = true := by
  decide +kernel

private theorem receipt1442 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1442, by decide⟩ cache1442 partial1442 = true := by
  decide +kernel

theorem receipt1441 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1441, by decide⟩ cache1441 partial1441 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1442,1443,1444,1453])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3195956221097041 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1442
  · exact receipt1443
  · exact receipt1444
  · exact receipt1453

theorem receipt1440 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1440, by decide⟩ cache1440 partial1440 = true := by
  decide +kernel

theorem receipt1439 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1439, by decide⟩ cache1439 partial1439 = true := by
  decide +kernel

private theorem receipt1437 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1437, by decide⟩ cache1437 partial1437 = true := by
  decide +kernel

private theorem receipt1436 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1436, by decide⟩ cache1436 partial1436 = true := by
  decide +kernel

private theorem receipt1435 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1435, by decide⟩ cache1435 partial1435 = true := by
  decide +kernel

private theorem receipt1434 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1434, by decide⟩ cache1434 partial1434 = true := by
  decide +kernel

private theorem receipt1433 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1433, by decide⟩ cache1433 partial1433 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1434,1435,1436,1437])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3160767552992082 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1434
  · exact receipt1435
  · exact receipt1436
  · exact receipt1437

private theorem receipt1432 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1432, by decide⟩ cache1432 partial1432 = true := by
  decide +kernel

private theorem receipt1431 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1431, by decide⟩ cache1431 partial1431 = true := by
  decide +kernel

private theorem receipt1430 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1430, by decide⟩ cache1430 partial1430 = true := by
  decide +kernel

private theorem receipt1429 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1429, by decide⟩ cache1429 partial1429 = true := by
  decide +kernel

private theorem receipt1428 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1428, by decide⟩ cache1428 partial1428 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1429,1430,1431,1432])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3149769751704243 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1429
  · exact receipt1430
  · exact receipt1431
  · exact receipt1432

private theorem receipt1427 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1427, by decide⟩ cache1427 partial1427 = true := by
  decide +kernel

private theorem receipt1426 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1426, by decide⟩ cache1426 partial1426 = true := by
  decide +kernel

private theorem receipt1425 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1425, by decide⟩ cache1425 partial1425 = true := by
  decide +kernel

private theorem receipt1424 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1424, by decide⟩ cache1424 partial1424 = true := by
  decide +kernel

private theorem receipt1423 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1423, by decide⟩ cache1423 partial1423 = true := by
  decide +kernel

private theorem receipt1422 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1422, by decide⟩ cache1422 partial1422 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1423,1424,1425,1426])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3136572390158835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1423
  · exact receipt1424
  · exact receipt1425
  · exact receipt1426

private theorem receipt1421 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1421, by decide⟩ cache1421 partial1421 = true := by
  decide +kernel

private theorem receipt1420 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1420, by decide⟩ cache1420 partial1420 = true := by
  decide +kernel

private theorem receipt1419 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1419, by decide⟩ cache1419 partial1419 = true := by
  decide +kernel

private theorem receipt1418 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1418, by decide⟩ cache1418 partial1418 = true := by
  decide +kernel

private theorem receipt1417 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1417, by decide⟩ cache1417 partial1417 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1418,1419,1420,1421])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3125574588870995 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1418
  · exact receipt1419
  · exact receipt1420
  · exact receipt1421

private theorem receipt1416 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1416, by decide⟩ cache1416 partial1416 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1417,1422,1427,1428])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3140971510149426 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1417
  · exact receipt1422
  · exact receipt1427
  · exact receipt1428

private theorem receipt1415 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1415, by decide⟩ cache1415 partial1415 = true := by
  decide +kernel

private theorem receipt1414 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1414, by decide⟩ cache1414 partial1414 = true := by
  decide +kernel

private theorem receipt1413 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1413, by decide⟩ cache1413 partial1413 = true := by
  decide +kernel

private theorem receipt1412 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1412, by decide⟩ cache1412 partial1412 = true := by
  decide +kernel

private theorem receipt1411 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1411, by decide⟩ cache1411 partial1411 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1412,1413,1414,1415])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3112377227325587 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1412
  · exact receipt1413
  · exact receipt1414
  · exact receipt1415

private theorem receipt1410 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1410, by decide⟩ cache1410 partial1410 = true := by
  decide +kernel

private theorem receipt1409 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1409, by decide⟩ cache1409 partial1409 = true := by
  decide +kernel

private theorem receipt1408 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1408, by decide⟩ cache1408 partial1408 = true := by
  decide +kernel

private theorem receipt1407 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1407, by decide⟩ cache1407 partial1407 = true := by
  decide +kernel

private theorem receipt1406 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1406, by decide⟩ cache1406 partial1406 = true := by
  decide +kernel

private theorem receipt1405 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1405, by decide⟩ cache1405 partial1405 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1406,1407,1408,1409])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3099179865780179 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1406
  · exact receipt1407
  · exact receipt1408
  · exact receipt1409

private theorem receipt1404 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1404, by decide⟩ cache1404 partial1404 = true := by
  decide +kernel

private theorem receipt1403 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1403, by decide⟩ cache1403 partial1403 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1404,1405,1410,1411])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3103578985770898 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1404
  · exact receipt1405
  · exact receipt1410
  · exact receipt1411

private theorem receipt1402 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1402, by decide⟩ cache1402 partial1402 = true := by
  decide +kernel

theorem receipt1401 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1401, by decide⟩ cache1401 partial1401 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1402,1403,1416,1433])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3151960718356305 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1402
  · exact receipt1403
  · exact receipt1416
  · exact receipt1433


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
