/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock10
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock10
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock10
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1541 : Cache :=
  step cache1540 ⟨17, by decide⟩ 0
private def partial1541 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1540 ⟨17, by decide⟩ (some 0)

private def cache1542 : Cache :=
  step cache1540 ⟨17, by decide⟩ 1
private def partial1542 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1540 ⟨17, by decide⟩ (some 1)

private def cache1543 : Cache :=
  step cache1542 ⟨18, by decide⟩ 0
private def partial1543 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1542 ⟨18, by decide⟩ (some 0)

private def cache1544 : Cache :=
  step cache1542 ⟨18, by decide⟩ 1
private def partial1544 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1542 ⟨18, by decide⟩ (some 1)

private def cache1545 : Cache :=
  step cache1544 ⟨19, by decide⟩ 0
private def partial1545 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1544 ⟨19, by decide⟩ (some 0)

private def cache1546 : Cache :=
  step cache1544 ⟨19, by decide⟩ 1
private def partial1546 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1544 ⟨19, by decide⟩ (some 1)

private def cache1547 : Cache :=
  step cache1544 ⟨19, by decide⟩ 2
private def partial1547 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1544 ⟨19, by decide⟩ (some 2)

private def cache1548 : Cache :=
  step cache1544 ⟨19, by decide⟩ 3
private def partial1548 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1544 ⟨19, by decide⟩ (some 3)

private def cache1549 : Cache :=
  step cache1542 ⟨18, by decide⟩ 2
private def partial1549 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1542 ⟨18, by decide⟩ (some 2)

private def cache1550 : Cache :=
  step cache1549 ⟨19, by decide⟩ 0
private def partial1550 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1549 ⟨19, by decide⟩ (some 0)

private def cache1551 : Cache :=
  step cache1549 ⟨19, by decide⟩ 1
private def partial1551 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1549 ⟨19, by decide⟩ (some 1)

private def cache1552 : Cache :=
  step cache1549 ⟨19, by decide⟩ 2
private def partial1552 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1549 ⟨19, by decide⟩ (some 2)

private def cache1553 : Cache :=
  step cache1549 ⟨19, by decide⟩ 3
private def partial1553 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1549 ⟨19, by decide⟩ (some 3)

private def cache1554 : Cache :=
  step cache1542 ⟨18, by decide⟩ 3
private def partial1554 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1542 ⟨18, by decide⟩ (some 3)

private def cache1555 : Cache :=
  step cache1540 ⟨17, by decide⟩ 2
private def partial1555 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1540 ⟨17, by decide⟩ (some 2)

private def cache1556 : Cache :=
  step cache1555 ⟨18, by decide⟩ 0
private def partial1556 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1555 ⟨18, by decide⟩ (some 0)

private def cache1557 : Cache :=
  step cache1556 ⟨19, by decide⟩ 0
private def partial1557 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1556 ⟨19, by decide⟩ (some 0)

private def cache1558 : Cache :=
  step cache1556 ⟨19, by decide⟩ 1
private def partial1558 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1556 ⟨19, by decide⟩ (some 1)

private def cache1559 : Cache :=
  step cache1556 ⟨19, by decide⟩ 2
private def partial1559 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1556 ⟨19, by decide⟩ (some 2)

private def cache1560 : Cache :=
  step cache1556 ⟨19, by decide⟩ 3
private def partial1560 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1556 ⟨19, by decide⟩ (some 3)

private def cache1561 : Cache :=
  step cache1555 ⟨18, by decide⟩ 1
private def partial1561 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1555 ⟨18, by decide⟩ (some 1)

private def cache1562 : Cache :=
  step cache1561 ⟨19, by decide⟩ 0
private def partial1562 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1561 ⟨19, by decide⟩ (some 0)

private def cache1563 : Cache :=
  step cache1561 ⟨19, by decide⟩ 1
private def partial1563 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1561 ⟨19, by decide⟩ (some 1)

private def cache1564 : Cache :=
  step cache1561 ⟨19, by decide⟩ 2
private def partial1564 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1561 ⟨19, by decide⟩ (some 2)

private def cache1565 : Cache :=
  step cache1561 ⟨19, by decide⟩ 3
private def partial1565 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1561 ⟨19, by decide⟩ (some 3)

private def cache1566 : Cache :=
  step cache1555 ⟨18, by decide⟩ 2
private def partial1566 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1555 ⟨18, by decide⟩ (some 2)

private def cache1567 : Cache :=
  step cache1566 ⟨19, by decide⟩ 0
private def partial1567 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1566 ⟨19, by decide⟩ (some 0)

private def cache1568 : Cache :=
  step cache1566 ⟨19, by decide⟩ 1
private def partial1568 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1566 ⟨19, by decide⟩ (some 1)

private def cache1569 : Cache :=
  step cache1566 ⟨19, by decide⟩ 2
private def partial1569 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1566 ⟨19, by decide⟩ (some 2)

private def cache1570 : Cache :=
  step cache1566 ⟨19, by decide⟩ 3
private def partial1570 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1566 ⟨19, by decide⟩ (some 3)

private def cache1571 : Cache :=
  step cache1555 ⟨18, by decide⟩ 3
private def partial1571 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1555 ⟨18, by decide⟩ (some 3)

private def cache1572 : Cache :=
  step cache1571 ⟨19, by decide⟩ 0
private def partial1572 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1571 ⟨19, by decide⟩ (some 0)

private def cache1573 : Cache :=
  step cache1571 ⟨19, by decide⟩ 1
private def partial1573 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1571 ⟨19, by decide⟩ (some 1)

private def cache1574 : Cache :=
  step cache1571 ⟨19, by decide⟩ 2
private def partial1574 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1571 ⟨19, by decide⟩ (some 2)

private def cache1575 : Cache :=
  step cache1571 ⟨19, by decide⟩ 3
private def partial1575 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1571 ⟨19, by decide⟩ (some 3)

private def cache1576 : Cache :=
  step cache1540 ⟨17, by decide⟩ 3
private def partial1576 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1540 ⟨17, by decide⟩ (some 3)

private def cache1577 : Cache :=
  step cache1576 ⟨18, by decide⟩ 0
private def partial1577 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1576 ⟨18, by decide⟩ (some 0)

private def cache1578 : Cache :=
  step cache1577 ⟨19, by decide⟩ 0
private def partial1578 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1577 ⟨19, by decide⟩ (some 0)

private def cache1579 : Cache :=
  step cache1577 ⟨19, by decide⟩ 1
private def partial1579 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1577 ⟨19, by decide⟩ (some 1)

private def cache1580 : Cache :=
  step cache1577 ⟨19, by decide⟩ 2
private def partial1580 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1577 ⟨19, by decide⟩ (some 2)

private def cache1581 : Cache :=
  step cache1577 ⟨19, by decide⟩ 3
private def partial1581 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1577 ⟨19, by decide⟩ (some 3)

private def cache1582 : Cache :=
  step cache1576 ⟨18, by decide⟩ 1
private def partial1582 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1576 ⟨18, by decide⟩ (some 1)

private def cache1583 : Cache :=
  step cache1582 ⟨19, by decide⟩ 0
private def partial1583 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1582 ⟨19, by decide⟩ (some 0)

private def cache1584 : Cache :=
  step cache1582 ⟨19, by decide⟩ 1
private def partial1584 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1582 ⟨19, by decide⟩ (some 1)

private def cache1585 : Cache :=
  step cache1582 ⟨19, by decide⟩ 2
private def partial1585 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1582 ⟨19, by decide⟩ (some 2)

private def cache1586 : Cache :=
  step cache1582 ⟨19, by decide⟩ 3
private def partial1586 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1582 ⟨19, by decide⟩ (some 3)

private def cache1587 : Cache :=
  step cache1576 ⟨18, by decide⟩ 2
private def partial1587 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1576 ⟨18, by decide⟩ (some 2)

private def cache1588 : Cache :=
  step cache1587 ⟨19, by decide⟩ 0
private def partial1588 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1587 ⟨19, by decide⟩ (some 0)

private def cache1589 : Cache :=
  step cache1587 ⟨19, by decide⟩ 1
private def partial1589 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1587 ⟨19, by decide⟩ (some 1)

private def cache1590 : Cache :=
  step cache1587 ⟨19, by decide⟩ 2
private def partial1590 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1587 ⟨19, by decide⟩ (some 2)

private def cache1591 : Cache :=
  step cache1587 ⟨19, by decide⟩ 3
private def partial1591 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1587 ⟨19, by decide⟩ (some 3)

private def cache1592 : Cache :=
  step cache1576 ⟨18, by decide⟩ 3
private def partial1592 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1576 ⟨18, by decide⟩ (some 3)

private def cache1593 : Cache :=
  step cache1592 ⟨19, by decide⟩ 0
private def partial1593 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1592 ⟨19, by decide⟩ (some 0)

private def cache1594 : Cache :=
  step cache1592 ⟨19, by decide⟩ 1
private def partial1594 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1592 ⟨19, by decide⟩ (some 1)

private def cache1595 : Cache :=
  step cache1592 ⟨19, by decide⟩ 2
private def partial1595 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1592 ⟨19, by decide⟩ (some 2)

private def cache1596 : Cache :=
  step cache1592 ⟨19, by decide⟩ 3
private def partial1596 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1592 ⟨19, by decide⟩ (some 3)

private theorem receipt1596 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1596, by decide⟩ cache1596 partial1596 = true := by
  decide +kernel

private theorem receipt1595 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1595, by decide⟩ cache1595 partial1595 = true := by
  decide +kernel

private theorem receipt1594 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1594, by decide⟩ cache1594 partial1594 = true := by
  decide +kernel

private theorem receipt1593 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1593, by decide⟩ cache1593 partial1593 = true := by
  decide +kernel

private theorem receipt1592 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1592, by decide⟩ cache1592 partial1592 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1593,1594,1595,1596])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3510497633945395 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1593
  · exact receipt1594
  · exact receipt1595
  · exact receipt1596

private theorem receipt1591 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1591, by decide⟩ cache1591 partial1591 = true := by
  decide +kernel

private theorem receipt1590 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1590, by decide⟩ cache1590 partial1590 = true := by
  decide +kernel

private theorem receipt1589 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1589, by decide⟩ cache1589 partial1589 = true := by
  decide +kernel

private theorem receipt1588 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1588, by decide⟩ cache1588 partial1588 = true := by
  decide +kernel

private theorem receipt1587 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1587, by decide⟩ cache1587 partial1587 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1588,1589,1590,1591])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3499499832657555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1588
  · exact receipt1589
  · exact receipt1590
  · exact receipt1591

private theorem receipt1586 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1586, by decide⟩ cache1586 partial1586 = true := by
  decide +kernel

private theorem receipt1585 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1585, by decide⟩ cache1585 partial1585 = true := by
  decide +kernel

private theorem receipt1584 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1584, by decide⟩ cache1584 partial1584 = true := by
  decide +kernel

private theorem receipt1583 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1583, by decide⟩ cache1583 partial1583 = true := by
  decide +kernel

private theorem receipt1582 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1582, by decide⟩ cache1582 partial1582 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1583,1584,1585,1586])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3488502031369715 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1583
  · exact receipt1584
  · exact receipt1585
  · exact receipt1586

private theorem receipt1581 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1581, by decide⟩ cache1581 partial1581 = true := by
  decide +kernel

private theorem receipt1580 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1580, by decide⟩ cache1580 partial1580 = true := by
  decide +kernel

private theorem receipt1579 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1579, by decide⟩ cache1579 partial1579 = true := by
  decide +kernel

private theorem receipt1578 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1578, by decide⟩ cache1578 partial1578 = true := by
  decide +kernel

private theorem receipt1577 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1577, by decide⟩ cache1577 partial1577 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1578,1579,1580,1581])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3477504230081875 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1578
  · exact receipt1579
  · exact receipt1580
  · exact receipt1581

private theorem receipt1576 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1576, by decide⟩ cache1576 partial1576 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1577,1582,1587,1592])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3501697244382514 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1577
  · exact receipt1582
  · exact receipt1587
  · exact receipt1592

private theorem receipt1575 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1575, by decide⟩ cache1575 partial1575 = true := by
  decide +kernel

private theorem receipt1574 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1574, by decide⟩ cache1574 partial1574 = true := by
  decide +kernel

private theorem receipt1573 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1573, by decide⟩ cache1573 partial1573 = true := by
  decide +kernel

private theorem receipt1572 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1572, by decide⟩ cache1572 partial1572 = true := by
  decide +kernel

private theorem receipt1571 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1571, by decide⟩ cache1571 partial1571 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1572,1573,1574,1575])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3464306868536467 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1572
  · exact receipt1573
  · exact receipt1574
  · exact receipt1575

private theorem receipt1570 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1570, by decide⟩ cache1570 partial1570 = true := by
  decide +kernel

private theorem receipt1569 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1569, by decide⟩ cache1569 partial1569 = true := by
  decide +kernel

private theorem receipt1568 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1568, by decide⟩ cache1568 partial1568 = true := by
  decide +kernel

private theorem receipt1567 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1567, by decide⟩ cache1567 partial1567 = true := by
  decide +kernel

private theorem receipt1566 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1566, by decide⟩ cache1566 partial1566 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1567,1568,1569,1570])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3453309067248627 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1567
  · exact receipt1568
  · exact receipt1569
  · exact receipt1570

private theorem receipt1565 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1565, by decide⟩ cache1565 partial1565 = true := by
  decide +kernel

private theorem receipt1564 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1564, by decide⟩ cache1564 partial1564 = true := by
  decide +kernel

private theorem receipt1563 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1563, by decide⟩ cache1563 partial1563 = true := by
  decide +kernel

private theorem receipt1562 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1562, by decide⟩ cache1562 partial1562 = true := by
  decide +kernel

private theorem receipt1561 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1561, by decide⟩ cache1561 partial1561 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1562,1563,1564,1565])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3442311265960787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1562
  · exact receipt1563
  · exact receipt1564
  · exact receipt1565

private theorem receipt1560 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1560, by decide⟩ cache1560 partial1560 = true := by
  decide +kernel

private theorem receipt1559 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1559, by decide⟩ cache1559 partial1559 = true := by
  decide +kernel

private theorem receipt1558 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1558, by decide⟩ cache1558 partial1558 = true := by
  decide +kernel

private theorem receipt1557 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1557, by decide⟩ cache1557 partial1557 = true := by
  decide +kernel

private theorem receipt1556 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1556, by decide⟩ cache1556 partial1556 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1557,1558,1559,1560])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3431313464672947 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1557
  · exact receipt1558
  · exact receipt1559
  · exact receipt1560

private theorem receipt1555 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1555, by decide⟩ cache1555 partial1555 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1556,1561,1566,1571])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3455506478973586 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1556
  · exact receipt1561
  · exact receipt1566
  · exact receipt1571

private theorem receipt1554 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1554, by decide⟩ cache1554 partial1554 = true := by
  decide +kernel

private theorem receipt1553 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1553, by decide⟩ cache1553 partial1553 = true := by
  decide +kernel

private theorem receipt1552 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1552, by decide⟩ cache1552 partial1552 = true := by
  decide +kernel

private theorem receipt1551 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1551, by decide⟩ cache1551 partial1551 = true := by
  decide +kernel

private theorem receipt1550 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1550, by decide⟩ cache1550 partial1550 = true := by
  decide +kernel

private theorem receipt1549 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1549, by decide⟩ cache1549 partial1549 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1550,1551,1552,1553])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3415916542869971 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1550
  · exact receipt1551
  · exact receipt1552
  · exact receipt1553

private theorem receipt1548 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1548, by decide⟩ cache1548 partial1548 = true := by
  decide +kernel

private theorem receipt1547 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1547, by decide⟩ cache1547 partial1547 = true := by
  decide +kernel

private theorem receipt1546 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1546, by decide⟩ cache1546 partial1546 = true := by
  decide +kernel

private theorem receipt1545 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1545, by decide⟩ cache1545 partial1545 = true := by
  decide +kernel

private theorem receipt1544 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1544, by decide⟩ cache1544 partial1544 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1545,1546,1547,1548])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3404918741582131 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1545
  · exact receipt1546
  · exact receipt1547
  · exact receipt1548

private theorem receipt1543 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1543, by decide⟩ cache1543 partial1543 = true := by
  decide +kernel

private theorem receipt1542 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1542, by decide⟩ cache1542 partial1542 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1543,1544,1549,1554])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3418113954595058 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1543
  · exact receipt1544
  · exact receipt1549
  · exact receipt1554

private theorem receipt1541 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1541, by decide⟩ cache1541 partial1541 = true := by
  decide +kernel

theorem receipt1540 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1540, by decide⟩ cache1540 partial1540 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1541,1542,1555,1576])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3466495687180465 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1541
  · exact receipt1542
  · exact receipt1555
  · exact receipt1576


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock10
