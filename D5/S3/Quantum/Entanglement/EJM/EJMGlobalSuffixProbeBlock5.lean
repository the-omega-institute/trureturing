/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock5
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock5
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
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

private def cache1516 : Cache :=
  step cache1515 ⟨17, by decide⟩ 0
private def partial1516 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1515 ⟨17, by decide⟩ (some 0)

private def cache1517 : Cache :=
  step cache1515 ⟨17, by decide⟩ 1
private def partial1517 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1515 ⟨17, by decide⟩ (some 1)

private def cache1518 : Cache :=
  step cache1515 ⟨17, by decide⟩ 2
private def partial1518 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1515 ⟨17, by decide⟩ (some 2)

private def cache1519 : Cache :=
  step cache1515 ⟨17, by decide⟩ 3
private def partial1519 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1515 ⟨17, by decide⟩ (some 3)

private def cache1520 : Cache :=
  step cache1519 ⟨18, by decide⟩ 0
private def partial1520 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1519 ⟨18, by decide⟩ (some 0)

private def cache1521 : Cache :=
  step cache1520 ⟨19, by decide⟩ 0
private def partial1521 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1520 ⟨19, by decide⟩ (some 0)

private def cache1522 : Cache :=
  step cache1520 ⟨19, by decide⟩ 1
private def partial1522 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1520 ⟨19, by decide⟩ (some 1)

private def cache1523 : Cache :=
  step cache1520 ⟨19, by decide⟩ 2
private def partial1523 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1520 ⟨19, by decide⟩ (some 2)

private def cache1524 : Cache :=
  step cache1520 ⟨19, by decide⟩ 3
private def partial1524 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1520 ⟨19, by decide⟩ (some 3)

private def cache1525 : Cache :=
  step cache1519 ⟨18, by decide⟩ 1
private def partial1525 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1519 ⟨18, by decide⟩ (some 1)

private def cache1526 : Cache :=
  step cache1525 ⟨19, by decide⟩ 0
private def partial1526 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1525 ⟨19, by decide⟩ (some 0)

private def cache1527 : Cache :=
  step cache1525 ⟨19, by decide⟩ 1
private def partial1527 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1525 ⟨19, by decide⟩ (some 1)

private def cache1528 : Cache :=
  step cache1525 ⟨19, by decide⟩ 2
private def partial1528 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1525 ⟨19, by decide⟩ (some 2)

private def cache1529 : Cache :=
  step cache1525 ⟨19, by decide⟩ 3
private def partial1529 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1525 ⟨19, by decide⟩ (some 3)

private def cache1530 : Cache :=
  step cache1519 ⟨18, by decide⟩ 2
private def partial1530 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1519 ⟨18, by decide⟩ (some 2)

private def cache1531 : Cache :=
  step cache1530 ⟨19, by decide⟩ 0
private def partial1531 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1530 ⟨19, by decide⟩ (some 0)

private def cache1532 : Cache :=
  step cache1530 ⟨19, by decide⟩ 1
private def partial1532 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1530 ⟨19, by decide⟩ (some 1)

private def cache1533 : Cache :=
  step cache1530 ⟨19, by decide⟩ 2
private def partial1533 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1530 ⟨19, by decide⟩ (some 2)

private def cache1534 : Cache :=
  step cache1530 ⟨19, by decide⟩ 3
private def partial1534 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1530 ⟨19, by decide⟩ (some 3)

private def cache1535 : Cache :=
  step cache1519 ⟨18, by decide⟩ 3
private def partial1535 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1519 ⟨18, by decide⟩ (some 3)

private def cache1536 : Cache :=
  step cache1535 ⟨19, by decide⟩ 0
private def partial1536 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1535 ⟨19, by decide⟩ (some 0)

private def cache1537 : Cache :=
  step cache1535 ⟨19, by decide⟩ 1
private def partial1537 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1535 ⟨19, by decide⟩ (some 1)

private def cache1538 : Cache :=
  step cache1535 ⟨19, by decide⟩ 2
private def partial1538 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1535 ⟨19, by decide⟩ (some 2)

private def cache1539 : Cache :=
  step cache1535 ⟨19, by decide⟩ 3
private def partial1539 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1535 ⟨19, by decide⟩ (some 3)

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

private def cache1598 : Cache :=
  step cache1597 ⟨15, by decide⟩ 0
private def partial1598 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1597 ⟨15, by decide⟩ (some 0)

private def cache1599 : Cache :=
  step cache1597 ⟨15, by decide⟩ 1
private def partial1599 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1597 ⟨15, by decide⟩ (some 1)

private def cache1600 : Cache :=
  step cache1597 ⟨15, by decide⟩ 2
private def partial1600 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1597 ⟨15, by decide⟩ (some 2)

private def cache1601 : Cache :=
  step cache1597 ⟨15, by decide⟩ 3
private def partial1601 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1597 ⟨15, by decide⟩ (some 3)

private def cache1602 : Cache :=
  step cache1601 ⟨16, by decide⟩ 0
private def partial1602 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1601 ⟨16, by decide⟩ (some 0)

private def cache1603 : Cache :=
  step cache1601 ⟨16, by decide⟩ 1
private def partial1603 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1601 ⟨16, by decide⟩ (some 1)

private def cache1604 : Cache :=
  step cache1601 ⟨16, by decide⟩ 2
private def partial1604 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1601 ⟨16, by decide⟩ (some 2)

private def cache1605 : Cache :=
  step cache1604 ⟨17, by decide⟩ 0
private def partial1605 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1604 ⟨17, by decide⟩ (some 0)

private def cache1606 : Cache :=
  step cache1604 ⟨17, by decide⟩ 1
private def partial1606 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1604 ⟨17, by decide⟩ (some 1)

private def cache1607 : Cache :=
  step cache1604 ⟨17, by decide⟩ 2
private def partial1607 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1604 ⟨17, by decide⟩ (some 2)

private def cache1608 : Cache :=
  step cache1604 ⟨17, by decide⟩ 3
private def partial1608 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1604 ⟨17, by decide⟩ (some 3)

private def cache1609 : Cache :=
  step cache1608 ⟨18, by decide⟩ 0
private def partial1609 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1608 ⟨18, by decide⟩ (some 0)

private def cache1610 : Cache :=
  step cache1608 ⟨18, by decide⟩ 1
private def partial1610 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1608 ⟨18, by decide⟩ (some 1)

private def cache1611 : Cache :=
  step cache1610 ⟨19, by decide⟩ 0
private def partial1611 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1610 ⟨19, by decide⟩ (some 0)

private def cache1612 : Cache :=
  step cache1610 ⟨19, by decide⟩ 1
private def partial1612 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1610 ⟨19, by decide⟩ (some 1)

private def cache1613 : Cache :=
  step cache1610 ⟨19, by decide⟩ 2
private def partial1613 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1610 ⟨19, by decide⟩ (some 2)

private def cache1614 : Cache :=
  step cache1610 ⟨19, by decide⟩ 3
private def partial1614 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1610 ⟨19, by decide⟩ (some 3)

private def cache1615 : Cache :=
  step cache1608 ⟨18, by decide⟩ 2
private def partial1615 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1608 ⟨18, by decide⟩ (some 2)

private def cache1616 : Cache :=
  step cache1615 ⟨19, by decide⟩ 0
private def partial1616 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1615 ⟨19, by decide⟩ (some 0)

private def cache1617 : Cache :=
  step cache1615 ⟨19, by decide⟩ 1
private def partial1617 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1615 ⟨19, by decide⟩ (some 1)

private def cache1618 : Cache :=
  step cache1615 ⟨19, by decide⟩ 2
private def partial1618 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1615 ⟨19, by decide⟩ (some 2)

private def cache1619 : Cache :=
  step cache1615 ⟨19, by decide⟩ 3
private def partial1619 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1615 ⟨19, by decide⟩ (some 3)

private def cache1620 : Cache :=
  step cache1608 ⟨18, by decide⟩ 3
private def partial1620 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1608 ⟨18, by decide⟩ (some 3)

private def cache1621 : Cache :=
  step cache1620 ⟨19, by decide⟩ 0
private def partial1621 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1620 ⟨19, by decide⟩ (some 0)

private def cache1622 : Cache :=
  step cache1620 ⟨19, by decide⟩ 1
private def partial1622 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1620 ⟨19, by decide⟩ (some 1)

private def cache1623 : Cache :=
  step cache1620 ⟨19, by decide⟩ 2
private def partial1623 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1620 ⟨19, by decide⟩ (some 2)

private def cache1624 : Cache :=
  step cache1620 ⟨19, by decide⟩ 3
private def partial1624 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1620 ⟨19, by decide⟩ (some 3)

private def cache1625 : Cache :=
  step cache1601 ⟨16, by decide⟩ 3
private def partial1625 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1601 ⟨16, by decide⟩ (some 3)

private def cache1626 : Cache :=
  step cache1625 ⟨17, by decide⟩ 0
private def partial1626 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1625 ⟨17, by decide⟩ (some 0)

private def cache1627 : Cache :=
  step cache1625 ⟨17, by decide⟩ 1
private def partial1627 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1625 ⟨17, by decide⟩ (some 1)

private def cache1628 : Cache :=
  step cache1627 ⟨18, by decide⟩ 0
private def partial1628 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1627 ⟨18, by decide⟩ (some 0)

private def cache1629 : Cache :=
  step cache1627 ⟨18, by decide⟩ 1
private def partial1629 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1627 ⟨18, by decide⟩ (some 1)

private def cache1630 : Cache :=
  step cache1629 ⟨19, by decide⟩ 0
private def partial1630 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1629 ⟨19, by decide⟩ (some 0)

private def cache1631 : Cache :=
  step cache1629 ⟨19, by decide⟩ 1
private def partial1631 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1629 ⟨19, by decide⟩ (some 1)

private def cache1632 : Cache :=
  step cache1629 ⟨19, by decide⟩ 2
private def partial1632 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1629 ⟨19, by decide⟩ (some 2)

private def cache1633 : Cache :=
  step cache1629 ⟨19, by decide⟩ 3
private def partial1633 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1629 ⟨19, by decide⟩ (some 3)

private def cache1634 : Cache :=
  step cache1627 ⟨18, by decide⟩ 2
private def partial1634 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1627 ⟨18, by decide⟩ (some 2)

private def cache1635 : Cache :=
  step cache1627 ⟨18, by decide⟩ 3
private def partial1635 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1627 ⟨18, by decide⟩ (some 3)

private def cache1636 : Cache :=
  step cache1625 ⟨17, by decide⟩ 2
private def partial1636 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1625 ⟨17, by decide⟩ (some 2)

private def cache1637 : Cache :=
  step cache1636 ⟨18, by decide⟩ 0
private def partial1637 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1636 ⟨18, by decide⟩ (some 0)

private def cache1638 : Cache :=
  step cache1637 ⟨19, by decide⟩ 0
private def partial1638 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1637 ⟨19, by decide⟩ (some 0)

private def cache1639 : Cache :=
  step cache1637 ⟨19, by decide⟩ 1
private def partial1639 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1637 ⟨19, by decide⟩ (some 1)

private def cache1640 : Cache :=
  step cache1637 ⟨19, by decide⟩ 2
private def partial1640 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1637 ⟨19, by decide⟩ (some 2)

private def cache1641 : Cache :=
  step cache1637 ⟨19, by decide⟩ 3
private def partial1641 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1637 ⟨19, by decide⟩ (some 3)

private def cache1642 : Cache :=
  step cache1636 ⟨18, by decide⟩ 1
private def partial1642 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1636 ⟨18, by decide⟩ (some 1)

private def cache1643 : Cache :=
  step cache1642 ⟨19, by decide⟩ 0
private def partial1643 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1642 ⟨19, by decide⟩ (some 0)

private def cache1644 : Cache :=
  step cache1642 ⟨19, by decide⟩ 1
private def partial1644 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1642 ⟨19, by decide⟩ (some 1)

private def cache1645 : Cache :=
  step cache1642 ⟨19, by decide⟩ 2
private def partial1645 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1642 ⟨19, by decide⟩ (some 2)

private def cache1646 : Cache :=
  step cache1642 ⟨19, by decide⟩ 3
private def partial1646 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1642 ⟨19, by decide⟩ (some 3)

private def cache1647 : Cache :=
  step cache1636 ⟨18, by decide⟩ 2
private def partial1647 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1636 ⟨18, by decide⟩ (some 2)

private def cache1648 : Cache :=
  step cache1636 ⟨18, by decide⟩ 3
private def partial1648 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1636 ⟨18, by decide⟩ (some 3)

private def cache1649 : Cache :=
  step cache1625 ⟨17, by decide⟩ 3
private def partial1649 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1625 ⟨17, by decide⟩ (some 3)

private def cache1650 : Cache :=
  step cache1649 ⟨18, by decide⟩ 0
private def partial1650 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1649 ⟨18, by decide⟩ (some 0)

private def cache1651 : Cache :=
  step cache1649 ⟨18, by decide⟩ 1
private def partial1651 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1649 ⟨18, by decide⟩ (some 1)

private def cache1652 : Cache :=
  step cache1651 ⟨19, by decide⟩ 0
private def partial1652 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1651 ⟨19, by decide⟩ (some 0)

private def cache1653 : Cache :=
  step cache1651 ⟨19, by decide⟩ 1
private def partial1653 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1651 ⟨19, by decide⟩ (some 1)

private def cache1654 : Cache :=
  step cache1651 ⟨19, by decide⟩ 2
private def partial1654 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1651 ⟨19, by decide⟩ (some 2)

private def cache1655 : Cache :=
  step cache1651 ⟨19, by decide⟩ 3
private def partial1655 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1651 ⟨19, by decide⟩ (some 3)

private def cache1656 : Cache :=
  step cache1649 ⟨18, by decide⟩ 2
private def partial1656 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1649 ⟨18, by decide⟩ (some 2)

private def cache1657 : Cache :=
  step cache1649 ⟨18, by decide⟩ 3
private def partial1657 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1649 ⟨18, by decide⟩ (some 3)

private theorem receipt1657 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1657, by decide⟩ cache1657 partial1657 = true := by
  decide +kernel

private theorem receipt1656 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1656, by decide⟩ cache1656 partial1656 = true := by
  decide +kernel

private theorem receipt1655 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1655, by decide⟩ cache1655 partial1655 = true := by
  decide +kernel

private theorem receipt1654 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1654, by decide⟩ cache1654 partial1654 = true := by
  decide +kernel

private theorem receipt1653 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1653, by decide⟩ cache1653 partial1653 = true := by
  decide +kernel

private theorem receipt1652 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1652, by decide⟩ cache1652 partial1652 = true := by
  decide +kernel

private theorem receipt1651 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1651, by decide⟩ cache1651 partial1651 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1652,1653,1654,1655])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3640271689141907 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1652
  · exact receipt1653
  · exact receipt1654
  · exact receipt1655

private theorem receipt1650 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1650, by decide⟩ cache1650 partial1650 = true := by
  decide +kernel

private theorem receipt1649 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1649, by decide⟩ cache1649 partial1649 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1650,1651,1656,1657])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3644670809132626 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1650
  · exact receipt1651
  · exact receipt1656
  · exact receipt1657

private theorem receipt1648 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1648, by decide⟩ cache1648 partial1648 = true := by
  decide +kernel

private theorem receipt1647 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1647, by decide⟩ cache1647 partial1647 = true := by
  decide +kernel

private theorem receipt1646 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1646, by decide⟩ cache1646 partial1646 = true := by
  decide +kernel

private theorem receipt1645 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1645, by decide⟩ cache1645 partial1645 = true := by
  decide +kernel

private theorem receipt1644 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1644, by decide⟩ cache1644 partial1644 = true := by
  decide +kernel

private theorem receipt1643 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1643, by decide⟩ cache1643 partial1643 = true := by
  decide +kernel

private theorem receipt1642 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1642, by decide⟩ cache1642 partial1642 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1643,1644,1645,1646])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3620475646823795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1643
  · exact receipt1644
  · exact receipt1645
  · exact receipt1646

private theorem receipt1641 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1641, by decide⟩ cache1641 partial1641 = true := by
  decide +kernel

private theorem receipt1640 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1640, by decide⟩ cache1640 partial1640 = true := by
  decide +kernel

private theorem receipt1639 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1639, by decide⟩ cache1639 partial1639 = true := by
  decide +kernel

private theorem receipt1638 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1638, by decide⟩ cache1638 partial1638 = true := by
  decide +kernel

private theorem receipt1637 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1637, by decide⟩ cache1637 partial1637 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1638,1639,1640,1641])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3609477845535955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1638
  · exact receipt1639
  · exact receipt1640
  · exact receipt1641

private theorem receipt1636 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1636, by decide⟩ cache1636 partial1636 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1637,1642,1647,1648])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3624874766814386 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1637
  · exact receipt1642
  · exact receipt1647
  · exact receipt1648

private theorem receipt1635 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1635, by decide⟩ cache1635 partial1635 = true := by
  decide +kernel

private theorem receipt1634 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1634, by decide⟩ cache1634 partial1634 = true := by
  decide +kernel

private theorem receipt1633 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1633, by decide⟩ cache1633 partial1633 = true := by
  decide +kernel

private theorem receipt1632 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1632, by decide⟩ cache1632 partial1632 = true := by
  decide +kernel

private theorem receipt1631 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1631, by decide⟩ cache1631 partial1631 = true := by
  decide +kernel

private theorem receipt1630 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1630, by decide⟩ cache1630 partial1630 = true := by
  decide +kernel

private theorem receipt1629 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1629, by decide⟩ cache1629 partial1629 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1630,1631,1632,1633])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3591881363475411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1630
  · exact receipt1631
  · exact receipt1632
  · exact receipt1633

private theorem receipt1628 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1628, by decide⟩ cache1628 partial1628 = true := by
  decide +kernel

private theorem receipt1627 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1627, by decide⟩ cache1627 partial1627 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1628,1629,1634,1635])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3596280483466130 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1628
  · exact receipt1629
  · exact receipt1634
  · exact receipt1635

private theorem receipt1626 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1626, by decide⟩ cache1626 partial1626 = true := by
  decide +kernel

private theorem receipt1625 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1625, by decide⟩ cache1625 partial1625 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1626,1627,1636,1649])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3627067882523473 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1626
  · exact receipt1627
  · exact receipt1636
  · exact receipt1649

private theorem receipt1624 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1624, by decide⟩ cache1624 partial1624 = true := by
  decide +kernel

private theorem receipt1623 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1623, by decide⟩ cache1623 partial1623 = true := by
  decide +kernel

private theorem receipt1622 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1622, by decide⟩ cache1622 partial1622 = true := by
  decide +kernel

private theorem receipt1621 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1621, by decide⟩ cache1621 partial1621 = true := by
  decide +kernel

private theorem receipt1620 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1620, by decide⟩ cache1620 partial1620 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1621,1622,1623,1624])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3572085321157299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1621
  · exact receipt1622
  · exact receipt1623
  · exact receipt1624

private theorem receipt1619 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1619, by decide⟩ cache1619 partial1619 = true := by
  decide +kernel

private theorem receipt1618 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1618, by decide⟩ cache1618 partial1618 = true := by
  decide +kernel

private theorem receipt1617 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1617, by decide⟩ cache1617 partial1617 = true := by
  decide +kernel

private theorem receipt1616 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1616, by decide⟩ cache1616 partial1616 = true := by
  decide +kernel

private theorem receipt1615 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1615, by decide⟩ cache1615 partial1615 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1616,1617,1618,1619])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3561087519869459 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1616
  · exact receipt1617
  · exact receipt1618
  · exact receipt1619

private theorem receipt1614 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1614, by decide⟩ cache1614 partial1614 = true := by
  decide +kernel

private theorem receipt1613 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1613, by decide⟩ cache1613 partial1613 = true := by
  decide +kernel

private theorem receipt1612 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1612, by decide⟩ cache1612 partial1612 = true := by
  decide +kernel

private theorem receipt1611 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1611, by decide⟩ cache1611 partial1611 = true := by
  decide +kernel

private theorem receipt1610 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1610, by decide⟩ cache1610 partial1610 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1611,1612,1613,1614])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3550089718581619 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1611
  · exact receipt1612
  · exact receipt1613
  · exact receipt1614

private theorem receipt1609 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1609, by decide⟩ cache1609 partial1609 = true := by
  decide +kernel

private theorem receipt1608 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1608, by decide⟩ cache1608 partial1608 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1609,1610,1615,1620])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3563284931594546 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1609
  · exact receipt1610
  · exact receipt1615
  · exact receipt1620

private theorem receipt1607 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1607, by decide⟩ cache1607 partial1607 = true := by
  decide +kernel

private theorem receipt1606 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1606, by decide⟩ cache1606 partial1606 = true := by
  decide +kernel

private theorem receipt1605 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1605, by decide⟩ cache1605 partial1605 = true := by
  decide +kernel

private theorem receipt1604 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1604, by decide⟩ cache1604 partial1604 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1605,1606,1607,1608])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3536892357036209 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1605
  · exact receipt1606
  · exact receipt1607
  · exact receipt1608

private theorem receipt1603 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1603, by decide⟩ cache1603 partial1603 = true := by
  decide +kernel

private theorem receipt1602 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1602, by decide⟩ cache1602 partial1602 = true := by
  decide +kernel

private theorem receipt1601 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1601, by decide⟩ cache1601 partial1601 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1602,1603,1604,1625])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3574274141374544 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1602
  · exact receipt1603
  · exact receipt1604
  · exact receipt1625

private theorem receipt1600 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1600, by decide⟩ cache1600 partial1600 = true := by
  decide +kernel

private theorem receipt1599 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1599, by decide⟩ cache1599 partial1599 = true := by
  decide +kernel

private theorem receipt1598 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1598, by decide⟩ cache1598 partial1598 = true := by
  decide +kernel

theorem receipt1597 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨1597, by decide⟩ cache1597 partial1597 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![1598,1599,1600,1601])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(3521495435233231 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1598
  · exact receipt1599
  · exact receipt1600
  · exact receipt1601

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

private theorem receipt1539 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1539, by decide⟩ cache1539 partial1539 = true := by
  decide +kernel

private theorem receipt1538 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1538, by decide⟩ cache1538 partial1538 = true := by
  decide +kernel

private theorem receipt1537 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1537, by decide⟩ cache1537 partial1537 = true := by
  decide +kernel

private theorem receipt1536 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1536, by decide⟩ cache1536 partial1536 = true := by
  decide +kernel

#print axioms receipt1536

private theorem receipt1535 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1535, by decide⟩ cache1535 partial1535 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1536,1537,1538,1539])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3385122699264019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1536
  · exact receipt1537
  · exact receipt1538
  · exact receipt1539

private theorem receipt1534 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1534, by decide⟩ cache1534 partial1534 = true := by
  decide +kernel

private theorem receipt1533 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1533, by decide⟩ cache1533 partial1533 = true := by
  decide +kernel

private theorem receipt1532 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1532, by decide⟩ cache1532 partial1532 = true := by
  decide +kernel

private theorem receipt1531 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1531, by decide⟩ cache1531 partial1531 = true := by
  decide +kernel

private theorem receipt1530 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1530, by decide⟩ cache1530 partial1530 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1531,1532,1533,1534])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3374124897976179 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1531
  · exact receipt1532
  · exact receipt1533
  · exact receipt1534

private theorem receipt1529 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1529, by decide⟩ cache1529 partial1529 = true := by
  decide +kernel

private theorem receipt1528 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1528, by decide⟩ cache1528 partial1528 = true := by
  decide +kernel

private theorem receipt1527 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1527, by decide⟩ cache1527 partial1527 = true := by
  decide +kernel

private theorem receipt1526 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1526, by decide⟩ cache1526 partial1526 = true := by
  decide +kernel

private theorem receipt1525 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1525, by decide⟩ cache1525 partial1525 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1526,1527,1528,1529])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3363127096688339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1526
  · exact receipt1527
  · exact receipt1528
  · exact receipt1529

private theorem receipt1524 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1524, by decide⟩ cache1524 partial1524 = true := by
  decide +kernel

private theorem receipt1523 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1523, by decide⟩ cache1523 partial1523 = true := by
  decide +kernel

private theorem receipt1522 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1522, by decide⟩ cache1522 partial1522 = true := by
  decide +kernel

private theorem receipt1521 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1521, by decide⟩ cache1521 partial1521 = true := by
  decide +kernel

private theorem receipt1520 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1520, by decide⟩ cache1520 partial1520 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1521,1522,1523,1524])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3352129295400499 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1521
  · exact receipt1522
  · exact receipt1523
  · exact receipt1524

private theorem receipt1519 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1519, by decide⟩ cache1519 partial1519 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1520,1525,1530,1535])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3376322309701138 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1520
  · exact receipt1525
  · exact receipt1530
  · exact receipt1535

private theorem receipt1518 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1518, by decide⟩ cache1518 partial1518 = true := by
  decide +kernel

private theorem receipt1517 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1517, by decide⟩ cache1517 partial1517 = true := by
  decide +kernel

private theorem receipt1516 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1516, by decide⟩ cache1516 partial1516 = true := by
  decide +kernel

theorem receipt1515 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1515, by decide⟩ cache1515 partial1515 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1516,1517,1518,1519])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3341131494112657 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1516
  · exact receipt1517
  · exact receipt1518
  · exact receipt1519

theorem receipt1514 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1514, by decide⟩ cache1514 partial1514 = true := by
  decide +kernel

theorem receipt1513 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1513, by decide⟩ cache1513 partial1513 = true := by
  decide +kernel

theorem receipt1511 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1511, by decide⟩ cache1511 partial1511 = true := by
  decide +kernel

theorem receipt1510 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1510, by decide⟩ cache1510 partial1510 = true := by
  decide +kernel

theorem receipt1509 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1509, by decide⟩ cache1509 partial1509 = true := by
  decide +kernel

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


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
