/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main03
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main03.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts00

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main03

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![2, 2, 2, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![3, 7, 3, 2, 1, 1, 1]

private def n1505 : MainTree := .leaf (mainGapLeaf ![2, 2, 2, 0, 0, 0, 0])
private def n1506 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 0, 0, 0])
private def n1504 : MainTree := .split 2 2 n1505 n1506
private def n1507 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 0, 0, 0])
private def n1503 : MainTree := .split 1 2 n1504 n1507
private def n1510 : MainTree := .leaf (mainFullLeaf ![3, 2, 2, 0, 0, 0, 0])
private def n1511 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 0, 0, 0])
private def n1509 : MainTree := .split 2 2 n1510 n1511
private def n1513 : MainTree := .leaf (mainGapLeaf ![3, 3, 2, 0, 0, 0, 0])
private def n1514 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 0, 0, 0])
private def n1512 : MainTree := .split 2 2 n1513 n1514
private def n1508 : MainTree := .split 1 2 n1509 n1512
private def n1502 : MainTree := .split 0 2 n1503 n1508
private def n1517 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 0, 0, 1])
private def n1518 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 0, 0, 1])
private def n1516 : MainTree := .split 1 2 n1517 n1518
private def n1520 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 0, 0, 1])
private def n1521 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 0, 0, 1])
private def n1519 : MainTree := .split 1 2 n1520 n1521
private def n1515 : MainTree := .split 0 2 n1516 n1519
private def n1501 : MainTree := .split 6 0 n1502 n1515
private def n1525 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 0, 1, 0])
private def n1526 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 0, 1, 0])
private def n1524 : MainTree := .split 1 2 n1525 n1526
private def n1529 : MainTree := .leaf (mainGapLeaf ![3, 2, 2, 0, 0, 1, 0])
private def n1530 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 0, 1, 0])
private def n1528 : MainTree := .split 2 2 n1529 n1530
private def n1531 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 0, 1, 0])
private def n1527 : MainTree := .split 1 2 n1528 n1531
private def n1523 : MainTree := .split 0 2 n1524 n1527
private def n1533 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 0, 1, 1])
private def n1534 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 0, 1, 1])
private def n1532 : MainTree := .split 0 2 n1533 n1534
private def n1522 : MainTree := .split 6 0 n1523 n1532
private def n1500 : MainTree := .split 5 0 n1501 n1522
private def n1540 : MainTree := .leaf (mainGapLeaf ![2, 2, 2, 0, 1, 0, 0])
private def n1541 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 1, 0, 0])
private def n1539 : MainTree := .split 2 2 n1540 n1541
private def n1542 : MainTree := .leaf (mainRankLeaf 1 ![2, 3, 3, 0, 1, 0, 0])
private def n1538 : MainTree := .split 1 2 n1539 n1542
private def n1545 : MainTree := .leaf (mainRankLeaf 2 ![3, 2, 2, 0, 1, 0, 0])
private def n1546 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 1, 0, 0])
private def n1544 : MainTree := .split 2 2 n1545 n1546
private def n1548 : MainTree := .leaf (mainGapLeaf ![3, 3, 2, 0, 1, 0, 0])
private def n1549 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 1, 0, 0])
private def n1547 : MainTree := .split 2 2 n1548 n1549
private def n1543 : MainTree := .split 1 2 n1544 n1547
private def n1537 : MainTree := .split 0 2 n1538 n1543
private def n1552 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 1, 0, 1])
private def n1553 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 1, 0, 1])
private def n1551 : MainTree := .split 1 2 n1552 n1553
private def n1555 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 1, 0, 1])
private def n1556 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 1, 0, 1])
private def n1554 : MainTree := .split 1 2 n1555 n1556
private def n1550 : MainTree := .split 0 2 n1551 n1554
private def n1536 : MainTree := .split 6 0 n1537 n1550
private def n1560 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 0, 1, 1, 0])
private def n1561 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 1, 1, 0])
private def n1559 : MainTree := .split 1 2 n1560 n1561
private def n1563 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 0, 1, 1, 0])
private def n1564 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 1, 1, 0])
private def n1562 : MainTree := .split 1 2 n1563 n1564
private def n1558 : MainTree := .split 0 2 n1559 n1562
private def n1566 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 0, 1, 1, 1])
private def n1567 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 0, 1, 1, 1])
private def n1565 : MainTree := .split 0 2 n1566 n1567
private def n1557 : MainTree := .split 6 0 n1558 n1565
private def n1535 : MainTree := .split 5 0 n1536 n1557
private def n1499 : MainTree := .split 4 0 n1500 n1535
private def n1573 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 0, 0, 0, 0])
private def n1574 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 0, 0, 0, 0])
private def n1572 : MainTree := .split 0 2 n1573 n1574
private def n1575 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 0, 0, 0])
private def n1571 : MainTree := .split 1 5 n1572 n1575
private def n1578 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 0, 0, 0, 1])
private def n1579 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 0, 0, 0, 1])
private def n1577 : MainTree := .split 0 2 n1578 n1579
private def n1580 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 0, 0, 1])
private def n1576 : MainTree := .split 1 5 n1577 n1580
private def n1570 : MainTree := .split 6 0 n1571 n1576
private def n1584 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 0, 0, 1, 0])
private def n1585 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 0, 0, 1, 0])
private def n1583 : MainTree := .split 0 2 n1584 n1585
private def n1586 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 0, 1, 0])
private def n1582 : MainTree := .split 1 5 n1583 n1586
private def n1587 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 0, 1, 1])
private def n1581 : MainTree := .split 6 0 n1582 n1587
private def n1569 : MainTree := .split 5 0 n1570 n1581
private def n1592 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 0, 1, 0, 0])
private def n1593 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 0, 1, 0, 0])
private def n1591 : MainTree := .split 0 2 n1592 n1593
private def n1594 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 1, 0, 0])
private def n1590 : MainTree := .split 1 5 n1591 n1594
private def n1596 : MainTree := .leaf (mainRankLeaf 1 ![3, 5, 3, 0, 1, 0, 1])
private def n1597 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 1, 0, 1])
private def n1595 : MainTree := .split 1 5 n1596 n1597
private def n1589 : MainTree := .split 6 0 n1590 n1595
private def n1601 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 0, 1, 1, 0])
private def n1602 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 0, 1, 1, 0])
private def n1600 : MainTree := .split 0 2 n1601 n1602
private def n1603 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 1, 1, 0])
private def n1599 : MainTree := .split 1 5 n1600 n1603
private def n1604 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 0, 1, 1, 1])
private def n1598 : MainTree := .split 6 0 n1599 n1604
private def n1588 : MainTree := .split 5 0 n1589 n1598
private def n1568 : MainTree := .split 4 0 n1569 n1588
private def n1498 : MainTree := .split 1 3 n1499 n1568
private def n1613 : MainTree := .leaf (mainRankLeaf 2 ![2, 2, 2, 1, 0, 0, 0])
private def n1614 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 1, 0, 0, 0])
private def n1612 : MainTree := .split 2 2 n1613 n1614
private def n1616 : MainTree := .leaf (mainGapLeaf ![2, 3, 2, 1, 0, 0, 0])
private def n1617 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 0, 0, 0])
private def n1615 : MainTree := .split 2 2 n1616 n1617
private def n1611 : MainTree := .split 1 2 n1612 n1615
private def n1620 : MainTree := .leaf (mainFullLeaf ![3, 2, 2, 1, 0, 0, 0])
private def n1621 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 0, 0, 0])
private def n1619 : MainTree := .split 2 2 n1620 n1621
private def n1623 : MainTree := .leaf (mainGapLeaf ![3, 3, 2, 1, 0, 0, 0])
private def n1624 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 0, 0, 0])
private def n1622 : MainTree := .split 2 2 n1623 n1624
private def n1618 : MainTree := .split 1 2 n1619 n1622
private def n1610 : MainTree := .split 0 2 n1611 n1618
private def n1627 : MainTree := .leaf (mainRankLeaf 1 ![2, 2, 3, 2, 0, 0, 0])
private def n1628 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 0, 0, 0])
private def n1626 : MainTree := .split 1 2 n1627 n1628
private def n1631 : MainTree := .leaf (mainGapLeaf ![3, 2, 2, 2, 0, 0, 0])
private def n1632 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 2, 0, 0, 0])
private def n1630 : MainTree := .split 2 2 n1631 n1632
private def n1633 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 0, 0, 0])
private def n1629 : MainTree := .split 1 2 n1630 n1633
private def n1625 : MainTree := .split 0 2 n1626 n1629
private def n1609 : MainTree := .split 3 1 n1610 n1625
private def n1637 : MainTree := .leaf (mainRankLeaf 1 ![2, 2, 3, 1, 0, 0, 1])
private def n1638 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 0, 0, 1])
private def n1636 : MainTree := .split 1 2 n1637 n1638
private def n1641 : MainTree := .leaf (mainGapLeaf ![3, 2, 2, 1, 0, 0, 1])
private def n1642 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 0, 0, 1])
private def n1640 : MainTree := .split 2 2 n1641 n1642
private def n1643 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 0, 0, 1])
private def n1639 : MainTree := .split 1 2 n1640 n1643
private def n1635 : MainTree := .split 0 2 n1636 n1639
private def n1645 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 0, 0, 1])
private def n1646 : MainTree := .leaf (mainRankLeaf 1 ![3, 3, 3, 2, 0, 0, 1])
private def n1644 : MainTree := .split 0 2 n1645 n1646
private def n1634 : MainTree := .split 3 1 n1635 n1644
private def n1608 : MainTree := .split 6 0 n1609 n1634
private def n1652 : MainTree := .leaf (mainGapLeaf ![2, 2, 2, 1, 0, 1, 0])
private def n1653 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 1, 0, 1, 0])
private def n1651 : MainTree := .split 2 2 n1652 n1653
private def n1654 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 0, 1, 0])
private def n1650 : MainTree := .split 1 2 n1651 n1654
private def n1657 : MainTree := .leaf (mainGapLeaf ![3, 2, 2, 1, 0, 1, 0])
private def n1658 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 0, 1, 0])
private def n1656 : MainTree := .split 2 2 n1657 n1658
private def n1660 : MainTree := .leaf (mainGapLeaf ![3, 3, 2, 1, 0, 1, 0])
private def n1661 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 0, 1, 0])
private def n1659 : MainTree := .split 2 2 n1660 n1661
private def n1655 : MainTree := .split 1 2 n1656 n1659
private def n1649 : MainTree := .split 0 2 n1650 n1655
private def n1664 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 2, 0, 1, 0])
private def n1665 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 0, 1, 0])
private def n1663 : MainTree := .split 1 2 n1664 n1665
private def n1667 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 2, 0, 1, 0])
private def n1668 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 0, 1, 0])
private def n1666 : MainTree := .split 1 2 n1667 n1668
private def n1662 : MainTree := .split 0 2 n1663 n1666
private def n1648 : MainTree := .split 3 1 n1649 n1662
private def n1671 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 0, 1, 1])
private def n1673 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 0, 1, 1])
private def n1674 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 0, 1, 1])
private def n1672 : MainTree := .split 1 2 n1673 n1674
private def n1670 : MainTree := .split 0 2 n1671 n1672
private def n1676 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 0, 1, 1])
private def n1677 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 0, 1, 1])
private def n1675 : MainTree := .split 0 2 n1676 n1677
private def n1669 : MainTree := .split 3 1 n1670 n1675
private def n1647 : MainTree := .split 6 0 n1648 n1669
private def n1607 : MainTree := .split 5 0 n1608 n1647
private def n1684 : MainTree := .leaf (mainGapLeaf ![2, 2, 2, 1, 1, 0, 0])
private def n1685 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 1, 1, 0, 0])
private def n1683 : MainTree := .split 2 2 n1684 n1685
private def n1686 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 1, 0, 0])
private def n1682 : MainTree := .split 1 2 n1683 n1686
private def n1689 : MainTree := .leaf (mainGapLeaf ![3, 2, 2, 1, 1, 0, 0])
private def n1690 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 1, 0, 0])
private def n1688 : MainTree := .split 2 2 n1689 n1690
private def n1691 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 1, 0, 0])
private def n1687 : MainTree := .split 1 2 n1688 n1691
private def n1681 : MainTree := .split 0 2 n1682 n1687
private def n1694 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 2, 1, 0, 0])
private def n1695 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 1, 0, 0])
private def n1693 : MainTree := .split 1 2 n1694 n1695
private def n1697 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 2, 1, 0, 0])
private def n1698 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 1, 0, 0])
private def n1696 : MainTree := .split 1 2 n1697 n1698
private def n1692 : MainTree := .split 0 2 n1693 n1696
private def n1680 : MainTree := .split 3 1 n1681 n1692
private def n1702 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 1, 1, 0, 1])
private def n1703 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 1, 0, 1])
private def n1701 : MainTree := .split 1 2 n1702 n1703
private def n1705 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 1, 0, 1])
private def n1706 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 1, 0, 1])
private def n1704 : MainTree := .split 1 2 n1705 n1706
private def n1700 : MainTree := .split 0 2 n1701 n1704
private def n1708 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 1, 0, 1])
private def n1709 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 1, 0, 1])
private def n1707 : MainTree := .split 0 2 n1708 n1709
private def n1699 : MainTree := .split 3 1 n1700 n1707
private def n1679 : MainTree := .split 6 0 n1680 n1699
private def n1714 : MainTree := .leaf (mainGapLeaf ![2, 2, 3, 1, 1, 1, 0])
private def n1715 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 1, 1, 0])
private def n1713 : MainTree := .split 1 2 n1714 n1715
private def n1717 : MainTree := .leaf (mainGapLeaf ![3, 2, 3, 1, 1, 1, 0])
private def n1718 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 1, 1, 0])
private def n1716 : MainTree := .split 1 2 n1717 n1718
private def n1712 : MainTree := .split 0 2 n1713 n1716
private def n1720 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 2, 1, 1, 0])
private def n1721 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 2, 1, 1, 0])
private def n1719 : MainTree := .split 0 2 n1720 n1721
private def n1711 : MainTree := .split 3 1 n1712 n1719
private def n1724 : MainTree := .leaf (mainGapLeaf ![2, 3, 3, 1, 1, 1, 1])
private def n1725 : MainTree := .leaf (mainGapLeaf ![3, 3, 3, 1, 1, 1, 1])
private def n1723 : MainTree := .split 0 2 n1724 n1725
private def n1726 : MainTree :=
  .leaf (.rankIndexed 1 1536 RankReadouts00.rankReadout1726)
private def n1722 : MainTree := .split 3 1 n1723 n1726
private def n1710 : MainTree := .split 6 0 n1711 n1722
private def n1678 : MainTree := .split 5 0 n1679 n1710
private def n1606 : MainTree := .split 4 0 n1607 n1678
private def n1733 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 0, 0, 0])
private def n1735 : MainTree := .leaf (mainGapLeaf ![3, 5, 2, 1, 0, 0, 0])
private def n1736 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 0, 0, 0])
private def n1734 : MainTree := .split 2 2 n1735 n1736
private def n1732 : MainTree := .split 0 2 n1733 n1734
private def n1738 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 2, 0, 0, 0])
private def n1739 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 0, 0, 0])
private def n1737 : MainTree := .split 0 2 n1738 n1739
private def n1731 : MainTree := .split 3 1 n1732 n1737
private def n1741 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 1, 0, 0, 0])
private def n1742 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 0, 0, 0])
private def n1740 : MainTree := .split 3 1 n1741 n1742
private def n1730 : MainTree := .split 1 5 n1731 n1740
private def n1746 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 0, 0, 1])
private def n1747 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 0, 0, 1])
private def n1745 : MainTree := .split 0 2 n1746 n1747
private def n1748 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 0, 0, 1])
private def n1744 : MainTree := .split 3 1 n1745 n1748
private def n1750 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 1, 0, 0, 1])
private def n1751 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 0, 0, 1])
private def n1749 : MainTree := .split 3 1 n1750 n1751
private def n1743 : MainTree := .split 1 5 n1744 n1749
private def n1729 : MainTree := .split 6 0 n1730 n1743
private def n1756 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 0, 1, 0])
private def n1757 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 0, 1, 0])
private def n1755 : MainTree := .split 0 2 n1756 n1757
private def n1758 : MainTree :=
  .leaf (.rankIndexed 1 576 RankReadouts00.rankReadout1758)
private def n1754 : MainTree := .split 3 1 n1755 n1758
private def n1760 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 1, 0, 1, 0])
private def n1761 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 0, 1, 0])
private def n1759 : MainTree := .split 3 1 n1760 n1761
private def n1753 : MainTree := .split 1 5 n1754 n1759
private def n1764 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 0, 1, 1])
private def n1765 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 0, 1, 1])
private def n1763 : MainTree := .split 3 1 n1764 n1765
private def n1766 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 0, 1, 1])
private def n1762 : MainTree := .split 1 5 n1763 n1766
private def n1752 : MainTree := .split 6 0 n1753 n1762
private def n1728 : MainTree := .split 5 0 n1729 n1752
private def n1772 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 1, 0, 0])
private def n1773 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 1, 0, 0])
private def n1771 : MainTree := .split 0 2 n1772 n1773
private def n1775 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 2, 1, 0, 0])
private def n1776 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 1, 0, 0])
private def n1774 : MainTree := .split 0 2 n1775 n1776
private def n1770 : MainTree := .split 3 1 n1771 n1774
private def n1778 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 1, 1, 0, 0])
private def n1779 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 1, 0, 0])
private def n1777 : MainTree := .split 3 1 n1778 n1779
private def n1769 : MainTree := .split 1 5 n1770 n1777
private def n1783 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 1, 0, 1])
private def n1784 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 1, 0, 1])
private def n1782 : MainTree := .split 0 2 n1783 n1784
private def n1785 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 1, 0, 1])
private def n1781 : MainTree := .split 3 1 n1782 n1785
private def n1786 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 1, 0, 1])
private def n1780 : MainTree := .split 1 5 n1781 n1786
private def n1768 : MainTree := .split 6 0 n1769 n1780
private def n1791 : MainTree := .leaf (mainGapLeaf ![2, 5, 3, 1, 1, 1, 0])
private def n1792 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 1, 1, 0])
private def n1790 : MainTree := .split 0 2 n1791 n1792
private def n1793 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 2, 1, 1, 0])
private def n1789 : MainTree := .split 3 1 n1790 n1793
private def n1794 : MainTree := .leaf (mainGapLeaf ![3, 7, 3, 2, 1, 1, 0])
private def n1788 : MainTree := .split 1 5 n1789 n1794
private def n1797 : MainTree := .leaf (mainGapLeaf ![3, 5, 3, 1, 1, 1, 1])
private def d1798 : List ℕ := [
    0x202410642b84881202420307202440684983000010782480024e00042580c06c00082a0018480060240000,
    0xa3186c40194e81802a200c0907802604812a401a0c84f86c801c3604820612700100d84842a86d8062540,
    0x3825972807c3c04e224c0c12d00700064a06c11384e425a3080487380090c225c5a00806c22a14b00c4250,
    0x2466e003406a37872449a0795482880281e024930206c0f000349c7e02c04e16f030449007a12800524a558,
    0x6dc0660315007211985446d02ba0243680a824548a7980691222784992bc0326000e072248c3015101242b0,
    0x5417500213644f00da4861880652742aa5b80140986da2b97884c80dc2684204895422ac1210223302430d0,
    0x2717400110940ca3d87844fa2640d95a82e84850886ca01e2a93624b80cc6d91500634fc2728400123206cc,
    0x2a501b4b44ea7f82540c91822d84f900e70831c4a80926606c914078201d4ec3612625701844833100502a6,
    0x25e4e95a26f830c18104c0823902a313073c00d4b20c60912525600407811f82615a473031a0846c63c8108,
    0x5a14a27b00813c46c355013a2904e61e84b10c52512d430a04a6180740f873a00b4a43197e85286c513c2c8,
    0x13903a6083484e525b0e86f472a49407e3090493c251812c7391b024e0c355c6e82d28a003c07238025d72c,
    0x1a07e207d54c3c128c2c25d002c1e44e33700b024d6f23062d14927a00710f412a2800074384a17e455a2c4,
    0x4d00e47264286f116830549107b51454a28a8582b412902a1e233824b6e455906e76803937c5080f249e729,
    0x28960275802936c1e10ac0e23f048e30319079c06d51212627c0f12b25c049d0a07e16e20362c160479037a,
    0x5116d21250262b133436a4c00aa2476780d46e115879a03506b50437927a84858872519c49b3286d42be549,
    0x587992102ae1232795bc74833209c0d26de3e02bd78c0336014cc50281026c0e14247235b019a2f048d546,
    0x672765018445ba01671032419909a6683a85456d12bb14875478a0254ca4f40de3690a926a42257818c48b,
    0x7892004c98420dd2695ac4212ec32263008c6ce5433d01102ad7520233664bc3314f28000d16dd15418a2e0,
    0x3652664f10db5745aa7002ea4878b831418905408a3982752ab7445b90154ba0ce7c80993dc6db5681524fe,
    0x4b97fc0cd5721862dc1513120526204fd27310084170c7420134ac0963216647f03da5306cd1447867511c8,
    0x3d92da8a85e80447851fc4fb38826570a73431e5a92e94aa6627b80893cc6cb10c14229801f4504ee3631f0,
    0x427836101fa3504ed2635a66fc5717321850863110513943ca52010a2a71344b67411b87fa0952560cb564,
    0x4b54eb0b87f92556fa30e18304e2d961c7a83920fc13273e00f44070931d4a97ec09366152c5628702cc141,
    0x2d65618a461a0767700413841f90fa4085a54a673131b1a87b47ea08552a6c755413e3c92941092ca5d81ec,
    0x3824d825f6900ec72e5a34306f917030d7b204d0833c651c39155229286013173d1b41ea4b33400c72536ec,
    0x6f63f82d549630b7a404b61907551a12e8282840f943c73b5c81b24a555e7e95296ea8a213d03e2c960c34c,
    0x3d07350c0f638128285043a59072d1a44a37e67b12283c52c655113b2915d460a76034a4e73741e90b40ea,
    0x6f572b16c1a22f849507f54e3c328e51985c12d5d202e1e633c1b13720b224f68055d6e92d31608a176c7a2,
    0x5167a121885a0f52b612b2815c443933a6480a47e56e655b3e82c576a79403b37e6094d434950a8180e942c,
    0x49f8d032c1a10a27e36703b054d28d2c360675c5d179202d4d21e50e63710b13f442a6f358016a307194493,
    0x54b28b1188592b575a02b36e4c41e30ae33967c8083f26e515c19279e06f76937d27e50984c0f358c5c2718,
    0x67a0d67d00a13e46e315a03746860550679137b2084d181484a0e558a7275b419e4292f416932a6385156d6,
    0x6034ce7591d036d8120ad26e0e342657c3f15b22f248f8c019105c79d2145133a012727d2b374c3365c14c2,
    0x6790d557a18e8882e415905a79b62821250527b5be84971458974a19d09e32966c3ac3e25386d52bf14c78e,
    0x4cd50384681126d7124253265b119b2f163466a7c03aa5473d46d311414a7560274583354f636b4c18040ab,
    0x5798bc18d63208e05939c2113d21122af5bd4be7493331c07cc80209d0d36df56c1563e12e28b05f078d204,
    0x7465bb0174487113257ca7f409b3de6695343a956a87814975578b1cc2024cb3584f50df26b5ae7044232ee,
    0x5326cf1463d129c1114547535e01ca3671f44bd4f35768017028ba15531618b0562e162439a2776a8104845,
    0x1f24bb7fe0cf7c93dd2de5698ac1535ec6227784ff38c20110284370e4105ad2ed4ae3236667bc6317f208d,
    0x467876141fe3541c938a2676985757365ab7012eb1788b93157ba05508b3ce52410e39929a8684527451bc,
    0x6fe5734001872dd3137ac05339662152213683010144470d7431ba4ad0976655667f13db5318748aa1455ea,
    0xfe38940c44270b59873531f1ac4ab7ee66352e7b92303cd87210d2ce1432995dc4516123524ef1f10bc7fd,
    0x7b60873955563cb29652186410b1355da1ee4b78e83441b90ba7fb2576885652db61e8a97745e97aa0451fd,
    0x73f5cc1b64413426507ed52d6ee5638a68712cd7720433866114dc1fb35169482040a5a74346fd7331741aa,
    0x3b855513f2952cb60e76434e5d94da1ed6920ee0b93fc4326fb17230f04f61d51e7a939322082c8620fd133,
    0x1eb0b63416843fa6ed2d71648a57a661b07777138582a2868540fb43e5944095ca4a78d81a97b57eb22c52b,
    0x3f47060d34d50e3834d981c6918520ed59272f1a64312fc1717b364022a3c751d5532935d68617621b5376,
    0xeb42e6f758416e3f92fa4978c87a521c51b85e12f82928543d33e5c91b364c6827d855f3ec6eb1628a376e,
    0x21a50d0f72835c685171c43b5918d41a564a0a67e76743b42293ea2c75d579660b4d676134b1d837581a0b5,
    0x8d216d32e1a32f963c6723b254f28f11c85d75e5d302f4601e733d37380c0b33f668158219689016176d7a3,
    0x3a421911a85b2b75c54c633b67e7d464980a0a56e715e3e946c76b5f879537f20c4d550b84e58e81971a42d,
    0x7198d132d7d20a33e667153c3b188046a60775d7931d420a4d38160e73f55b642b2f65818c416b19563a517,
    0x53a6d714e11945c75b1d236f4c50af67d57e8093f388c8c215d19305e79f62c2163a227f6b084d58d74e5c3,
    0x1c44c380667b0d77d13e588a2e68b415b5f446962a50720981584b71658b4185b519f2f532b66e7c43ae639,
    0x3e353987c8b214d5f278f2064cf35c1d181326f6a042757d5b32f36368c17c205d2153d61163a145a74d337,
    0x7575e41ce45935a4f780570657b8be18f8892e505b39e6292136ac8385bf44c71574b1c27ce09f66d3ad56e,
    0x1c17cd80356d1572e36268b177c5f12056aa10684741444a7133276357f666b5367c13ab2383d587a11514b,
    0x56b8ae5ee87977a1cd38e20335969c4125af7052ef17c8bd7be63308f39d3d329e86c1134565e21f64bf8f0,
    0x4556163565e11cb1f569a57740470317a8bb31705762552639b8346a986a1057471be4497cb6587f53df535,
    0x1bd1f30be7ff68c4022df8ad5ed7ae62377938d83210344670f59c4114af8e06677bd7f323453387614729d,
    0x68a5678758ab7765eb0474786151ff35538b82440e69959a7371ae1797bb2323cf52510f29b5de8694538ec,
    0x7ef52f3bc2318732cf5dd6134de3536968220bd4366ff1764017ad3972245238661378314458ea3461bb654,
    0x7b764422e3ba5572978657665db1ef8e93450bb3fe68989861f7757ab22282e0ff40d5ce4435998dc1ad652,
    0x8cc17364251f22182d8635cd1b73436867dc6516ef1668a74747733874dd69585659682140b4358da1751ab,
    0x8ca1657a721e82b2876b885543f5955cb64e8d97da22d3ee3b947260f76534f1dc4db81e6930ef3fd4332fe,
    0x7d93ed89216376f5fc47150f81d85371e5938d61a72fd6763b664122b5d74647631da3770b76855863fb894,
    0x8d57d664b0a76753b53eb88446e5fa79720e4d71d981b42f58516f2fb63e8c921d11e85f46233f64d80e683,
    0x5f920d6b284f58f41c71b8d332f63d67353e3b388211d75f1d646180d3f75838c61978913a621b6b45c771d,
    0x7d33e753d8b65f688146b1d520b8176a441a5b72f78c57c663b3a511b45e4c78f867f7d580b88e15f46d62e,
    0x5f562b6ae83a44e71741966f7c53af23c53b87e14f45d35e1d36a257f88d8c305f62d2173a383c6b174f1c6,
    0x86e83944d8f21c37cf65c56f87d8b377e5f320735d4166a16377c323a3d71175e645b8f41c580788b2e78b5,
    0x29f86d4575e31f78f140662777d8366ab10741544b8e465a7f753723987b5e51cf35b69e70717e8bf39f6ad,
    0x8e123587747a61735782669b40517b52783586b8ee1bf68e6598af5ef47c77b38f69d59e4138e217d7bf236,
    0x6462258678eb34765568b89a77747982540f59b8de1af3be2335df8ed0bf68d40389c7af22683344759d656,
    0x8961674756ba8575978db64522f3bb7671de3ff8ce89922382f6bc5cf8dd7de6533bd4764df697823437177,
    0x80f8935fd6b671f8d76773b78864651db5878958cb21f6b964f7db3ef5fe4731dd81f2ff8cd6434666877dd,
    0x6a541b7c723e45f8f988f62f83e6b341d53f8831d76a68c73a76b58fa7d788546f5fb20f41e63f11f4638fc,
    0x4078378e565b47e69f17f86f8f365d77f4178e623b5e78f56af83b44f65e23d87f35f6a383d8f61c78b75f7,
    0x6b78878fe5ff4678976bb1df8cf6bd7df47764789b6be8df3bf89d22765747b8278ef68f89e47d59f8e3237,
    0x8ff6bf89f47f8e765f8f723f83f6a78fb41f8fd]
private def a1798 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![3, 5, 3, 2, 1, 1, 1])
    4096 29 2304 d1798
private def n1798 : MainTree := .leaf (mainGapLeafOfDivisors ![3, 5, 3, 2, 1, 1, 1] a1798)
private def n1796 : MainTree := .split 3 1 n1797 n1798
private def d1799 : List ℕ := [
    0x203010643786081203020309603040686183c00010783080026600043180c0900008360018600060300000,
    0xa3d890401966818036200c0909c032060136401a0c867890801c4206020613300100d86043689180626c0,
    0x3831996807c48066230c0c139007000662090113866431a3c80489780090c231c7200809023616300c4310,
    0x30692003406a43896461a0796c83480281e03093c206c0f000361ca203806619303c461007a12800530a6d8,
    0x91c0660316809611986c491037a0244280a830560a9d806912233861937c0327800e096260c3c1690124370,
    0x6c19900214246700da60618806533436a73801409891a3799c86480dc3284e06096c236c1210223f03030d0,
    0x9800110940ca4989c467a3240d97283a860508824090a01e3694226380cc91915006367c332a800123e090c,
    0x1b63466aa383140c918239867900e9483dc6280927e09091409c201d66c4213226f01846033d0050366331,
    0x6697229383cc18104c08245036313097c00d6320c60913126e00409c11f83217249703da084906488108365,
    0x9f00814849036d013a3506661e86310c53113943ca04a7980740f897a00b6243d9a286a890513c38854031e,
    0x40866531b0e89342a096a61407e3c904948269812c9791b030e0c36dc928392ae003c07244031d96c721622,
    0x6cc48134c38275002c1e46634300b030d9323c63916129e00710f412a3400074f8621a246da38413903a788,
    0x9311683c561107b6946ca34aa9837412902a1e23f830b9246d906e9a803943c6880f284061e9691a0a2207d,
    0x1e10ac0e24b060e3c31909dc06d69212633c0f137274061d0a0a212589220363817849d043a6500e49664e8,
    0x42a6400aa3077f80d49211589da03506b68443933aa8870896519c61b3e85a091437e6c934978299802942c,
    0x3f2b4009c0d291e4a037d9cc03378164c682a5032c0e14e496373019a3b060d6c62486919121250263713f4,
    0x19909a7e84686c591137b1489949ca02564a6740de4290a932a4e26f818c60b0589d921036e12333973c988,
    0x7b008c24490e6c349011036d99202342663c3f1672a400d191d15418a3a0067558336681a8473a0169503e4,
    0x5408a24245833536b98473901563a0cea0809949c91b6e81528a067e9c9200649a820dd32972c4e13ac3e2,
    0x94c2b898201362c0963e17e4a3049a6b090d1449c65489911c84253266710db6f472a9403aa607af83d4189,
    0x62a7e29f808948c24190b10c14235801f51066e4231f0639a3c0cd6f218639c1513d20527a067d333100a81,
    0x48a6a010a3678581346369811b8a3a0953160cb6e449939aae87680449c51fc67b44832594a9743de7293a9,
    0x9493dd629a2c0937e16ac6e2ab038c1415440429c37901fa41066d32372693c2a86f19721850863d1051454,
    0x6d413e48935410938a5427581ec63566b0b8a3931527093a3ce18304e39979c9e8452ba00fc13297e00f500,
    0x1ea6334000c75b831392c3966e1ae479a0769b00414441f90fa8484c87256269713db1a89f4a2a0856aa907,
    0x3e38978c54140c44265831f8100ec2a496e7234f09391703cd9f204d08348669c4516d2352aa013197d1b4,
    0xb40ea9362a24b83956163cb9e404b79907569a12ea683440f94fc97b7481b26256dea292606a992aae213d,
    0x7368c0f6441844342a904fa71096d1a4623a265a89f12284853866d113b35175478a9a040a667b584341e9,
    0x1a23b861507f5706ce48334e250699a9c12d75202e1e63fc1b14320b230f8006dd929393160ae19ac9e203d,
    0x3417444f93fab487c80a4a2525c9266db4a83859aa9d403b43e78965440968a842a580e94ec9352a196b16c,
    0x6cd34d38378699c7519d202d6521e50e64310b14b44ea93370016a3c78b81946136969e1218a9a0f537612b,
    0x7fca484b292515c1929de06f5609a943d33e689a8c0f384170c74295861fb103ec1a15a40a2a237f025a470,
    0xa54a8a0e570a96773419e4e93b41693ea5a27b824c6959166cb34b118a993752d099a02b42e6441e30ae3f9,
    0x21424a69346012733d37398c3f6741b446427fa0d6a100a14a425992315a8a80375287856869d143b208651,
    0x5a146c4a26b891537f87014c9ce78364e5509991d042da520ad32e0e34e66fc4b17323b260fb0019105c9dd,
    0x42b641a440ab7f90d56fa18eac83a415955c05a9db7a821268533b73ea899542c070998ab4219d09e3e97ec,
    0x20464d683a86a5132d2889524e53e673119b3b17b47eaa0046a6c7bb849424991311414a9960275183f5676,
    0x8e24605945c21149211236f86073d63e9893f31c0b41a0ca4209d0d391f6ec1564a18a43a2af055a7709cd,
    0x9b49e7e96b44696ea8a2ab814954c9959cb1cc20264b4186750df5d032b72e9444e33ae2b06f9afc18d7b2,
    0x63d6736f6a41278942afa1553d618b0563a17a455945aba8337828104a852bc98673b0175089513e5a0aa34,
    0x102a8394e8502ba4d072d3ad62e3e37e69fc7b1a3208d6b224590f14649135c11151454a9937601ca4271f4,
    0x6a424310e45985c35aaa85129851bc1f263ba3e0cf5c0a0949d39e6e9aec1538a176c7a29b867fb7044c201,
    0x2686b1ab4aea14576a0469c77941fe5494141c944a3278182ac6f597672b9413ab178af93d59fa05508b48e,
    0x93e2aa6f34c018739d3d39ec0534567a1ba46a285a136a7010150494d2b99831ba62d0975887e56e6a3149b,
    0x7189753df8d01ac62ba2e7e36ae5b09f923048dab210d38e14354635975c51179241266fb601f10bca3d274,
    0x13575a1ee637b284041b95bc0baa3b3178082726e539b79eae99b47699ea045ba21fd0fe44984c4cc50294b,
    0x54504344679165c1fb41181484aa604ca7274f493d2a99731741aa9f60875784556d648b3566a1aa410b859,
    0x4f79d69e9e9453220ba1a6caa20fd13397f74c1b6501402b505ba7d0a2d2646ad92e6e3ae6ab138d2e89b2,
    0x9f5a2b22c2626ab4786d513f35538b78e9a454340e759b5c65a1ed8120ee2a60b94bc2714f293b1723cf8c0,
    0xb64018045b94ba92d397888164ae59e679b0775689b1445a6a346a940fb4fe8497144c974a627b181a95ac,
    0xa5c811a920ed7122a596f1a64f13bc1715745aa9f37c022a48725469d6d3353756aa12d89a2b5a1b54361eb,
    0xa9e12fa693454fd3fe749b4c1b37cc802a186dfbd04ac26192b162ae39ae8b003f53078d40d68e443846659,
    0x3878787559d678b6569a140b1d8b59435a5a0b50eb4ee9377042a316e4b98bc3ba617b085729e521c25269b,
    0xad01615649ad9e321a68d0f75e8845343746a9195c4fb2c8711b14b4a1a57ca0a6a277f425e5a94742294aa,
    0x3ee1a35a63b97bc5717f24726cfbc034f25111ca9d2d499e75302f5201e73fd433a4c0b34b68017028ba196,
    0x7feb49a147c9a4a0a525d92715e4a98ac52c5629ab7789d543f20c65568ba8e84370ea5929095a4edb1216d,
    0x1d420a653a560e75d84b57364eb3b6701b0416b8b91957ba24e697b8846421911aa9b3778682d27456463fb,
    0x462bb033f830a8d2c470d98e743b46959b113eda125a50a34a67f16bc25b4718748aaac052a78755499d9d3,
    0xbbc6ba24d91787214e11951c2d155299b1d242f6450af7fd6fea494b3280accb0215d19305e9df7ac216561,
    0x4a5aca3a6af415b55e8a97745297aa687b78209a55a8b28c9562c270b4d873519f3b53eb7eea045a346e7b9,
    0x28a4e72b46fd7333b37b6b01a0205dbba21549624b11646186451a98d3f78e81c4b45643a467fb0d75c8a11,
    0x9552c198b1c2b43a0e09f5907ed46d6ee4a38a66b9abc871af214d7729cf20664f55141c1d15d4a5332f820,
    0x54e9977641ce51941a677b685d2a4527c9462b26fbafe18fac93a555d05b45e7a9bac21382c862a7873f50c,
    0x9bc55b771b74baa20582a106a878542be4d428950a9533e78d87b5a367eb6b6a0146b238bb9495aba11514b,
    0x17cafd9fe7b308f58024745d49335eaac1135168617621f663fb301c15c4a0da4327a6ed1578a53a37a6af1,
    0x58c5c2a0b7d8a3549f26c6b56ebaee8a376eab92f09ba54db721cd44e20341981c5d18524d272f9453af2b1,
    0x761b641cb1f581a2ae6f7be84c427994317aafb3d78c80577a56a645b85eba9a74829aaa1052bd9871be509,
    0x9b9b7144da7210350694f85171c2bb4d18d462fb2058a7e75b49fda3323426a6b3ab614735d51579654b416,
    0x5b29fb23248f6a510f85d35b75eaa95132e0b2cb621bd1f30bea3f80c2765c14c239f890aed76d9ee7a3ba6,
    0x5be7d458980a6e7bd8269ab5aeb2ec9b676b0475387951ff41544b84ea644ce81971a2ad9778d21ae17957c,
    0x79365e413816b61a620bd2754f693f2ab1764c18c457a9ed457224ba56a3aa685b137a71505b2a406b541bb,
    0x9b59eb222ba3a6e0ff5f084d4cd74e503719b1c8d1b521ad7d2a2f2666af5b147c231ab338f8802ea54775d,
    0x1751ab5ae9f77c422e57947a6d7bc8357aa52dc9a675bb5e1efb294055bd0bb4be80927388c8c2ad879f56c,
    0x1b7403806b51a1c5bb7d1bd426592f88a166ae78b45342e956a9b344765d815a9684b716a614cb2984f5b1a,
    0x8b253278f9a540f1dcb5d65ba5e8130ef5e02a74bd4f33beb0c1735768c17c225669fb90221a6daa32da74d,
    0x4bb8bead4889b0a1659e721e5695eca6b347838a954ff2cc71574bb4e7ceb19a1a5adbd222d4ae26347987c,
    0x847a5da9329495e2ca713b161a73bd5757f65ab4767c1bc422b25587a7575242d99a31dab5b4370b7805706,
    0x573b8cbc221d25311ea9f86c2d65223ff8f0b4d7cda4e803a19bd14adad21635669af8b177c53168fb805ea,
    0xb15b4ba167cb0a75987f525f4754ab8aeac452e87977a9d720e6571d95dca5b2924ef70516f8bd3bb7beb09,
    0x876bc1ac211d2d555699f1d65215daa4d4b7284703b068bb197ad1565b8a466bb421b8345e986a74795d2c9,
    0x5cca15a4b282ace15f8ad52d7ae563779b7cbb220d832a8f2c670f4dc29195bb133ef8e05a77bd7f36be473,
    0xac152b2f8555b7a1d520ba5782428e5d94da7373b7b05a067bbbbe24fb8946511b51e8692d38ec647b387ff,
    0x8222b66ffbf0281acdb0305f7ad217463866bb1a7c8312c598f8ea1c6b475945caa134a76bd875af68ab776,
    0x55f7757abbae82eb79a7a28d50e9572c34d98dc5927efa0546f23cbbd6bbabe87314f51d55341eb6c1d35d6,
    0x41d5d58564d682128b2b58da7b7584a0323abbb49711786576651bb348e9b6a1c5a4727e5c9acb3a7898af5,
    0x9472b317eaff8cc58245fbad82daae863a7950db321c35c6a0f7dc5916efbe08a7abdaf32f49be773b76207,
    0xb75baba7682b1075f88552bf4d550bb2458e8d97daa3726e6b7239abb2f254f7651cf41b81eb695d3bec27d,
    0xb7344f81d85371e4d38d6b2217d5b69ff23658135faad5172e4763b661f7b315c5bea4c627b8948ca7a79bd,
    0xb65a6681b2afbe94c517b57e8c96a7b9885fa75aab2e2b2e1bf58d80e5c37d9bdc26d892aef76f53c2f19bb,
    0xbf80d2774c38c6adc8919ef226ba75f4a7350771d8d5b567d6b2158b5b5bda23526bab78842ee53a797417,
    0x5bf7d580b88ebd9ada2ed56e9b75395f284fa654cf29c71bb1e8d31af57d5b347ebcc23388275f2e1b2db63,
    0xb53a1e7d3bd626747d8b65368812eb65f8175e4a6329a4f71778c57c657bb94bca225aa72deb2b4078f8b55,
    0xa972ce717299b1b5af7c522f47b87ebc92dd9a71deb5f5e24bf88db0e8c3ad956db92223a6f83c5f174fb1d,
    0x77e533b821dda5f2965e13bfb0d5777c3bc6257b915262db8f4807a1dbd5ad688b1678b553556bb845ee83a,
    0x59a7f7477bc5ac687b5251db5de707bf88bfad5b0bb8e21f5ed86e8392cd8f2b4f7cf59ca1bbd34af87d8b3,
    0xb7e20f5dd4de2938e27bfb8dbc311f86d2d7523b3c8f1a4f286ad356777dbb6836b815eb29595f2cbb178e4,
    0x4dd5968e16bf877ac32fa5571d78265dbbf4285b07b8b467bb583586b8eeb3a5cea175998afac552f2fc77b,
    0x5cbbe489aaf77772f9b7b82528f4db8dea0723ebbf51f8edb6eb395cdbf2283acf89c7afb7dbb3a7e8332c7,
    0xbee27f8ce899baf82f5fca7b50f8dd7de593be223dabf2f641fb6d5d78232b7bf1586867a7db368eb1c7595,
    0x26f53e2f381fbed17f8cd583b9caaf2e6b335c77dd896be12f59bfb775fa8574d7b268db58523b767b35b6b,
    0xb992e3b2f8fc80fbddade89353d5f671f8d7b235b72378862e5b67beb4c78958cbb9aa775f9b2558f7dbbde,
    0x2df8f988fadb56f83e5f329db1f47fbcd8835e68c7addb962275f58fab577d7bdb8852ef53ba6729e57fbce,
    0x8e6bc75278f5bfaad7b855ef83b2cf59e87f1df5e3bfcb0fb9383d8f6a1fbd78b7537b865e529b7c7b95bcb,
    0x827bf58efb3b5cf89e2fdb7f4df8e3b3dbf6287bb78378e559bac72fe5dfbf9b8f86fb3e8f359d77fb83297,
    0x8febdf53fb9d2e78975fbb27bef8cfb9e5fd7dfbe32f7587b37be589b5fe8df23fb6fbf389da7f597be62fb,
    0xbff8ffb9f5ffbe789fbf72ffb3f8e7bfb59fbfd8f7b87bfe83f5e7b978fb29fbcf8fdadf5f7887b9b]
private def a1799 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![3, 7, 3, 2, 1, 1, 1])
    4096 29 3072 d1799
private def n1799 : MainTree := .leaf (mainGapLeafOfDivisors ![3, 7, 3, 2, 1, 1, 1] a1799)
private def n1795 : MainTree := .split 1 5 n1796 n1799
private def n1787 : MainTree := .split 6 0 n1788 n1795
private def n1767 : MainTree := .split 5 0 n1768 n1787
private def n1727 : MainTree := .split 4 0 n1728 n1767
private def n1605 : MainTree := .split 1 3 n1606 n1727
private def n1497 : MainTree := .split 3 0 n1498 n1605

private theorem c1500 : C ![2, 2, 2, 0, 0, 0, 0] ![3, 3, 3, 0, 0, 1, 1] n1500 := by
  decide +kernel

private theorem c1536 : C ![2, 2, 2, 0, 1, 0, 0] ![3, 3, 3, 0, 1, 0, 1] n1536 := by
  decide +kernel

private theorem c1557 : C ![2, 2, 2, 0, 1, 1, 0] ![3, 3, 3, 0, 1, 1, 1] n1557 := by
  decide +kernel

private theorem c1535 : C ![2, 2, 2, 0, 1, 0, 0] ![3, 3, 3, 0, 1, 1, 1] n1535 := by
  exact checkExponentBoxTree_join c1536 c1557 (by decide +kernel)

private theorem c1499 : C ![2, 2, 2, 0, 0, 0, 0] ![3, 3, 3, 0, 1, 1, 1] n1499 := by
  exact checkExponentBoxTree_join c1500 c1535 (by decide +kernel)

private theorem c1570 : C ![2, 4, 2, 0, 0, 0, 0] ![3, 7, 3, 0, 0, 0, 1] n1570 := by
  decide +kernel

private theorem c1581 : C ![2, 4, 2, 0, 0, 1, 0] ![3, 7, 3, 0, 0, 1, 1] n1581 := by
  decide +kernel

private theorem c1569 : C ![2, 4, 2, 0, 0, 0, 0] ![3, 7, 3, 0, 0, 1, 1] n1569 := by
  exact checkExponentBoxTree_join c1570 c1581 (by decide +kernel)

private theorem c1589 : C ![2, 4, 2, 0, 1, 0, 0] ![3, 7, 3, 0, 1, 0, 1] n1589 := by
  decide +kernel

private theorem c1599 : C ![2, 4, 2, 0, 1, 1, 0] ![3, 7, 3, 0, 1, 1, 0] n1599 := by
  decide +kernel

private theorem c1604 : C ![2, 4, 2, 0, 1, 1, 1] ![3, 7, 3, 0, 1, 1, 1] n1604 := by
  decide +kernel

private theorem c1598 : C ![2, 4, 2, 0, 1, 1, 0] ![3, 7, 3, 0, 1, 1, 1] n1598 := by
  exact checkExponentBoxTree_join c1599 c1604 (by decide +kernel)

private theorem c1588 : C ![2, 4, 2, 0, 1, 0, 0] ![3, 7, 3, 0, 1, 1, 1] n1588 := by
  exact checkExponentBoxTree_join c1589 c1598 (by decide +kernel)

private theorem c1568 : C ![2, 4, 2, 0, 0, 0, 0] ![3, 7, 3, 0, 1, 1, 1] n1568 := by
  exact checkExponentBoxTree_join c1569 c1588 (by decide +kernel)

private theorem c1498 : C ![2, 2, 2, 0, 0, 0, 0] ![3, 7, 3, 0, 1, 1, 1] n1498 := by
  exact checkExponentBoxTree_join c1499 c1568 (by decide +kernel)

private theorem c1609 : C ![2, 2, 2, 1, 0, 0, 0] ![3, 3, 3, 2, 0, 0, 0] n1609 := by
  decide +kernel

private theorem c1635 : C ![2, 2, 2, 1, 0, 0, 1] ![3, 3, 3, 1, 0, 0, 1] n1635 := by
  decide +kernel

private theorem c1644 : C ![2, 2, 2, 2, 0, 0, 1] ![3, 3, 3, 2, 0, 0, 1] n1644 := by
  decide +kernel

private theorem c1634 : C ![2, 2, 2, 1, 0, 0, 1] ![3, 3, 3, 2, 0, 0, 1] n1634 := by
  exact checkExponentBoxTree_join c1635 c1644 (by decide +kernel)

private theorem c1608 : C ![2, 2, 2, 1, 0, 0, 0] ![3, 3, 3, 2, 0, 0, 1] n1608 := by
  exact checkExponentBoxTree_join c1609 c1634 (by decide +kernel)

private theorem c1649 : C ![2, 2, 2, 1, 0, 1, 0] ![3, 3, 3, 1, 0, 1, 0] n1649 := by
  decide +kernel

private theorem c1662 : C ![2, 2, 2, 2, 0, 1, 0] ![3, 3, 3, 2, 0, 1, 0] n1662 := by
  decide +kernel

private theorem c1648 : C ![2, 2, 2, 1, 0, 1, 0] ![3, 3, 3, 2, 0, 1, 0] n1648 := by
  exact checkExponentBoxTree_join c1649 c1662 (by decide +kernel)

private theorem c1670 : C ![2, 2, 2, 1, 0, 1, 1] ![3, 3, 3, 1, 0, 1, 1] n1670 := by
  decide +kernel

private theorem c1675 : C ![2, 2, 2, 2, 0, 1, 1] ![3, 3, 3, 2, 0, 1, 1] n1675 := by
  decide +kernel

private theorem c1669 : C ![2, 2, 2, 1, 0, 1, 1] ![3, 3, 3, 2, 0, 1, 1] n1669 := by
  exact checkExponentBoxTree_join c1670 c1675 (by decide +kernel)

private theorem c1647 : C ![2, 2, 2, 1, 0, 1, 0] ![3, 3, 3, 2, 0, 1, 1] n1647 := by
  exact checkExponentBoxTree_join c1648 c1669 (by decide +kernel)

private theorem c1607 : C ![2, 2, 2, 1, 0, 0, 0] ![3, 3, 3, 2, 0, 1, 1] n1607 := by
  exact checkExponentBoxTree_join c1608 c1647 (by decide +kernel)

private theorem c1681 : C ![2, 2, 2, 1, 1, 0, 0] ![3, 3, 3, 1, 1, 0, 0] n1681 := by
  decide +kernel

private theorem c1692 : C ![2, 2, 2, 2, 1, 0, 0] ![3, 3, 3, 2, 1, 0, 0] n1692 := by
  decide +kernel

private theorem c1680 : C ![2, 2, 2, 1, 1, 0, 0] ![3, 3, 3, 2, 1, 0, 0] n1680 := by
  exact checkExponentBoxTree_join c1681 c1692 (by decide +kernel)

private theorem c1700 : C ![2, 2, 2, 1, 1, 0, 1] ![3, 3, 3, 1, 1, 0, 1] n1700 := by
  decide +kernel

private theorem c1707 : C ![2, 2, 2, 2, 1, 0, 1] ![3, 3, 3, 2, 1, 0, 1] n1707 := by
  decide +kernel

private theorem c1699 : C ![2, 2, 2, 1, 1, 0, 1] ![3, 3, 3, 2, 1, 0, 1] n1699 := by
  exact checkExponentBoxTree_join c1700 c1707 (by decide +kernel)

private theorem c1679 : C ![2, 2, 2, 1, 1, 0, 0] ![3, 3, 3, 2, 1, 0, 1] n1679 := by
  exact checkExponentBoxTree_join c1680 c1699 (by decide +kernel)

private theorem c1712 : C ![2, 2, 2, 1, 1, 1, 0] ![3, 3, 3, 1, 1, 1, 0] n1712 := by
  decide +kernel

private theorem c1719 : C ![2, 2, 2, 2, 1, 1, 0] ![3, 3, 3, 2, 1, 1, 0] n1719 := by
  decide +kernel

private theorem c1711 : C ![2, 2, 2, 1, 1, 1, 0] ![3, 3, 3, 2, 1, 1, 0] n1711 := by
  exact checkExponentBoxTree_join c1712 c1719 (by decide +kernel)

private theorem c1724 : C ![2, 2, 2, 1, 1, 1, 1] ![2, 3, 3, 1, 1, 1, 1] n1724 := by
  decide +kernel

private theorem c1725 : C ![3, 2, 2, 1, 1, 1, 1] ![3, 3, 3, 1, 1, 1, 1] n1725 := by
  decide +kernel

private theorem c1723 : C ![2, 2, 2, 1, 1, 1, 1] ![3, 3, 3, 1, 1, 1, 1] n1723 := by
  exact checkExponentBoxTree_join c1724 c1725 (by decide +kernel)

private theorem c1726 : C ![2, 2, 2, 2, 1, 1, 1] ![3, 3, 3, 2, 1, 1, 1] n1726 := by
  decide +kernel

private theorem c1722 : C ![2, 2, 2, 1, 1, 1, 1] ![3, 3, 3, 2, 1, 1, 1] n1722 := by
  exact checkExponentBoxTree_join c1723 c1726 (by decide +kernel)

private theorem c1710 : C ![2, 2, 2, 1, 1, 1, 0] ![3, 3, 3, 2, 1, 1, 1] n1710 := by
  exact checkExponentBoxTree_join c1711 c1722 (by decide +kernel)

private theorem c1678 : C ![2, 2, 2, 1, 1, 0, 0] ![3, 3, 3, 2, 1, 1, 1] n1678 := by
  exact checkExponentBoxTree_join c1679 c1710 (by decide +kernel)

private theorem c1606 : C ![2, 2, 2, 1, 0, 0, 0] ![3, 3, 3, 2, 1, 1, 1] n1606 := by
  exact checkExponentBoxTree_join c1607 c1678 (by decide +kernel)

private theorem c1730 : C ![2, 4, 2, 1, 0, 0, 0] ![3, 7, 3, 2, 0, 0, 0] n1730 := by
  decide +kernel

private theorem c1744 : C ![2, 4, 2, 1, 0, 0, 1] ![3, 5, 3, 2, 0, 0, 1] n1744 := by
  decide +kernel

private theorem c1749 : C ![2, 6, 2, 1, 0, 0, 1] ![3, 7, 3, 2, 0, 0, 1] n1749 := by
  decide +kernel

private theorem c1743 : C ![2, 4, 2, 1, 0, 0, 1] ![3, 7, 3, 2, 0, 0, 1] n1743 := by
  exact checkExponentBoxTree_join c1744 c1749 (by decide +kernel)

private theorem c1729 : C ![2, 4, 2, 1, 0, 0, 0] ![3, 7, 3, 2, 0, 0, 1] n1729 := by
  exact checkExponentBoxTree_join c1730 c1743 (by decide +kernel)

private theorem c1754 : C ![2, 4, 2, 1, 0, 1, 0] ![3, 5, 3, 2, 0, 1, 0] n1754 := by
  decide +kernel

private theorem c1759 : C ![2, 6, 2, 1, 0, 1, 0] ![3, 7, 3, 2, 0, 1, 0] n1759 := by
  decide +kernel

private theorem c1753 : C ![2, 4, 2, 1, 0, 1, 0] ![3, 7, 3, 2, 0, 1, 0] n1753 := by
  exact checkExponentBoxTree_join c1754 c1759 (by decide +kernel)

private theorem c1764 : C ![2, 4, 2, 1, 0, 1, 1] ![3, 5, 3, 1, 0, 1, 1] n1764 := by
  decide +kernel

private theorem c1765 : C ![2, 4, 2, 2, 0, 1, 1] ![3, 5, 3, 2, 0, 1, 1] n1765 := by
  decide +kernel

private theorem c1763 : C ![2, 4, 2, 1, 0, 1, 1] ![3, 5, 3, 2, 0, 1, 1] n1763 := by
  exact checkExponentBoxTree_join c1764 c1765 (by decide +kernel)

private theorem c1766 : C ![2, 6, 2, 1, 0, 1, 1] ![3, 7, 3, 2, 0, 1, 1] n1766 := by
  decide +kernel

private theorem c1762 : C ![2, 4, 2, 1, 0, 1, 1] ![3, 7, 3, 2, 0, 1, 1] n1762 := by
  exact checkExponentBoxTree_join c1763 c1766 (by decide +kernel)

private theorem c1752 : C ![2, 4, 2, 1, 0, 1, 0] ![3, 7, 3, 2, 0, 1, 1] n1752 := by
  exact checkExponentBoxTree_join c1753 c1762 (by decide +kernel)

private theorem c1728 : C ![2, 4, 2, 1, 0, 0, 0] ![3, 7, 3, 2, 0, 1, 1] n1728 := by
  exact checkExponentBoxTree_join c1729 c1752 (by decide +kernel)

private theorem c1770 : C ![2, 4, 2, 1, 1, 0, 0] ![3, 5, 3, 2, 1, 0, 0] n1770 := by
  decide +kernel

private theorem c1777 : C ![2, 6, 2, 1, 1, 0, 0] ![3, 7, 3, 2, 1, 0, 0] n1777 := by
  decide +kernel

private theorem c1769 : C ![2, 4, 2, 1, 1, 0, 0] ![3, 7, 3, 2, 1, 0, 0] n1769 := by
  exact checkExponentBoxTree_join c1770 c1777 (by decide +kernel)

private theorem c1782 : C ![2, 4, 2, 1, 1, 0, 1] ![3, 5, 3, 1, 1, 0, 1] n1782 := by
  decide +kernel

private theorem c1785 : C ![2, 4, 2, 2, 1, 0, 1] ![3, 5, 3, 2, 1, 0, 1] n1785 := by
  decide +kernel

private theorem c1781 : C ![2, 4, 2, 1, 1, 0, 1] ![3, 5, 3, 2, 1, 0, 1] n1781 := by
  exact checkExponentBoxTree_join c1782 c1785 (by decide +kernel)

private theorem c1786 : C ![2, 6, 2, 1, 1, 0, 1] ![3, 7, 3, 2, 1, 0, 1] n1786 := by
  decide +kernel

private theorem c1780 : C ![2, 4, 2, 1, 1, 0, 1] ![3, 7, 3, 2, 1, 0, 1] n1780 := by
  exact checkExponentBoxTree_join c1781 c1786 (by decide +kernel)

private theorem c1768 : C ![2, 4, 2, 1, 1, 0, 0] ![3, 7, 3, 2, 1, 0, 1] n1768 := by
  exact checkExponentBoxTree_join c1769 c1780 (by decide +kernel)

private theorem c1790 : C ![2, 4, 2, 1, 1, 1, 0] ![3, 5, 3, 1, 1, 1, 0] n1790 := by
  decide +kernel

private theorem c1793 : C ![2, 4, 2, 2, 1, 1, 0] ![3, 5, 3, 2, 1, 1, 0] n1793 := by
  decide +kernel

private theorem c1789 : C ![2, 4, 2, 1, 1, 1, 0] ![3, 5, 3, 2, 1, 1, 0] n1789 := by
  exact checkExponentBoxTree_join c1790 c1793 (by decide +kernel)

private theorem c1794 : C ![2, 6, 2, 1, 1, 1, 0] ![3, 7, 3, 2, 1, 1, 0] n1794 := by
  decide +kernel

private theorem c1788 : C ![2, 4, 2, 1, 1, 1, 0] ![3, 7, 3, 2, 1, 1, 0] n1788 := by
  exact checkExponentBoxTree_join c1789 c1794 (by decide +kernel)

private theorem c1797 : C ![2, 4, 2, 1, 1, 1, 1] ![3, 5, 3, 1, 1, 1, 1] n1797 := by
  decide +kernel

private theorem c1798 : C ![2, 4, 2, 2, 1, 1, 1] ![3, 5, 3, 2, 1, 1, 1] n1798 := by
  decide +kernel

private theorem c1796 : C ![2, 4, 2, 1, 1, 1, 1] ![3, 5, 3, 2, 1, 1, 1] n1796 := by
  exact checkExponentBoxTree_join c1797 c1798 (by decide +kernel)

private theorem c1799 : C ![2, 6, 2, 1, 1, 1, 1] ![3, 7, 3, 2, 1, 1, 1] n1799 := by
  decide +kernel

private theorem c1795 : C ![2, 4, 2, 1, 1, 1, 1] ![3, 7, 3, 2, 1, 1, 1] n1795 := by
  exact checkExponentBoxTree_join c1796 c1799 (by decide +kernel)

private theorem c1787 : C ![2, 4, 2, 1, 1, 1, 0] ![3, 7, 3, 2, 1, 1, 1] n1787 := by
  exact checkExponentBoxTree_join c1788 c1795 (by decide +kernel)

private theorem c1767 : C ![2, 4, 2, 1, 1, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1767 := by
  exact checkExponentBoxTree_join c1768 c1787 (by decide +kernel)

private theorem c1727 : C ![2, 4, 2, 1, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1727 := by
  exact checkExponentBoxTree_join c1728 c1767 (by decide +kernel)

private theorem c1605 : C ![2, 2, 2, 1, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1605 := by
  exact checkExponentBoxTree_join c1606 c1727 (by decide +kernel)

private theorem c1497 : C ![2, 2, 2, 0, 0, 0, 0] ![3, 7, 3, 2, 1, 1, 1] n1497 := by
  exact checkExponentBoxTree_join c1498 c1605 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n1497

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c1497

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main03
