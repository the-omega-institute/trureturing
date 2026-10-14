/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock7
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock7
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1683 : Cache :=
  step cache1682 ⟨17, by decide⟩ 0
private def partial1683 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1682 ⟨17, by decide⟩ (some 0)

private def cache1684 : Cache :=
  step cache1682 ⟨17, by decide⟩ 1
private def partial1684 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1682 ⟨17, by decide⟩ (some 1)

private def cache1685 : Cache :=
  step cache1684 ⟨18, by decide⟩ 0
private def partial1685 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1684 ⟨18, by decide⟩ (some 0)

private def cache1686 : Cache :=
  step cache1684 ⟨18, by decide⟩ 1
private def partial1686 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1684 ⟨18, by decide⟩ (some 1)

private def cache1687 : Cache :=
  step cache1686 ⟨19, by decide⟩ 0
private def partial1687 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1686 ⟨19, by decide⟩ (some 0)

private def cache1688 : Cache :=
  step cache1686 ⟨19, by decide⟩ 1
private def partial1688 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1686 ⟨19, by decide⟩ (some 1)

private def cache1689 : Cache :=
  step cache1686 ⟨19, by decide⟩ 2
private def partial1689 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1686 ⟨19, by decide⟩ (some 2)

private def cache1690 : Cache :=
  step cache1686 ⟨19, by decide⟩ 3
private def partial1690 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1686 ⟨19, by decide⟩ (some 3)

private def cache1691 : Cache :=
  step cache1684 ⟨18, by decide⟩ 2
private def partial1691 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1684 ⟨18, by decide⟩ (some 2)

private def cache1692 : Cache :=
  step cache1691 ⟨19, by decide⟩ 0
private def partial1692 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1691 ⟨19, by decide⟩ (some 0)

private def cache1693 : Cache :=
  step cache1691 ⟨19, by decide⟩ 1
private def partial1693 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1691 ⟨19, by decide⟩ (some 1)

private def cache1694 : Cache :=
  step cache1691 ⟨19, by decide⟩ 2
private def partial1694 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1691 ⟨19, by decide⟩ (some 2)

private def cache1695 : Cache :=
  step cache1691 ⟨19, by decide⟩ 3
private def partial1695 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1691 ⟨19, by decide⟩ (some 3)

private def cache1696 : Cache :=
  step cache1684 ⟨18, by decide⟩ 3
private def partial1696 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1684 ⟨18, by decide⟩ (some 3)

private def cache1697 : Cache :=
  step cache1682 ⟨17, by decide⟩ 2
private def partial1697 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1682 ⟨17, by decide⟩ (some 2)

private def cache1698 : Cache :=
  step cache1697 ⟨18, by decide⟩ 0
private def partial1698 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1697 ⟨18, by decide⟩ (some 0)

private def cache1699 : Cache :=
  step cache1698 ⟨19, by decide⟩ 0
private def partial1699 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1698 ⟨19, by decide⟩ (some 0)

private def cache1700 : Cache :=
  step cache1698 ⟨19, by decide⟩ 1
private def partial1700 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1698 ⟨19, by decide⟩ (some 1)

private def cache1701 : Cache :=
  step cache1698 ⟨19, by decide⟩ 2
private def partial1701 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1698 ⟨19, by decide⟩ (some 2)

private def cache1702 : Cache :=
  step cache1698 ⟨19, by decide⟩ 3
private def partial1702 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1698 ⟨19, by decide⟩ (some 3)

private def cache1703 : Cache :=
  step cache1697 ⟨18, by decide⟩ 1
private def partial1703 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1697 ⟨18, by decide⟩ (some 1)

private def cache1704 : Cache :=
  step cache1703 ⟨19, by decide⟩ 0
private def partial1704 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1703 ⟨19, by decide⟩ (some 0)

private def cache1705 : Cache :=
  step cache1703 ⟨19, by decide⟩ 1
private def partial1705 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1703 ⟨19, by decide⟩ (some 1)

private def cache1706 : Cache :=
  step cache1703 ⟨19, by decide⟩ 2
private def partial1706 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1703 ⟨19, by decide⟩ (some 2)

private def cache1707 : Cache :=
  step cache1703 ⟨19, by decide⟩ 3
private def partial1707 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1703 ⟨19, by decide⟩ (some 3)

private def cache1708 : Cache :=
  step cache1697 ⟨18, by decide⟩ 2
private def partial1708 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1697 ⟨18, by decide⟩ (some 2)

private def cache1709 : Cache :=
  step cache1708 ⟨19, by decide⟩ 0
private def partial1709 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1708 ⟨19, by decide⟩ (some 0)

private def cache1710 : Cache :=
  step cache1708 ⟨19, by decide⟩ 1
private def partial1710 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1708 ⟨19, by decide⟩ (some 1)

private def cache1711 : Cache :=
  step cache1708 ⟨19, by decide⟩ 2
private def partial1711 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1708 ⟨19, by decide⟩ (some 2)

private def cache1712 : Cache :=
  step cache1708 ⟨19, by decide⟩ 3
private def partial1712 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1708 ⟨19, by decide⟩ (some 3)

private def cache1713 : Cache :=
  step cache1697 ⟨18, by decide⟩ 3
private def partial1713 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1697 ⟨18, by decide⟩ (some 3)

private def cache1714 : Cache :=
  step cache1713 ⟨19, by decide⟩ 0
private def partial1714 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1713 ⟨19, by decide⟩ (some 0)

private def cache1715 : Cache :=
  step cache1713 ⟨19, by decide⟩ 1
private def partial1715 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1713 ⟨19, by decide⟩ (some 1)

private def cache1716 : Cache :=
  step cache1713 ⟨19, by decide⟩ 2
private def partial1716 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1713 ⟨19, by decide⟩ (some 2)

private def cache1717 : Cache :=
  step cache1713 ⟨19, by decide⟩ 3
private def partial1717 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1713 ⟨19, by decide⟩ (some 3)

private def cache1718 : Cache :=
  step cache1682 ⟨17, by decide⟩ 3
private def partial1718 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1682 ⟨17, by decide⟩ (some 3)

private def cache1719 : Cache :=
  step cache1718 ⟨18, by decide⟩ 0
private def partial1719 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1718 ⟨18, by decide⟩ (some 0)

private def cache1720 : Cache :=
  step cache1719 ⟨19, by decide⟩ 0
private def partial1720 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1719 ⟨19, by decide⟩ (some 0)

private def cache1721 : Cache :=
  step cache1719 ⟨19, by decide⟩ 1
private def partial1721 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1719 ⟨19, by decide⟩ (some 1)

private def cache1722 : Cache :=
  step cache1719 ⟨19, by decide⟩ 2
private def partial1722 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1719 ⟨19, by decide⟩ (some 2)

private def cache1723 : Cache :=
  step cache1719 ⟨19, by decide⟩ 3
private def partial1723 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1719 ⟨19, by decide⟩ (some 3)

private def cache1724 : Cache :=
  step cache1718 ⟨18, by decide⟩ 1
private def partial1724 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1718 ⟨18, by decide⟩ (some 1)

private def cache1725 : Cache :=
  step cache1724 ⟨19, by decide⟩ 0
private def partial1725 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1724 ⟨19, by decide⟩ (some 0)

private def cache1726 : Cache :=
  step cache1724 ⟨19, by decide⟩ 1
private def partial1726 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1724 ⟨19, by decide⟩ (some 1)

private def cache1727 : Cache :=
  step cache1724 ⟨19, by decide⟩ 2
private def partial1727 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1724 ⟨19, by decide⟩ (some 2)

private def cache1728 : Cache :=
  step cache1724 ⟨19, by decide⟩ 3
private def partial1728 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1724 ⟨19, by decide⟩ (some 3)

private def cache1729 : Cache :=
  step cache1718 ⟨18, by decide⟩ 2
private def partial1729 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1718 ⟨18, by decide⟩ (some 2)

private def cache1730 : Cache :=
  step cache1729 ⟨19, by decide⟩ 0
private def partial1730 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1729 ⟨19, by decide⟩ (some 0)

private def cache1731 : Cache :=
  step cache1729 ⟨19, by decide⟩ 1
private def partial1731 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1729 ⟨19, by decide⟩ (some 1)

private def cache1732 : Cache :=
  step cache1729 ⟨19, by decide⟩ 2
private def partial1732 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1729 ⟨19, by decide⟩ (some 2)

private def cache1733 : Cache :=
  step cache1729 ⟨19, by decide⟩ 3
private def partial1733 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1729 ⟨19, by decide⟩ (some 3)

private def cache1734 : Cache :=
  step cache1718 ⟨18, by decide⟩ 3
private def partial1734 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1718 ⟨18, by decide⟩ (some 3)

private def cache1735 : Cache :=
  step cache1734 ⟨19, by decide⟩ 0
private def partial1735 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1734 ⟨19, by decide⟩ (some 0)

private def cache1736 : Cache :=
  step cache1734 ⟨19, by decide⟩ 1
private def partial1736 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1734 ⟨19, by decide⟩ (some 1)

private def cache1737 : Cache :=
  step cache1734 ⟨19, by decide⟩ 2
private def partial1737 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1734 ⟨19, by decide⟩ (some 2)

private def cache1738 : Cache :=
  step cache1734 ⟨19, by decide⟩ 3
private def partial1738 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1734 ⟨19, by decide⟩ (some 3)

private theorem receipt1738 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1738, by decide⟩ cache1738 partial1738 = true := by
  decide +kernel

private theorem receipt1737 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1737, by decide⟩ cache1737 partial1737 = true := by
  decide +kernel

private theorem receipt1736 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1736, by decide⟩ cache1736 partial1736 = true := by
  decide +kernel

private theorem receipt1735 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1735, by decide⟩ cache1735 partial1735 = true := by
  decide +kernel

private theorem receipt1734 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1734, by decide⟩ cache1734 partial1734 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1735,1736,1737,1738])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3822835190520051 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1735
  · exact receipt1736
  · exact receipt1737
  · exact receipt1738

private theorem receipt1733 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1733, by decide⟩ cache1733 partial1733 = true := by
  decide +kernel

private theorem receipt1732 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1732, by decide⟩ cache1732 partial1732 = true := by
  decide +kernel

private theorem receipt1731 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1731, by decide⟩ cache1731 partial1731 = true := by
  decide +kernel

private theorem receipt1730 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1730, by decide⟩ cache1730 partial1730 = true := by
  decide +kernel

private theorem receipt1729 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1729, by decide⟩ cache1729 partial1729 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1730,1731,1732,1733])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3811837389232211 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1730
  · exact receipt1731
  · exact receipt1732
  · exact receipt1733

private theorem receipt1728 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1728, by decide⟩ cache1728 partial1728 = true := by
  decide +kernel

private theorem receipt1727 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1727, by decide⟩ cache1727 partial1727 = true := by
  decide +kernel

private theorem receipt1726 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1726, by decide⟩ cache1726 partial1726 = true := by
  decide +kernel

private theorem receipt1725 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1725, by decide⟩ cache1725 partial1725 = true := by
  decide +kernel

private theorem receipt1724 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1724, by decide⟩ cache1724 partial1724 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1725,1726,1727,1728])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3800839587944371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1725
  · exact receipt1726
  · exact receipt1727
  · exact receipt1728

private theorem receipt1723 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1723, by decide⟩ cache1723 partial1723 = true := by
  decide +kernel

private theorem receipt1722 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1722, by decide⟩ cache1722 partial1722 = true := by
  decide +kernel

private theorem receipt1721 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1721, by decide⟩ cache1721 partial1721 = true := by
  decide +kernel

private theorem receipt1720 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1720, by decide⟩ cache1720 partial1720 = true := by
  decide +kernel

private theorem receipt1719 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1719, by decide⟩ cache1719 partial1719 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1720,1721,1722,1723])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3789841786656531 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1720
  · exact receipt1721
  · exact receipt1722
  · exact receipt1723

private theorem receipt1718 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1718, by decide⟩ cache1718 partial1718 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1719,1724,1729,1734])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3814034800957170 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1719
  · exact receipt1724
  · exact receipt1729
  · exact receipt1734

private theorem receipt1717 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1717, by decide⟩ cache1717 partial1717 = true := by
  decide +kernel

private theorem receipt1716 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1716, by decide⟩ cache1716 partial1716 = true := by
  decide +kernel

private theorem receipt1715 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1715, by decide⟩ cache1715 partial1715 = true := by
  decide +kernel

private theorem receipt1714 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1714, by decide⟩ cache1714 partial1714 = true := by
  decide +kernel

private theorem receipt1713 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1713, by decide⟩ cache1713 partial1713 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1714,1715,1716,1717])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3776644425111123 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1714
  · exact receipt1715
  · exact receipt1716
  · exact receipt1717

private theorem receipt1712 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1712, by decide⟩ cache1712 partial1712 = true := by
  decide +kernel

private theorem receipt1711 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1711, by decide⟩ cache1711 partial1711 = true := by
  decide +kernel

private theorem receipt1710 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1710, by decide⟩ cache1710 partial1710 = true := by
  decide +kernel

private theorem receipt1709 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1709, by decide⟩ cache1709 partial1709 = true := by
  decide +kernel

private theorem receipt1708 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1708, by decide⟩ cache1708 partial1708 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1709,1710,1711,1712])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3765646623823283 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1709
  · exact receipt1710
  · exact receipt1711
  · exact receipt1712

private theorem receipt1707 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1707, by decide⟩ cache1707 partial1707 = true := by
  decide +kernel

private theorem receipt1706 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1706, by decide⟩ cache1706 partial1706 = true := by
  decide +kernel

private theorem receipt1705 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1705, by decide⟩ cache1705 partial1705 = true := by
  decide +kernel

private theorem receipt1704 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1704, by decide⟩ cache1704 partial1704 = true := by
  decide +kernel

private theorem receipt1703 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1703, by decide⟩ cache1703 partial1703 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1704,1705,1706,1707])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3754648822535443 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1704
  · exact receipt1705
  · exact receipt1706
  · exact receipt1707

private theorem receipt1702 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1702, by decide⟩ cache1702 partial1702 = true := by
  decide +kernel

private theorem receipt1701 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1701, by decide⟩ cache1701 partial1701 = true := by
  decide +kernel

private theorem receipt1700 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1700, by decide⟩ cache1700 partial1700 = true := by
  decide +kernel

private theorem receipt1699 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1699, by decide⟩ cache1699 partial1699 = true := by
  decide +kernel

private theorem receipt1698 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1698, by decide⟩ cache1698 partial1698 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1699,1700,1701,1702])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3743651021247603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1699
  · exact receipt1700
  · exact receipt1701
  · exact receipt1702

private theorem receipt1697 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1697, by decide⟩ cache1697 partial1697 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1698,1703,1708,1713])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3767844035548242 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1698
  · exact receipt1703
  · exact receipt1708
  · exact receipt1713

private theorem receipt1696 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1696, by decide⟩ cache1696 partial1696 = true := by
  decide +kernel

private theorem receipt1695 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1695, by decide⟩ cache1695 partial1695 = true := by
  decide +kernel

private theorem receipt1694 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1694, by decide⟩ cache1694 partial1694 = true := by
  decide +kernel

private theorem receipt1693 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1693, by decide⟩ cache1693 partial1693 = true := by
  decide +kernel

private theorem receipt1692 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1692, by decide⟩ cache1692 partial1692 = true := by
  decide +kernel

private theorem receipt1691 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1691, by decide⟩ cache1691 partial1691 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1692,1693,1694,1695])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3728254099444627 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1692
  · exact receipt1693
  · exact receipt1694
  · exact receipt1695

private theorem receipt1690 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1690, by decide⟩ cache1690 partial1690 = true := by
  decide +kernel

private theorem receipt1689 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1689, by decide⟩ cache1689 partial1689 = true := by
  decide +kernel

private theorem receipt1688 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1688, by decide⟩ cache1688 partial1688 = true := by
  decide +kernel

private theorem receipt1687 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1687, by decide⟩ cache1687 partial1687 = true := by
  decide +kernel

private theorem receipt1686 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1686, by decide⟩ cache1686 partial1686 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1687,1688,1689,1690])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3717256298156787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1687
  · exact receipt1688
  · exact receipt1689
  · exact receipt1690

private theorem receipt1685 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1685, by decide⟩ cache1685 partial1685 = true := by
  decide +kernel

private theorem receipt1684 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1684, by decide⟩ cache1684 partial1684 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1685,1686,1691,1696])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3730451511169714 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1685
  · exact receipt1686
  · exact receipt1691
  · exact receipt1696

private theorem receipt1683 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1683, by decide⟩ cache1683 partial1683 = true := by
  decide +kernel

theorem receipt1682 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1682, by decide⟩ cache1682 partial1682 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1683,1684,1697,1718])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3778833243755121 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1683
  · exact receipt1684
  · exact receipt1697
  · exact receipt1718


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
