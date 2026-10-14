/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock8
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock8
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock8
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1666 : Cache :=
  step cache1665 ⟨17, by decide⟩ 0
private def partial1666 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1665 ⟨17, by decide⟩ (some 0)

private def cache1667 : Cache :=
  step cache1665 ⟨17, by decide⟩ 1
private def partial1667 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1665 ⟨17, by decide⟩ (some 1)

private def cache1668 : Cache :=
  step cache1665 ⟨17, by decide⟩ 2
private def partial1668 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1665 ⟨17, by decide⟩ (some 2)

private def cache1669 : Cache :=
  step cache1665 ⟨17, by decide⟩ 3
private def partial1669 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1665 ⟨17, by decide⟩ (some 3)

private def cache1670 : Cache :=
  step cache1669 ⟨18, by decide⟩ 0
private def partial1670 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1669 ⟨18, by decide⟩ (some 0)

private def cache1671 : Cache :=
  step cache1669 ⟨18, by decide⟩ 1
private def partial1671 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1669 ⟨18, by decide⟩ (some 1)

private def cache1672 : Cache :=
  step cache1669 ⟨18, by decide⟩ 2
private def partial1672 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1669 ⟨18, by decide⟩ (some 2)

private def cache1673 : Cache :=
  step cache1672 ⟨19, by decide⟩ 0
private def partial1673 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1672 ⟨19, by decide⟩ (some 0)

private def cache1674 : Cache :=
  step cache1672 ⟨19, by decide⟩ 1
private def partial1674 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1672 ⟨19, by decide⟩ (some 1)

private def cache1675 : Cache :=
  step cache1672 ⟨19, by decide⟩ 2
private def partial1675 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1672 ⟨19, by decide⟩ (some 2)

private def cache1676 : Cache :=
  step cache1672 ⟨19, by decide⟩ 3
private def partial1676 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1672 ⟨19, by decide⟩ (some 3)

private def cache1677 : Cache :=
  step cache1669 ⟨18, by decide⟩ 3
private def partial1677 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1669 ⟨18, by decide⟩ (some 3)

private def cache1678 : Cache :=
  step cache1677 ⟨19, by decide⟩ 0
private def partial1678 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1677 ⟨19, by decide⟩ (some 0)

private def cache1679 : Cache :=
  step cache1677 ⟨19, by decide⟩ 1
private def partial1679 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1677 ⟨19, by decide⟩ (some 1)

private def cache1680 : Cache :=
  step cache1677 ⟨19, by decide⟩ 2
private def partial1680 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1677 ⟨19, by decide⟩ (some 2)

private def cache1681 : Cache :=
  step cache1677 ⟨19, by decide⟩ 3
private def partial1681 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1677 ⟨19, by decide⟩ (some 3)

private theorem receipt1681 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1681, by decide⟩ cache1681 partial1681 = true := by
  decide +kernel

private theorem receipt1680 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1680, by decide⟩ cache1680 partial1680 = true := by
  decide +kernel

private theorem receipt1679 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1679, by decide⟩ cache1679 partial1679 = true := by
  decide +kernel

private theorem receipt1678 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1678, by decide⟩ cache1678 partial1678 = true := by
  decide +kernel

private theorem receipt1677 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1677, by decide⟩ cache1677 partial1677 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1678,1679,1680,1681])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3697460255838675 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1678
  · exact receipt1679
  · exact receipt1680
  · exact receipt1681

private theorem receipt1676 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1676, by decide⟩ cache1676 partial1676 = true := by
  decide +kernel

private theorem receipt1675 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1675, by decide⟩ cache1675 partial1675 = true := by
  decide +kernel

private theorem receipt1674 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1674, by decide⟩ cache1674 partial1674 = true := by
  decide +kernel

private theorem receipt1673 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1673, by decide⟩ cache1673 partial1673 = true := by
  decide +kernel

private theorem receipt1672 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1672, by decide⟩ cache1672 partial1672 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1673,1674,1675,1676])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3686462454550835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1673
  · exact receipt1674
  · exact receipt1675
  · exact receipt1676

private theorem receipt1671 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1671, by decide⟩ cache1671 partial1671 = true := by
  decide +kernel

private theorem receipt1670 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1670, by decide⟩ cache1670 partial1670 = true := by
  decide +kernel

private theorem receipt1669 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1669, by decide⟩ cache1669 partial1669 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1670,1671,1672,1677])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3688659866800338 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1670
  · exact receipt1671
  · exact receipt1672
  · exact receipt1677

private theorem receipt1668 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1668, by decide⟩ cache1668 partial1668 = true := by
  decide +kernel

private theorem receipt1667 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1667, by decide⟩ cache1667 partial1667 = true := by
  decide +kernel

private theorem receipt1666 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1666, by decide⟩ cache1666 partial1666 = true := by
  decide +kernel

theorem receipt1665 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1665, by decide⟩ cache1665 partial1665 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1666,1667,1668,1669])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3671065532747857 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1666
  · exact receipt1667
  · exact receipt1668
  · exact receipt1669

theorem receipt1664 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1664, by decide⟩ cache1664 partial1664 = true := by
  decide +kernel

theorem receipt1663 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1663, by decide⟩ cache1663 partial1663 = true := by
  decide +kernel

theorem receipt1661 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1661, by decide⟩ cache1661 partial1661 = true := by
  decide +kernel

theorem receipt1660 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1660, by decide⟩ cache1660 partial1660 = true := by
  decide +kernel

theorem receipt1659 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1659, by decide⟩ cache1659 partial1659 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock8
