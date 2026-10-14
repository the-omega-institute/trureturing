/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock29
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock29
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock29
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache745 : Cache :=
  step cache744 ⟨17, by decide⟩ 0
private def partial745 : Partial (Fin 20) (Fin 4) :=
  Function.update partial744 ⟨17, by decide⟩ (some 0)

private def cache746 : Cache :=
  step cache744 ⟨17, by decide⟩ 1
private def partial746 : Partial (Fin 20) (Fin 4) :=
  Function.update partial744 ⟨17, by decide⟩ (some 1)

private def cache747 : Cache :=
  step cache746 ⟨18, by decide⟩ 0
private def partial747 : Partial (Fin 20) (Fin 4) :=
  Function.update partial746 ⟨18, by decide⟩ (some 0)

private def cache748 : Cache :=
  step cache746 ⟨18, by decide⟩ 1
private def partial748 : Partial (Fin 20) (Fin 4) :=
  Function.update partial746 ⟨18, by decide⟩ (some 1)

private def cache749 : Cache :=
  step cache748 ⟨19, by decide⟩ 0
private def partial749 : Partial (Fin 20) (Fin 4) :=
  Function.update partial748 ⟨19, by decide⟩ (some 0)

private def cache750 : Cache :=
  step cache748 ⟨19, by decide⟩ 1
private def partial750 : Partial (Fin 20) (Fin 4) :=
  Function.update partial748 ⟨19, by decide⟩ (some 1)

private def cache751 : Cache :=
  step cache748 ⟨19, by decide⟩ 2
private def partial751 : Partial (Fin 20) (Fin 4) :=
  Function.update partial748 ⟨19, by decide⟩ (some 2)

private def cache752 : Cache :=
  step cache748 ⟨19, by decide⟩ 3
private def partial752 : Partial (Fin 20) (Fin 4) :=
  Function.update partial748 ⟨19, by decide⟩ (some 3)

private def cache753 : Cache :=
  step cache746 ⟨18, by decide⟩ 2
private def partial753 : Partial (Fin 20) (Fin 4) :=
  Function.update partial746 ⟨18, by decide⟩ (some 2)

private def cache754 : Cache :=
  step cache746 ⟨18, by decide⟩ 3
private def partial754 : Partial (Fin 20) (Fin 4) :=
  Function.update partial746 ⟨18, by decide⟩ (some 3)

private def cache755 : Cache :=
  step cache754 ⟨19, by decide⟩ 0
private def partial755 : Partial (Fin 20) (Fin 4) :=
  Function.update partial754 ⟨19, by decide⟩ (some 0)

private def cache756 : Cache :=
  step cache754 ⟨19, by decide⟩ 1
private def partial756 : Partial (Fin 20) (Fin 4) :=
  Function.update partial754 ⟨19, by decide⟩ (some 1)

private def cache757 : Cache :=
  step cache754 ⟨19, by decide⟩ 2
private def partial757 : Partial (Fin 20) (Fin 4) :=
  Function.update partial754 ⟨19, by decide⟩ (some 2)

private def cache758 : Cache :=
  step cache754 ⟨19, by decide⟩ 3
private def partial758 : Partial (Fin 20) (Fin 4) :=
  Function.update partial754 ⟨19, by decide⟩ (some 3)

private def cache759 : Cache :=
  step cache744 ⟨17, by decide⟩ 2
private def partial759 : Partial (Fin 20) (Fin 4) :=
  Function.update partial744 ⟨17, by decide⟩ (some 2)

private def cache760 : Cache :=
  step cache759 ⟨18, by decide⟩ 0
private def partial760 : Partial (Fin 20) (Fin 4) :=
  Function.update partial759 ⟨18, by decide⟩ (some 0)

private def cache761 : Cache :=
  step cache759 ⟨18, by decide⟩ 1
private def partial761 : Partial (Fin 20) (Fin 4) :=
  Function.update partial759 ⟨18, by decide⟩ (some 1)

private def cache762 : Cache :=
  step cache759 ⟨18, by decide⟩ 2
private def partial762 : Partial (Fin 20) (Fin 4) :=
  Function.update partial759 ⟨18, by decide⟩ (some 2)

private def cache763 : Cache :=
  step cache759 ⟨18, by decide⟩ 3
private def partial763 : Partial (Fin 20) (Fin 4) :=
  Function.update partial759 ⟨18, by decide⟩ (some 3)

private def cache764 : Cache :=
  step cache763 ⟨19, by decide⟩ 0
private def partial764 : Partial (Fin 20) (Fin 4) :=
  Function.update partial763 ⟨19, by decide⟩ (some 0)

private def cache765 : Cache :=
  step cache763 ⟨19, by decide⟩ 1
private def partial765 : Partial (Fin 20) (Fin 4) :=
  Function.update partial763 ⟨19, by decide⟩ (some 1)

private def cache766 : Cache :=
  step cache763 ⟨19, by decide⟩ 2
private def partial766 : Partial (Fin 20) (Fin 4) :=
  Function.update partial763 ⟨19, by decide⟩ (some 2)

private def cache767 : Cache :=
  step cache763 ⟨19, by decide⟩ 3
private def partial767 : Partial (Fin 20) (Fin 4) :=
  Function.update partial763 ⟨19, by decide⟩ (some 3)

private def cache768 : Cache :=
  step cache744 ⟨17, by decide⟩ 3
private def partial768 : Partial (Fin 20) (Fin 4) :=
  Function.update partial744 ⟨17, by decide⟩ (some 3)

private def cache769 : Cache :=
  step cache768 ⟨18, by decide⟩ 0
private def partial769 : Partial (Fin 20) (Fin 4) :=
  Function.update partial768 ⟨18, by decide⟩ (some 0)

private def cache770 : Cache :=
  step cache768 ⟨18, by decide⟩ 1
private def partial770 : Partial (Fin 20) (Fin 4) :=
  Function.update partial768 ⟨18, by decide⟩ (some 1)

private def cache771 : Cache :=
  step cache770 ⟨19, by decide⟩ 0
private def partial771 : Partial (Fin 20) (Fin 4) :=
  Function.update partial770 ⟨19, by decide⟩ (some 0)

private def cache772 : Cache :=
  step cache770 ⟨19, by decide⟩ 1
private def partial772 : Partial (Fin 20) (Fin 4) :=
  Function.update partial770 ⟨19, by decide⟩ (some 1)

private def cache773 : Cache :=
  step cache770 ⟨19, by decide⟩ 2
private def partial773 : Partial (Fin 20) (Fin 4) :=
  Function.update partial770 ⟨19, by decide⟩ (some 2)

private def cache774 : Cache :=
  step cache770 ⟨19, by decide⟩ 3
private def partial774 : Partial (Fin 20) (Fin 4) :=
  Function.update partial770 ⟨19, by decide⟩ (some 3)

private def cache775 : Cache :=
  step cache768 ⟨18, by decide⟩ 2
private def partial775 : Partial (Fin 20) (Fin 4) :=
  Function.update partial768 ⟨18, by decide⟩ (some 2)

private def cache776 : Cache :=
  step cache768 ⟨18, by decide⟩ 3
private def partial776 : Partial (Fin 20) (Fin 4) :=
  Function.update partial768 ⟨18, by decide⟩ (some 3)

private def cache777 : Cache :=
  step cache776 ⟨19, by decide⟩ 0
private def partial777 : Partial (Fin 20) (Fin 4) :=
  Function.update partial776 ⟨19, by decide⟩ (some 0)

private def cache778 : Cache :=
  step cache776 ⟨19, by decide⟩ 1
private def partial778 : Partial (Fin 20) (Fin 4) :=
  Function.update partial776 ⟨19, by decide⟩ (some 1)

private def cache779 : Cache :=
  step cache776 ⟨19, by decide⟩ 2
private def partial779 : Partial (Fin 20) (Fin 4) :=
  Function.update partial776 ⟨19, by decide⟩ (some 2)

private def cache780 : Cache :=
  step cache776 ⟨19, by decide⟩ 3
private def partial780 : Partial (Fin 20) (Fin 4) :=
  Function.update partial776 ⟨19, by decide⟩ (some 3)

private theorem receipt780 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨780, by decide⟩ cache780 partial780 = true := by
  decide +kernel

private theorem receipt779 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨779, by decide⟩ cache779 partial779 = true := by
  decide +kernel

private theorem receipt778 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨778, by decide⟩ cache778 partial778 = true := by
  decide +kernel

private theorem receipt777 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨777, by decide⟩ cache777 partial777 = true := by
  decide +kernel

private theorem receipt776 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨776, by decide⟩ cache776 partial776 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![777,778,779,780])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1715656463769907 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt777
  · exact receipt778
  · exact receipt779
  · exact receipt780

private theorem receipt775 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨775, by decide⟩ cache775 partial775 = true := by
  decide +kernel

private theorem receipt774 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨774, by decide⟩ cache774 partial774 = true := by
  decide +kernel

private theorem receipt773 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨773, by decide⟩ cache773 partial773 = true := by
  decide +kernel

private theorem receipt772 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨772, by decide⟩ cache772 partial772 = true := by
  decide +kernel

private theorem receipt771 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨771, by decide⟩ cache771 partial771 = true := by
  decide +kernel

private theorem receipt770 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨770, by decide⟩ cache770 partial770 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![771,772,773,774])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1702459102224499 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt771
  · exact receipt772
  · exact receipt773
  · exact receipt774

private theorem receipt769 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨769, by decide⟩ cache769 partial769 = true := by
  decide +kernel

private theorem receipt768 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨768, by decide⟩ cache768 partial768 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![769,770,775,776])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1706858222215218 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt769
  · exact receipt770
  · exact receipt775
  · exact receipt776

#print axioms receipt768

private theorem receipt767 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨767, by decide⟩ cache767 partial767 = true := by
  decide +kernel

private theorem receipt766 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨766, by decide⟩ cache766 partial766 = true := by
  decide +kernel

private theorem receipt765 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨765, by decide⟩ cache765 partial765 = true := by
  decide +kernel

private theorem receipt764 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨764, by decide⟩ cache764 partial764 = true := by
  decide +kernel

private theorem receipt763 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨763, by decide⟩ cache763 partial763 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![764,765,766,767])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1687062180421523 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt764
  · exact receipt765
  · exact receipt766
  · exact receipt767

private theorem receipt762 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨762, by decide⟩ cache762 partial762 = true := by
  decide +kernel

private theorem receipt761 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨761, by decide⟩ cache761 partial761 = true := by
  decide +kernel

private theorem receipt760 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨760, by decide⟩ cache760 partial760 = true := by
  decide +kernel

private theorem receipt759 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨759, by decide⟩ cache759 partial759 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![760,761,762,763])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1678263939391250 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt760
  · exact receipt761
  · exact receipt762
  · exact receipt763

private theorem receipt758 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨758, by decide⟩ cache758 partial758 = true := by
  decide +kernel

private theorem receipt757 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨757, by decide⟩ cache757 partial757 = true := by
  decide +kernel

private theorem receipt756 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨756, by decide⟩ cache756 partial756 = true := by
  decide +kernel

private theorem receipt755 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨755, by decide⟩ cache755 partial755 = true := by
  decide +kernel

private theorem receipt754 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨754, by decide⟩ cache754 partial754 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![755,756,757,758])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1667266138103411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt755
  · exact receipt756
  · exact receipt757
  · exact receipt758

private theorem receipt753 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨753, by decide⟩ cache753 partial753 = true := by
  decide +kernel

private theorem receipt752 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨752, by decide⟩ cache752 partial752 = true := by
  decide +kernel

private theorem receipt751 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨751, by decide⟩ cache751 partial751 = true := by
  decide +kernel

private theorem receipt750 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨750, by decide⟩ cache750 partial750 = true := by
  decide +kernel

private theorem receipt749 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨749, by decide⟩ cache749 partial749 = true := by
  decide +kernel

private theorem receipt748 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨748, by decide⟩ cache748 partial748 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![749,750,751,752])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1654068776558003 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt749
  · exact receipt750
  · exact receipt751
  · exact receipt752

private theorem receipt747 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨747, by decide⟩ cache747 partial747 = true := by
  decide +kernel

private theorem receipt746 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨746, by decide⟩ cache746 partial746 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![747,748,753,754])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1658467896548722 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt747
  · exact receipt748
  · exact receipt753
  · exact receipt754

private theorem receipt745 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨745, by decide⟩ cache745 partial745 = true := by
  decide +kernel

theorem receipt744 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨744, by decide⟩ cache744 partial744 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![745,746,759,768])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1689257443089713 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt745
  · exact receipt746
  · exact receipt759
  · exact receipt768


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock29
