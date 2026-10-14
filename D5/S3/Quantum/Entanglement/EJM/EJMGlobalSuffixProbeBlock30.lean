/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock30
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock30
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock30
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache696 : Cache :=
  step cache695 ⟨17, by decide⟩ 0
private def partial696 : Partial (Fin 20) (Fin 4) :=
  Function.update partial695 ⟨17, by decide⟩ (some 0)

private def cache697 : Cache :=
  step cache695 ⟨17, by decide⟩ 1
private def partial697 : Partial (Fin 20) (Fin 4) :=
  Function.update partial695 ⟨17, by decide⟩ (some 1)

private def cache698 : Cache :=
  step cache697 ⟨18, by decide⟩ 0
private def partial698 : Partial (Fin 20) (Fin 4) :=
  Function.update partial697 ⟨18, by decide⟩ (some 0)

private def cache699 : Cache :=
  step cache697 ⟨18, by decide⟩ 1
private def partial699 : Partial (Fin 20) (Fin 4) :=
  Function.update partial697 ⟨18, by decide⟩ (some 1)

private def cache700 : Cache :=
  step cache697 ⟨18, by decide⟩ 2
private def partial700 : Partial (Fin 20) (Fin 4) :=
  Function.update partial697 ⟨18, by decide⟩ (some 2)

private def cache701 : Cache :=
  step cache697 ⟨18, by decide⟩ 3
private def partial701 : Partial (Fin 20) (Fin 4) :=
  Function.update partial697 ⟨18, by decide⟩ (some 3)

private def cache702 : Cache :=
  step cache701 ⟨19, by decide⟩ 0
private def partial702 : Partial (Fin 20) (Fin 4) :=
  Function.update partial701 ⟨19, by decide⟩ (some 0)

private def cache703 : Cache :=
  step cache701 ⟨19, by decide⟩ 1
private def partial703 : Partial (Fin 20) (Fin 4) :=
  Function.update partial701 ⟨19, by decide⟩ (some 1)

private def cache704 : Cache :=
  step cache701 ⟨19, by decide⟩ 2
private def partial704 : Partial (Fin 20) (Fin 4) :=
  Function.update partial701 ⟨19, by decide⟩ (some 2)

private def cache705 : Cache :=
  step cache701 ⟨19, by decide⟩ 3
private def partial705 : Partial (Fin 20) (Fin 4) :=
  Function.update partial701 ⟨19, by decide⟩ (some 3)

private def cache706 : Cache :=
  step cache695 ⟨17, by decide⟩ 2
private def partial706 : Partial (Fin 20) (Fin 4) :=
  Function.update partial695 ⟨17, by decide⟩ (some 2)

private def cache707 : Cache :=
  step cache706 ⟨18, by decide⟩ 0
private def partial707 : Partial (Fin 20) (Fin 4) :=
  Function.update partial706 ⟨18, by decide⟩ (some 0)

private def cache708 : Cache :=
  step cache707 ⟨19, by decide⟩ 0
private def partial708 : Partial (Fin 20) (Fin 4) :=
  Function.update partial707 ⟨19, by decide⟩ (some 0)

private def cache709 : Cache :=
  step cache707 ⟨19, by decide⟩ 1
private def partial709 : Partial (Fin 20) (Fin 4) :=
  Function.update partial707 ⟨19, by decide⟩ (some 1)

private def cache710 : Cache :=
  step cache707 ⟨19, by decide⟩ 2
private def partial710 : Partial (Fin 20) (Fin 4) :=
  Function.update partial707 ⟨19, by decide⟩ (some 2)

private def cache711 : Cache :=
  step cache707 ⟨19, by decide⟩ 3
private def partial711 : Partial (Fin 20) (Fin 4) :=
  Function.update partial707 ⟨19, by decide⟩ (some 3)

private def cache712 : Cache :=
  step cache706 ⟨18, by decide⟩ 1
private def partial712 : Partial (Fin 20) (Fin 4) :=
  Function.update partial706 ⟨18, by decide⟩ (some 1)

private def cache713 : Cache :=
  step cache712 ⟨19, by decide⟩ 0
private def partial713 : Partial (Fin 20) (Fin 4) :=
  Function.update partial712 ⟨19, by decide⟩ (some 0)

private def cache714 : Cache :=
  step cache712 ⟨19, by decide⟩ 1
private def partial714 : Partial (Fin 20) (Fin 4) :=
  Function.update partial712 ⟨19, by decide⟩ (some 1)

private def cache715 : Cache :=
  step cache712 ⟨19, by decide⟩ 2
private def partial715 : Partial (Fin 20) (Fin 4) :=
  Function.update partial712 ⟨19, by decide⟩ (some 2)

private def cache716 : Cache :=
  step cache712 ⟨19, by decide⟩ 3
private def partial716 : Partial (Fin 20) (Fin 4) :=
  Function.update partial712 ⟨19, by decide⟩ (some 3)

private def cache717 : Cache :=
  step cache706 ⟨18, by decide⟩ 2
private def partial717 : Partial (Fin 20) (Fin 4) :=
  Function.update partial706 ⟨18, by decide⟩ (some 2)

private def cache718 : Cache :=
  step cache706 ⟨18, by decide⟩ 3
private def partial718 : Partial (Fin 20) (Fin 4) :=
  Function.update partial706 ⟨18, by decide⟩ (some 3)

private def cache719 : Cache :=
  step cache718 ⟨19, by decide⟩ 0
private def partial719 : Partial (Fin 20) (Fin 4) :=
  Function.update partial718 ⟨19, by decide⟩ (some 0)

private def cache720 : Cache :=
  step cache718 ⟨19, by decide⟩ 1
private def partial720 : Partial (Fin 20) (Fin 4) :=
  Function.update partial718 ⟨19, by decide⟩ (some 1)

private def cache721 : Cache :=
  step cache718 ⟨19, by decide⟩ 2
private def partial721 : Partial (Fin 20) (Fin 4) :=
  Function.update partial718 ⟨19, by decide⟩ (some 2)

private def cache722 : Cache :=
  step cache718 ⟨19, by decide⟩ 3
private def partial722 : Partial (Fin 20) (Fin 4) :=
  Function.update partial718 ⟨19, by decide⟩ (some 3)

private def cache723 : Cache :=
  step cache695 ⟨17, by decide⟩ 3
private def partial723 : Partial (Fin 20) (Fin 4) :=
  Function.update partial695 ⟨17, by decide⟩ (some 3)

private def cache724 : Cache :=
  step cache723 ⟨18, by decide⟩ 0
private def partial724 : Partial (Fin 20) (Fin 4) :=
  Function.update partial723 ⟨18, by decide⟩ (some 0)

private def cache725 : Cache :=
  step cache724 ⟨19, by decide⟩ 0
private def partial725 : Partial (Fin 20) (Fin 4) :=
  Function.update partial724 ⟨19, by decide⟩ (some 0)

private def cache726 : Cache :=
  step cache724 ⟨19, by decide⟩ 1
private def partial726 : Partial (Fin 20) (Fin 4) :=
  Function.update partial724 ⟨19, by decide⟩ (some 1)

private def cache727 : Cache :=
  step cache724 ⟨19, by decide⟩ 2
private def partial727 : Partial (Fin 20) (Fin 4) :=
  Function.update partial724 ⟨19, by decide⟩ (some 2)

private def cache728 : Cache :=
  step cache724 ⟨19, by decide⟩ 3
private def partial728 : Partial (Fin 20) (Fin 4) :=
  Function.update partial724 ⟨19, by decide⟩ (some 3)

private def cache729 : Cache :=
  step cache723 ⟨18, by decide⟩ 1
private def partial729 : Partial (Fin 20) (Fin 4) :=
  Function.update partial723 ⟨18, by decide⟩ (some 1)

private def cache730 : Cache :=
  step cache729 ⟨19, by decide⟩ 0
private def partial730 : Partial (Fin 20) (Fin 4) :=
  Function.update partial729 ⟨19, by decide⟩ (some 0)

private def cache731 : Cache :=
  step cache729 ⟨19, by decide⟩ 1
private def partial731 : Partial (Fin 20) (Fin 4) :=
  Function.update partial729 ⟨19, by decide⟩ (some 1)

private def cache732 : Cache :=
  step cache729 ⟨19, by decide⟩ 2
private def partial732 : Partial (Fin 20) (Fin 4) :=
  Function.update partial729 ⟨19, by decide⟩ (some 2)

private def cache733 : Cache :=
  step cache729 ⟨19, by decide⟩ 3
private def partial733 : Partial (Fin 20) (Fin 4) :=
  Function.update partial729 ⟨19, by decide⟩ (some 3)

private def cache734 : Cache :=
  step cache723 ⟨18, by decide⟩ 2
private def partial734 : Partial (Fin 20) (Fin 4) :=
  Function.update partial723 ⟨18, by decide⟩ (some 2)

private def cache735 : Cache :=
  step cache734 ⟨19, by decide⟩ 0
private def partial735 : Partial (Fin 20) (Fin 4) :=
  Function.update partial734 ⟨19, by decide⟩ (some 0)

private def cache736 : Cache :=
  step cache734 ⟨19, by decide⟩ 1
private def partial736 : Partial (Fin 20) (Fin 4) :=
  Function.update partial734 ⟨19, by decide⟩ (some 1)

private def cache737 : Cache :=
  step cache734 ⟨19, by decide⟩ 2
private def partial737 : Partial (Fin 20) (Fin 4) :=
  Function.update partial734 ⟨19, by decide⟩ (some 2)

private def cache738 : Cache :=
  step cache734 ⟨19, by decide⟩ 3
private def partial738 : Partial (Fin 20) (Fin 4) :=
  Function.update partial734 ⟨19, by decide⟩ (some 3)

private def cache739 : Cache :=
  step cache723 ⟨18, by decide⟩ 3
private def partial739 : Partial (Fin 20) (Fin 4) :=
  Function.update partial723 ⟨18, by decide⟩ (some 3)

private def cache740 : Cache :=
  step cache739 ⟨19, by decide⟩ 0
private def partial740 : Partial (Fin 20) (Fin 4) :=
  Function.update partial739 ⟨19, by decide⟩ (some 0)

private def cache741 : Cache :=
  step cache739 ⟨19, by decide⟩ 1
private def partial741 : Partial (Fin 20) (Fin 4) :=
  Function.update partial739 ⟨19, by decide⟩ (some 1)

private def cache742 : Cache :=
  step cache739 ⟨19, by decide⟩ 2
private def partial742 : Partial (Fin 20) (Fin 4) :=
  Function.update partial739 ⟨19, by decide⟩ (some 2)

private def cache743 : Cache :=
  step cache739 ⟨19, by decide⟩ 3
private def partial743 : Partial (Fin 20) (Fin 4) :=
  Function.update partial739 ⟨19, by decide⟩ (some 3)

private theorem receipt743 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨743, by decide⟩ cache743 partial743 = true := by
  decide +kernel

private theorem receipt742 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨742, by decide⟩ cache742 partial742 = true := by
  decide +kernel

private theorem receipt741 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨741, by decide⟩ cache741 partial741 = true := by
  decide +kernel

private theorem receipt740 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨740, by decide⟩ cache740 partial740 = true := by
  decide +kernel

private theorem receipt739 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨739, by decide⟩ cache739 partial739 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![740,741,742,743])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1634272734239891 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt740
  · exact receipt741
  · exact receipt742
  · exact receipt743

private theorem receipt738 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨738, by decide⟩ cache738 partial738 = true := by
  decide +kernel

private theorem receipt737 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨737, by decide⟩ cache737 partial737 = true := by
  decide +kernel

private theorem receipt736 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨736, by decide⟩ cache736 partial736 = true := by
  decide +kernel

private theorem receipt735 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨735, by decide⟩ cache735 partial735 = true := by
  decide +kernel

private theorem receipt734 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨734, by decide⟩ cache734 partial734 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![735,736,737,738])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1623274932952051 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt735
  · exact receipt736
  · exact receipt737
  · exact receipt738

private theorem receipt733 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨733, by decide⟩ cache733 partial733 = true := by
  decide +kernel

private theorem receipt732 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨732, by decide⟩ cache732 partial732 = true := by
  decide +kernel

private theorem receipt731 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨731, by decide⟩ cache731 partial731 = true := by
  decide +kernel

private theorem receipt730 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨730, by decide⟩ cache730 partial730 = true := by
  decide +kernel

private theorem receipt729 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨729, by decide⟩ cache729 partial729 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![730,731,732,733])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1612277131664211 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt730
  · exact receipt731
  · exact receipt732
  · exact receipt733

private theorem receipt728 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨728, by decide⟩ cache728 partial728 = true := by
  decide +kernel

private theorem receipt727 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨727, by decide⟩ cache727 partial727 = true := by
  decide +kernel

private theorem receipt726 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨726, by decide⟩ cache726 partial726 = true := by
  decide +kernel

private theorem receipt725 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨725, by decide⟩ cache725 partial725 = true := by
  decide +kernel

private theorem receipt724 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨724, by decide⟩ cache724 partial724 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![725,726,727,728])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1601279330376371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt725
  · exact receipt726
  · exact receipt727
  · exact receipt728

private theorem receipt723 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨723, by decide⟩ cache723 partial723 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![724,729,734,739])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1625472344677010 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt724
  · exact receipt729
  · exact receipt734
  · exact receipt739

private theorem receipt722 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨722, by decide⟩ cache722 partial722 = true := by
  decide +kernel

private theorem receipt721 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨721, by decide⟩ cache721 partial721 = true := by
  decide +kernel

private theorem receipt720 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨720, by decide⟩ cache720 partial720 = true := by
  decide +kernel

private theorem receipt719 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨719, by decide⟩ cache719 partial719 = true := by
  decide +kernel

private theorem receipt718 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨718, by decide⟩ cache718 partial718 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![719,720,721,722])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1588081968830963 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt719
  · exact receipt720
  · exact receipt721
  · exact receipt722

private theorem receipt717 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨717, by decide⟩ cache717 partial717 = true := by
  decide +kernel

private theorem receipt716 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨716, by decide⟩ cache716 partial716 = true := by
  decide +kernel

private theorem receipt715 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨715, by decide⟩ cache715 partial715 = true := by
  decide +kernel

private theorem receipt714 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨714, by decide⟩ cache714 partial714 = true := by
  decide +kernel

private theorem receipt713 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨713, by decide⟩ cache713 partial713 = true := by
  decide +kernel

private theorem receipt712 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨712, by decide⟩ cache712 partial712 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![713,714,715,716])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1574884607285555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt713
  · exact receipt714
  · exact receipt715
  · exact receipt716

private theorem receipt711 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨711, by decide⟩ cache711 partial711 = true := by
  decide +kernel

private theorem receipt710 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨710, by decide⟩ cache710 partial710 = true := by
  decide +kernel

private theorem receipt709 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨709, by decide⟩ cache709 partial709 = true := by
  decide +kernel

private theorem receipt708 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨708, by decide⟩ cache708 partial708 = true := by
  decide +kernel

private theorem receipt707 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨707, by decide⟩ cache707 partial707 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![708,709,710,711])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1563886805997715 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt708
  · exact receipt709
  · exact receipt710
  · exact receipt711

private theorem receipt706 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨706, by decide⟩ cache706 partial706 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![707,712,717,718])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1579283727276146 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt707
  · exact receipt712
  · exact receipt717
  · exact receipt718

private theorem receipt705 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨705, by decide⟩ cache705 partial705 = true := by
  decide +kernel

private theorem receipt704 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨704, by decide⟩ cache704 partial704 = true := by
  decide +kernel

private theorem receipt703 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨703, by decide⟩ cache703 partial703 = true := by
  decide +kernel

private theorem receipt702 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨702, by decide⟩ cache702 partial702 = true := by
  decide +kernel

private theorem receipt701 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨701, by decide⟩ cache701 partial701 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![702,703,704,705])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1550689444452307 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt702
  · exact receipt703
  · exact receipt704
  · exact receipt705

private theorem receipt700 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨700, by decide⟩ cache700 partial700 = true := by
  decide +kernel

private theorem receipt699 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨699, by decide⟩ cache699 partial699 = true := by
  decide +kernel

private theorem receipt698 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨698, by decide⟩ cache698 partial698 = true := by
  decide +kernel

private theorem receipt697 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨697, by decide⟩ cache697 partial697 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![698,699,700,701])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1541891203422034 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt698
  · exact receipt699
  · exact receipt700
  · exact receipt701

private theorem receipt696 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨696, by decide⟩ cache696 partial696 = true := by
  decide +kernel

theorem receipt695 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨695, by decide⟩ cache695 partial695 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![696,697,706,723])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1590272936007441 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt696
  · exact receipt697
  · exact receipt706
  · exact receipt723

theorem receipt694 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨694, by decide⟩ cache694 partial694 = true := by
  decide +kernel

theorem receipt693 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨693, by decide⟩ cache693 partial693 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock30
