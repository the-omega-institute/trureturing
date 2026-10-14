/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock31
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock31
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock31
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache631 : Cache :=
  step cache630 ⟨17, by decide⟩ 0
private def partial631 : Partial (Fin 20) (Fin 4) :=
  Function.update partial630 ⟨17, by decide⟩ (some 0)

private def cache632 : Cache :=
  step cache630 ⟨17, by decide⟩ 1
private def partial632 : Partial (Fin 20) (Fin 4) :=
  Function.update partial630 ⟨17, by decide⟩ (some 1)

private def cache633 : Cache :=
  step cache632 ⟨18, by decide⟩ 0
private def partial633 : Partial (Fin 20) (Fin 4) :=
  Function.update partial632 ⟨18, by decide⟩ (some 0)

private def cache634 : Cache :=
  step cache632 ⟨18, by decide⟩ 1
private def partial634 : Partial (Fin 20) (Fin 4) :=
  Function.update partial632 ⟨18, by decide⟩ (some 1)

private def cache635 : Cache :=
  step cache632 ⟨18, by decide⟩ 2
private def partial635 : Partial (Fin 20) (Fin 4) :=
  Function.update partial632 ⟨18, by decide⟩ (some 2)

private def cache636 : Cache :=
  step cache632 ⟨18, by decide⟩ 3
private def partial636 : Partial (Fin 20) (Fin 4) :=
  Function.update partial632 ⟨18, by decide⟩ (some 3)

private def cache637 : Cache :=
  step cache630 ⟨17, by decide⟩ 2
private def partial637 : Partial (Fin 20) (Fin 4) :=
  Function.update partial630 ⟨17, by decide⟩ (some 2)

private def cache638 : Cache :=
  step cache637 ⟨18, by decide⟩ 0
private def partial638 : Partial (Fin 20) (Fin 4) :=
  Function.update partial637 ⟨18, by decide⟩ (some 0)

private def cache639 : Cache :=
  step cache637 ⟨18, by decide⟩ 1
private def partial639 : Partial (Fin 20) (Fin 4) :=
  Function.update partial637 ⟨18, by decide⟩ (some 1)

private def cache640 : Cache :=
  step cache637 ⟨18, by decide⟩ 2
private def partial640 : Partial (Fin 20) (Fin 4) :=
  Function.update partial637 ⟨18, by decide⟩ (some 2)

private def cache641 : Cache :=
  step cache640 ⟨19, by decide⟩ 0
private def partial641 : Partial (Fin 20) (Fin 4) :=
  Function.update partial640 ⟨19, by decide⟩ (some 0)

private def cache642 : Cache :=
  step cache640 ⟨19, by decide⟩ 1
private def partial642 : Partial (Fin 20) (Fin 4) :=
  Function.update partial640 ⟨19, by decide⟩ (some 1)

private def cache643 : Cache :=
  step cache640 ⟨19, by decide⟩ 2
private def partial643 : Partial (Fin 20) (Fin 4) :=
  Function.update partial640 ⟨19, by decide⟩ (some 2)

private def cache644 : Cache :=
  step cache640 ⟨19, by decide⟩ 3
private def partial644 : Partial (Fin 20) (Fin 4) :=
  Function.update partial640 ⟨19, by decide⟩ (some 3)

private def cache645 : Cache :=
  step cache637 ⟨18, by decide⟩ 3
private def partial645 : Partial (Fin 20) (Fin 4) :=
  Function.update partial637 ⟨18, by decide⟩ (some 3)

private def cache646 : Cache :=
  step cache630 ⟨17, by decide⟩ 3
private def partial646 : Partial (Fin 20) (Fin 4) :=
  Function.update partial630 ⟨17, by decide⟩ (some 3)

private def cache647 : Cache :=
  step cache646 ⟨18, by decide⟩ 0
private def partial647 : Partial (Fin 20) (Fin 4) :=
  Function.update partial646 ⟨18, by decide⟩ (some 0)

private def cache648 : Cache :=
  step cache646 ⟨18, by decide⟩ 1
private def partial648 : Partial (Fin 20) (Fin 4) :=
  Function.update partial646 ⟨18, by decide⟩ (some 1)

private def cache649 : Cache :=
  step cache648 ⟨19, by decide⟩ 0
private def partial649 : Partial (Fin 20) (Fin 4) :=
  Function.update partial648 ⟨19, by decide⟩ (some 0)

private def cache650 : Cache :=
  step cache648 ⟨19, by decide⟩ 1
private def partial650 : Partial (Fin 20) (Fin 4) :=
  Function.update partial648 ⟨19, by decide⟩ (some 1)

private def cache651 : Cache :=
  step cache648 ⟨19, by decide⟩ 2
private def partial651 : Partial (Fin 20) (Fin 4) :=
  Function.update partial648 ⟨19, by decide⟩ (some 2)

private def cache652 : Cache :=
  step cache648 ⟨19, by decide⟩ 3
private def partial652 : Partial (Fin 20) (Fin 4) :=
  Function.update partial648 ⟨19, by decide⟩ (some 3)

private def cache653 : Cache :=
  step cache646 ⟨18, by decide⟩ 2
private def partial653 : Partial (Fin 20) (Fin 4) :=
  Function.update partial646 ⟨18, by decide⟩ (some 2)

private def cache654 : Cache :=
  step cache653 ⟨19, by decide⟩ 0
private def partial654 : Partial (Fin 20) (Fin 4) :=
  Function.update partial653 ⟨19, by decide⟩ (some 0)

private def cache655 : Cache :=
  step cache653 ⟨19, by decide⟩ 1
private def partial655 : Partial (Fin 20) (Fin 4) :=
  Function.update partial653 ⟨19, by decide⟩ (some 1)

private def cache656 : Cache :=
  step cache653 ⟨19, by decide⟩ 2
private def partial656 : Partial (Fin 20) (Fin 4) :=
  Function.update partial653 ⟨19, by decide⟩ (some 2)

private def cache657 : Cache :=
  step cache653 ⟨19, by decide⟩ 3
private def partial657 : Partial (Fin 20) (Fin 4) :=
  Function.update partial653 ⟨19, by decide⟩ (some 3)

private def cache658 : Cache :=
  step cache646 ⟨18, by decide⟩ 3
private def partial658 : Partial (Fin 20) (Fin 4) :=
  Function.update partial646 ⟨18, by decide⟩ (some 3)

private def cache660 : Cache :=
  step cache659 ⟨17, by decide⟩ 0
private def partial660 : Partial (Fin 20) (Fin 4) :=
  Function.update partial659 ⟨17, by decide⟩ (some 0)

private def cache661 : Cache :=
  step cache659 ⟨17, by decide⟩ 1
private def partial661 : Partial (Fin 20) (Fin 4) :=
  Function.update partial659 ⟨17, by decide⟩ (some 1)

private def cache662 : Cache :=
  step cache661 ⟨18, by decide⟩ 0
private def partial662 : Partial (Fin 20) (Fin 4) :=
  Function.update partial661 ⟨18, by decide⟩ (some 0)

private def cache663 : Cache :=
  step cache661 ⟨18, by decide⟩ 1
private def partial663 : Partial (Fin 20) (Fin 4) :=
  Function.update partial661 ⟨18, by decide⟩ (some 1)

private def cache664 : Cache :=
  step cache663 ⟨19, by decide⟩ 0
private def partial664 : Partial (Fin 20) (Fin 4) :=
  Function.update partial663 ⟨19, by decide⟩ (some 0)

private def cache665 : Cache :=
  step cache663 ⟨19, by decide⟩ 1
private def partial665 : Partial (Fin 20) (Fin 4) :=
  Function.update partial663 ⟨19, by decide⟩ (some 1)

private def cache666 : Cache :=
  step cache663 ⟨19, by decide⟩ 2
private def partial666 : Partial (Fin 20) (Fin 4) :=
  Function.update partial663 ⟨19, by decide⟩ (some 2)

private def cache667 : Cache :=
  step cache663 ⟨19, by decide⟩ 3
private def partial667 : Partial (Fin 20) (Fin 4) :=
  Function.update partial663 ⟨19, by decide⟩ (some 3)

private def cache668 : Cache :=
  step cache661 ⟨18, by decide⟩ 2
private def partial668 : Partial (Fin 20) (Fin 4) :=
  Function.update partial661 ⟨18, by decide⟩ (some 2)

private def cache669 : Cache :=
  step cache661 ⟨18, by decide⟩ 3
private def partial669 : Partial (Fin 20) (Fin 4) :=
  Function.update partial661 ⟨18, by decide⟩ (some 3)

private def cache670 : Cache :=
  step cache669 ⟨19, by decide⟩ 0
private def partial670 : Partial (Fin 20) (Fin 4) :=
  Function.update partial669 ⟨19, by decide⟩ (some 0)

private def cache671 : Cache :=
  step cache669 ⟨19, by decide⟩ 1
private def partial671 : Partial (Fin 20) (Fin 4) :=
  Function.update partial669 ⟨19, by decide⟩ (some 1)

private def cache672 : Cache :=
  step cache669 ⟨19, by decide⟩ 2
private def partial672 : Partial (Fin 20) (Fin 4) :=
  Function.update partial669 ⟨19, by decide⟩ (some 2)

private def cache673 : Cache :=
  step cache669 ⟨19, by decide⟩ 3
private def partial673 : Partial (Fin 20) (Fin 4) :=
  Function.update partial669 ⟨19, by decide⟩ (some 3)

private def cache674 : Cache :=
  step cache659 ⟨17, by decide⟩ 2
private def partial674 : Partial (Fin 20) (Fin 4) :=
  Function.update partial659 ⟨17, by decide⟩ (some 2)

private def cache675 : Cache :=
  step cache674 ⟨18, by decide⟩ 0
private def partial675 : Partial (Fin 20) (Fin 4) :=
  Function.update partial674 ⟨18, by decide⟩ (some 0)

private def cache676 : Cache :=
  step cache674 ⟨18, by decide⟩ 1
private def partial676 : Partial (Fin 20) (Fin 4) :=
  Function.update partial674 ⟨18, by decide⟩ (some 1)

private def cache677 : Cache :=
  step cache674 ⟨18, by decide⟩ 2
private def partial677 : Partial (Fin 20) (Fin 4) :=
  Function.update partial674 ⟨18, by decide⟩ (some 2)

private def cache678 : Cache :=
  step cache674 ⟨18, by decide⟩ 3
private def partial678 : Partial (Fin 20) (Fin 4) :=
  Function.update partial674 ⟨18, by decide⟩ (some 3)

private def cache679 : Cache :=
  step cache659 ⟨17, by decide⟩ 3
private def partial679 : Partial (Fin 20) (Fin 4) :=
  Function.update partial659 ⟨17, by decide⟩ (some 3)

private def cache680 : Cache :=
  step cache679 ⟨18, by decide⟩ 0
private def partial680 : Partial (Fin 20) (Fin 4) :=
  Function.update partial679 ⟨18, by decide⟩ (some 0)

private def cache681 : Cache :=
  step cache679 ⟨18, by decide⟩ 1
private def partial681 : Partial (Fin 20) (Fin 4) :=
  Function.update partial679 ⟨18, by decide⟩ (some 1)

private def cache682 : Cache :=
  step cache679 ⟨18, by decide⟩ 2
private def partial682 : Partial (Fin 20) (Fin 4) :=
  Function.update partial679 ⟨18, by decide⟩ (some 2)

private def cache683 : Cache :=
  step cache682 ⟨19, by decide⟩ 0
private def partial683 : Partial (Fin 20) (Fin 4) :=
  Function.update partial682 ⟨19, by decide⟩ (some 0)

private def cache684 : Cache :=
  step cache682 ⟨19, by decide⟩ 1
private def partial684 : Partial (Fin 20) (Fin 4) :=
  Function.update partial682 ⟨19, by decide⟩ (some 1)

private def cache685 : Cache :=
  step cache682 ⟨19, by decide⟩ 2
private def partial685 : Partial (Fin 20) (Fin 4) :=
  Function.update partial682 ⟨19, by decide⟩ (some 2)

private def cache686 : Cache :=
  step cache682 ⟨19, by decide⟩ 3
private def partial686 : Partial (Fin 20) (Fin 4) :=
  Function.update partial682 ⟨19, by decide⟩ (some 3)

private def cache687 : Cache :=
  step cache679 ⟨18, by decide⟩ 3
private def partial687 : Partial (Fin 20) (Fin 4) :=
  Function.update partial679 ⟨18, by decide⟩ (some 3)

private def cache688 : Cache :=
  step cache687 ⟨19, by decide⟩ 0
private def partial688 : Partial (Fin 20) (Fin 4) :=
  Function.update partial687 ⟨19, by decide⟩ (some 0)

private def cache689 : Cache :=
  step cache687 ⟨19, by decide⟩ 1
private def partial689 : Partial (Fin 20) (Fin 4) :=
  Function.update partial687 ⟨19, by decide⟩ (some 1)

private def cache690 : Cache :=
  step cache687 ⟨19, by decide⟩ 2
private def partial690 : Partial (Fin 20) (Fin 4) :=
  Function.update partial687 ⟨19, by decide⟩ (some 2)

private def cache691 : Cache :=
  step cache687 ⟨19, by decide⟩ 3
private def partial691 : Partial (Fin 20) (Fin 4) :=
  Function.update partial687 ⟨19, by decide⟩ (some 3)

private theorem receipt691 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨691, by decide⟩ cache691 partial691 = true := by
  decide +kernel

private theorem receipt690 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨690, by decide⟩ cache690 partial690 = true := by
  decide +kernel

private theorem receipt689 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨689, by decide⟩ cache689 partial689 = true := by
  decide +kernel

private theorem receipt688 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨688, by decide⟩ cache688 partial688 = true := by
  decide +kernel

private theorem receipt687 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨687, by decide⟩ cache687 partial687 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![688,689,690,691])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1519895600846355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt688
  · exact receipt689
  · exact receipt690
  · exact receipt691

private theorem receipt686 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨686, by decide⟩ cache686 partial686 = true := by
  decide +kernel

private theorem receipt685 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨685, by decide⟩ cache685 partial685 = true := by
  decide +kernel

private theorem receipt684 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨684, by decide⟩ cache684 partial684 = true := by
  decide +kernel

private theorem receipt683 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨683, by decide⟩ cache683 partial683 = true := by
  decide +kernel

private theorem receipt682 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨682, by decide⟩ cache682 partial682 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![683,684,685,686])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1508897799558515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt683
  · exact receipt684
  · exact receipt685
  · exact receipt686

private theorem receipt681 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨681, by decide⟩ cache681 partial681 = true := by
  decide +kernel

private theorem receipt680 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨680, by decide⟩ cache680 partial680 = true := by
  decide +kernel

private theorem receipt679 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨679, by decide⟩ cache679 partial679 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![680,681,682,687])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1511095211808018 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt680
  · exact receipt681
  · exact receipt682
  · exact receipt687

private theorem receipt678 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨678, by decide⟩ cache678 partial678 = true := by
  decide +kernel

private theorem receipt677 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨677, by decide⟩ cache677 partial677 = true := by
  decide +kernel

private theorem receipt676 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨676, by decide⟩ cache676 partial676 = true := by
  decide +kernel

private theorem receipt675 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨675, by decide⟩ cache675 partial675 = true := by
  decide +kernel

private theorem receipt674 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨674, by decide⟩ cache674 partial674 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![675,676,677,678])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1491301317497970 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt675
  · exact receipt676
  · exact receipt677
  · exact receipt678

private theorem receipt673 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨673, by decide⟩ cache673 partial673 = true := by
  decide +kernel

private theorem receipt672 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨672, by decide⟩ cache672 partial672 = true := by
  decide +kernel

private theorem receipt671 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨671, by decide⟩ cache671 partial671 = true := by
  decide +kernel

private theorem receipt670 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨670, by decide⟩ cache670 partial670 = true := by
  decide +kernel

private theorem receipt669 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨669, by decide⟩ cache669 partial669 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![670,671,672,673])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1480303516210131 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt670
  · exact receipt671
  · exact receipt672
  · exact receipt673

private theorem receipt668 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨668, by decide⟩ cache668 partial668 = true := by
  decide +kernel

private theorem receipt667 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨667, by decide⟩ cache667 partial667 = true := by
  decide +kernel

private theorem receipt666 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨666, by decide⟩ cache666 partial666 = true := by
  decide +kernel

private theorem receipt665 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨665, by decide⟩ cache665 partial665 = true := by
  decide +kernel

private theorem receipt664 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨664, by decide⟩ cache664 partial664 = true := by
  decide +kernel

private theorem receipt663 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨663, by decide⟩ cache663 partial663 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![664,665,666,667])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1467106154664723 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt664
  · exact receipt665
  · exact receipt666
  · exact receipt667

private theorem receipt662 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨662, by decide⟩ cache662 partial662 = true := by
  decide +kernel

private theorem receipt661 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨661, by decide⟩ cache661 partial661 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![662,663,668,669])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1471505274655442 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt662
  · exact receipt663
  · exact receipt668
  · exact receipt669

private theorem receipt660 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨660, by decide⟩ cache660 partial660 = true := by
  decide +kernel

theorem receipt659 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨659, by decide⟩ cache659 partial659 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![660,661,674,679])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1493498728174225 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt660
  · exact receipt661
  · exact receipt674
  · exact receipt679

private theorem receipt658 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨658, by decide⟩ cache658 partial658 = true := by
  decide +kernel

private theorem receipt657 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨657, by decide⟩ cache657 partial657 = true := by
  decide +kernel

private theorem receipt656 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨656, by decide⟩ cache656 partial656 = true := by
  decide +kernel

private theorem receipt655 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨655, by decide⟩ cache655 partial655 = true := by
  decide +kernel

private theorem receipt654 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨654, by decide⟩ cache654 partial654 = true := by
  decide +kernel

private theorem receipt653 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨653, by decide⟩ cache653 partial653 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![654,655,656,657])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1445110552089043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt654
  · exact receipt655
  · exact receipt656
  · exact receipt657

private theorem receipt652 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨652, by decide⟩ cache652 partial652 = true := by
  decide +kernel

private theorem receipt651 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨651, by decide⟩ cache651 partial651 = true := by
  decide +kernel

private theorem receipt650 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨650, by decide⟩ cache650 partial650 = true := by
  decide +kernel

private theorem receipt649 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨649, by decide⟩ cache649 partial649 = true := by
  decide +kernel

private theorem receipt648 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨648, by decide⟩ cache648 partial648 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![649,650,651,652])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1434112750801203 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt649
  · exact receipt650
  · exact receipt651
  · exact receipt652

private theorem receipt647 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨647, by decide⟩ cache647 partial647 = true := by
  decide +kernel

private theorem receipt646 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨646, by decide⟩ cache646 partial646 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![647,648,653,658])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1447307963814130 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt647
  · exact receipt648
  · exact receipt653
  · exact receipt658

private theorem receipt645 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨645, by decide⟩ cache645 partial645 = true := by
  decide +kernel

private theorem receipt644 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨644, by decide⟩ cache644 partial644 = true := by
  decide +kernel

private theorem receipt643 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨643, by decide⟩ cache643 partial643 = true := by
  decide +kernel

private theorem receipt642 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨642, by decide⟩ cache642 partial642 = true := by
  decide +kernel

private theorem receipt641 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨641, by decide⟩ cache641 partial641 = true := by
  decide +kernel

private theorem receipt640 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨640, by decide⟩ cache640 partial640 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![641,642,643,644])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1416516268740659 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt641
  · exact receipt642
  · exact receipt643
  · exact receipt644

private theorem receipt639 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨639, by decide⟩ cache639 partial639 = true := by
  decide +kernel

private theorem receipt638 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨638, by decide⟩ cache638 partial638 = true := by
  decide +kernel

private theorem receipt637 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨637, by decide⟩ cache637 partial637 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![638,639,640,645])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1418713680990162 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt638
  · exact receipt639
  · exact receipt640
  · exact receipt645

private theorem receipt636 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨636, by decide⟩ cache636 partial636 = true := by
  decide +kernel

private theorem receipt635 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨635, by decide⟩ cache635 partial635 = true := by
  decide +kernel

private theorem receipt634 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨634, by decide⟩ cache634 partial634 = true := by
  decide +kernel

private theorem receipt633 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨633, by decide⟩ cache633 partial633 = true := by
  decide +kernel

private theorem receipt632 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨632, by decide⟩ cache632 partial632 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![633,634,635,636])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1398919786680114 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt633
  · exact receipt634
  · exact receipt635
  · exact receipt636

private theorem receipt631 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨631, by decide⟩ cache631 partial631 = true := by
  decide +kernel

theorem receipt630 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨630, by decide⟩ cache630 partial630 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![631,632,637,646])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1420911092715249 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt631
  · exact receipt632
  · exact receipt637
  · exact receipt646

theorem receipt629 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨629, by decide⟩ cache629 partial629 = true := by
  decide +kernel

theorem receipt628 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨628, by decide⟩ cache628 partial628 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock31
