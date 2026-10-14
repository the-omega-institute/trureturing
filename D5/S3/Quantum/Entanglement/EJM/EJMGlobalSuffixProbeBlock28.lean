/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock28
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock28
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock28
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache785 : Cache :=
  step cache784 ⟨17, by decide⟩ 0
private def partial785 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 0)

private def cache786 : Cache :=
  step cache784 ⟨17, by decide⟩ 1
private def partial786 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 1)

private def cache787 : Cache :=
  step cache786 ⟨18, by decide⟩ 0
private def partial787 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 0)

private def cache788 : Cache :=
  step cache786 ⟨18, by decide⟩ 1
private def partial788 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 1)

private def cache789 : Cache :=
  step cache786 ⟨18, by decide⟩ 2
private def partial789 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 2)

private def cache790 : Cache :=
  step cache786 ⟨18, by decide⟩ 3
private def partial790 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 3)

private def cache791 : Cache :=
  step cache790 ⟨19, by decide⟩ 0
private def partial791 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 0)

private def cache792 : Cache :=
  step cache790 ⟨19, by decide⟩ 1
private def partial792 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 1)

private def cache793 : Cache :=
  step cache790 ⟨19, by decide⟩ 2
private def partial793 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 2)

private def cache794 : Cache :=
  step cache790 ⟨19, by decide⟩ 3
private def partial794 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 3)

private def cache795 : Cache :=
  step cache784 ⟨17, by decide⟩ 2
private def partial795 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 2)

private def cache796 : Cache :=
  step cache795 ⟨18, by decide⟩ 0
private def partial796 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 0)

private def cache797 : Cache :=
  step cache795 ⟨18, by decide⟩ 1
private def partial797 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 1)

private def cache798 : Cache :=
  step cache795 ⟨18, by decide⟩ 2
private def partial798 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 2)

private def cache799 : Cache :=
  step cache795 ⟨18, by decide⟩ 3
private def partial799 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 3)

private def cache800 : Cache :=
  step cache784 ⟨17, by decide⟩ 3
private def partial800 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 3)

private def cache801 : Cache :=
  step cache800 ⟨18, by decide⟩ 0
private def partial801 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 0)

private def cache802 : Cache :=
  step cache801 ⟨19, by decide⟩ 0
private def partial802 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 0)

private def cache803 : Cache :=
  step cache801 ⟨19, by decide⟩ 1
private def partial803 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 1)

private def cache804 : Cache :=
  step cache801 ⟨19, by decide⟩ 2
private def partial804 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 2)

private def cache805 : Cache :=
  step cache801 ⟨19, by decide⟩ 3
private def partial805 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 3)

private def cache806 : Cache :=
  step cache800 ⟨18, by decide⟩ 1
private def partial806 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 1)

private def cache807 : Cache :=
  step cache806 ⟨19, by decide⟩ 0
private def partial807 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 0)

private def cache808 : Cache :=
  step cache806 ⟨19, by decide⟩ 1
private def partial808 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 1)

private def cache809 : Cache :=
  step cache806 ⟨19, by decide⟩ 2
private def partial809 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 2)

private def cache810 : Cache :=
  step cache806 ⟨19, by decide⟩ 3
private def partial810 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 3)

private def cache811 : Cache :=
  step cache800 ⟨18, by decide⟩ 2
private def partial811 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 2)

private def cache812 : Cache :=
  step cache811 ⟨19, by decide⟩ 0
private def partial812 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 0)

private def cache813 : Cache :=
  step cache811 ⟨19, by decide⟩ 1
private def partial813 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 1)

private def cache814 : Cache :=
  step cache811 ⟨19, by decide⟩ 2
private def partial814 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 2)

private def cache815 : Cache :=
  step cache811 ⟨19, by decide⟩ 3
private def partial815 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 3)

private def cache816 : Cache :=
  step cache800 ⟨18, by decide⟩ 3
private def partial816 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 3)

private def cache817 : Cache :=
  step cache816 ⟨19, by decide⟩ 0
private def partial817 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 0)

private def cache818 : Cache :=
  step cache816 ⟨19, by decide⟩ 1
private def partial818 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 1)

private def cache819 : Cache :=
  step cache816 ⟨19, by decide⟩ 2
private def partial819 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 2)

private def cache820 : Cache :=
  step cache816 ⟨19, by decide⟩ 3
private def partial820 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 3)

private theorem receipt820 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨820, by decide⟩ cache820 partial820 = true := by
  decide +kernel

private theorem receipt819 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨819, by decide⟩ cache819 partial819 = true := by
  decide +kernel

private theorem receipt818 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨818, by decide⟩ cache818 partial818 = true := by
  decide +kernel

private theorem receipt817 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨817, by decide⟩ cache817 partial817 = true := by
  decide +kernel

private theorem receipt816 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨816, by decide⟩ cache816 partial816 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![817,818,819,820])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1803638874072627 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt817
  · exact receipt818
  · exact receipt819
  · exact receipt820

private theorem receipt815 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨815, by decide⟩ cache815 partial815 = true := by
  decide +kernel

private theorem receipt814 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨814, by decide⟩ cache814 partial814 = true := by
  decide +kernel

private theorem receipt813 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨813, by decide⟩ cache813 partial813 = true := by
  decide +kernel

private theorem receipt812 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨812, by decide⟩ cache812 partial812 = true := by
  decide +kernel

private theorem receipt811 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨811, by decide⟩ cache811 partial811 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![812,813,814,815])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1792641072784787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt812
  · exact receipt813
  · exact receipt814
  · exact receipt815

private theorem receipt810 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨810, by decide⟩ cache810 partial810 = true := by
  decide +kernel

private theorem receipt809 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨809, by decide⟩ cache809 partial809 = true := by
  decide +kernel

private theorem receipt808 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨808, by decide⟩ cache808 partial808 = true := by
  decide +kernel

private theorem receipt807 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨807, by decide⟩ cache807 partial807 = true := by
  decide +kernel

private theorem receipt806 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨806, by decide⟩ cache806 partial806 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![807,808,809,810])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1781643271496947 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt807
  · exact receipt808
  · exact receipt809
  · exact receipt810

private theorem receipt805 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨805, by decide⟩ cache805 partial805 = true := by
  decide +kernel

private theorem receipt804 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨804, by decide⟩ cache804 partial804 = true := by
  decide +kernel

private theorem receipt803 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨803, by decide⟩ cache803 partial803 = true := by
  decide +kernel

private theorem receipt802 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨802, by decide⟩ cache802 partial802 = true := by
  decide +kernel

private theorem receipt801 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨801, by decide⟩ cache801 partial801 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![802,803,804,805])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1770645470209107 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt802
  · exact receipt803
  · exact receipt804
  · exact receipt805

private theorem receipt800 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨800, by decide⟩ cache800 partial800 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![801,806,811,816])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1794838484509746 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt801
  · exact receipt806
  · exact receipt811
  · exact receipt816

private theorem receipt799 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨799, by decide⟩ cache799 partial799 = true := by
  decide +kernel

private theorem receipt798 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨798, by decide⟩ cache798 partial798 = true := by
  decide +kernel

private theorem receipt797 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨797, by decide⟩ cache797 partial797 = true := by
  decide +kernel

private theorem receipt796 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨796, by decide⟩ cache796 partial796 = true := by
  decide +kernel

private theorem receipt795 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨795, by decide⟩ cache795 partial795 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![796,797,798,799])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1757448108663698 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt796
  · exact receipt797
  · exact receipt798
  · exact receipt799

private theorem receipt794 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨794, by decide⟩ cache794 partial794 = true := by
  decide +kernel

private theorem receipt793 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨793, by decide⟩ cache793 partial793 = true := by
  decide +kernel

private theorem receipt792 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨792, by decide⟩ cache792 partial792 = true := by
  decide +kernel

private theorem receipt791 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨791, by decide⟩ cache791 partial791 = true := by
  decide +kernel

private theorem receipt790 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨790, by decide⟩ cache790 partial790 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![791,792,793,794])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1746450307375859 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt791
  · exact receipt792
  · exact receipt793
  · exact receipt794

private theorem receipt789 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨789, by decide⟩ cache789 partial789 = true := by
  decide +kernel

private theorem receipt788 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨788, by decide⟩ cache788 partial788 = true := by
  decide +kernel

private theorem receipt787 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨787, by decide⟩ cache787 partial787 = true := by
  decide +kernel

private theorem receipt786 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨786, by decide⟩ cache786 partial786 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![787,788,789,790])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1737652066345586 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt787
  · exact receipt788
  · exact receipt789
  · exact receipt790

private theorem receipt785 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨785, by decide⟩ cache785 partial785 = true := by
  decide +kernel

theorem receipt784 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨784, by decide⟩ cache784 partial784 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![785,786,795,800])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1759645519864369 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt785
  · exact receipt786
  · exact receipt795
  · exact receipt800

theorem receipt783 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨783, by decide⟩ cache783 partial783 = true := by
  decide +kernel

theorem receipt782 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨782, by decide⟩ cache782 partial782 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock28
