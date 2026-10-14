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

theorem receipt626 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨626, by decide⟩ cache626 partial626 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock10
