/- Isolated complete Raw029 candidate. Not installed, elaborated, kernel
checked or performance accepted. All 128 original Accepted and all 128 original
CanonicalResponse types are retained. Each decision checks memoNodes with its
own original prefixCache and prefixPartial, then transports to the unchanged
original checker. No original Raw029 acceptance theorem is imported. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalNodeMemo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.FullNodeMemoRaw029
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
  (CanonicalResponse response_of_raw)
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem raw_cut_03712 : EJMOriginalReplayAssembly.Accepted 14 278563 ⟨117038, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117038, by decide⟩
    (prefixCache 14 278563) (prefixPartial 14 278563)).symm.trans (by
      decide +kernel)

theorem response_cut_03712 : CanonicalResponse ⟨14, 2, 0, 117038, 278563, 1673, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117038, 278563, 1673, 4096⟩ (by decide) (by decide) raw_cut_03712

theorem raw_cut_03713 : EJMOriginalReplayAssembly.Accepted 14 278564 ⟨117047, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117047, by decide⟩
    (prefixCache 14 278564) (prefixPartial 14 278564)).symm.trans (by
      decide +kernel)

theorem response_cut_03713 : CanonicalResponse ⟨14, 2, 0, 117047, 278564, 709, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117047, 278564, 709, 4096⟩ (by decide) (by decide) raw_cut_03713

theorem raw_cut_03714 : EJMOriginalReplayAssembly.Accepted 14 278565 ⟨117088, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117088, by decide⟩
    (prefixCache 14 278565) (prefixPartial 14 278565)).symm.trans (by
      decide +kernel)

theorem response_cut_03714 : CanonicalResponse ⟨14, 2, 0, 117088, 278565, 1477, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117088, 278565, 1477, 4096⟩ (by decide) (by decide) raw_cut_03714

theorem raw_cut_03715 : EJMOriginalReplayAssembly.Accepted 14 278566 ⟨117118, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117118, by decide⟩
    (prefixCache 14 278566) (prefixPartial 14 278566)).symm.trans (by
      decide +kernel)

theorem response_cut_03715 : CanonicalResponse ⟨14, 2, 0, 117118, 278566, 1253, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117118, 278566, 1253, 4096⟩ (by decide) (by decide) raw_cut_03715

theorem raw_cut_03716 : EJMOriginalReplayAssembly.Accepted 14 278567 ⟨117142, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117142, by decide⟩
    (prefixCache 14 278567) (prefixPartial 14 278567)).symm.trans (by
      decide +kernel)

theorem response_cut_03716 : CanonicalResponse ⟨14, 2, 0, 117142, 278567, 1121, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117142, 278567, 1121, 4096⟩ (by decide) (by decide) raw_cut_03716

theorem raw_cut_03717 : EJMOriginalReplayAssembly.Accepted 13 69642 ⟨117193, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117193, by decide⟩
    (prefixCache 13 69642) (prefixPartial 13 69642)).symm.trans (by
      decide +kernel)

theorem response_cut_03717 : CanonicalResponse ⟨13, 2, 0, 117193, 69642, 2461, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117193, 69642, 2461, 16384⟩ (by decide) (by decide) raw_cut_03717

theorem raw_cut_03718 : EJMOriginalReplayAssembly.Accepted 13 69643 ⟨117232, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117232, by decide⟩
    (prefixCache 13 69643) (prefixPartial 13 69643)).symm.trans (by
      decide +kernel)

theorem response_cut_03718 : CanonicalResponse ⟨13, 2, 0, 117232, 69643, 1353, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117232, 69643, 1353, 16384⟩ (by decide) (by decide) raw_cut_03718

theorem raw_cut_03719 : EJMOriginalReplayAssembly.Accepted 12 17411 ⟨893, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨893, by decide⟩
    (prefixCache 12 17411) (prefixPartial 12 17411)).symm.trans (by
      decide +kernel)

theorem response_cut_03719 : CanonicalResponse ⟨12, 1, 0, 893, 17411, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 893, 17411, 1, 65536⟩ (by decide) (by decide) raw_cut_03719

theorem raw_cut_03720 : EJMOriginalReplayAssembly.Accepted 12 17412 ⟨895, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨895, by decide⟩
    (prefixCache 12 17412) (prefixPartial 12 17412)).symm.trans (by
      decide +kernel)

theorem response_cut_03720 : CanonicalResponse ⟨12, 1, 0, 895, 17412, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 895, 17412, 1, 65536⟩ (by decide) (by decide) raw_cut_03720

theorem raw_cut_03721 : EJMOriginalReplayAssembly.Accepted 13 69652 ⟨117306, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117306, by decide⟩
    (prefixCache 13 69652) (prefixPartial 13 69652)).symm.trans (by
      decide +kernel)

theorem response_cut_03721 : CanonicalResponse ⟨13, 2, 0, 117306, 69652, 2277, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117306, 69652, 2277, 16384⟩ (by decide) (by decide) raw_cut_03721

theorem raw_cut_03722 : EJMOriginalReplayAssembly.Accepted 13 69653 ⟨117365, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117365, by decide⟩
    (prefixCache 13 69653) (prefixPartial 13 69653)).symm.trans (by
      decide +kernel)

theorem response_cut_03722 : CanonicalResponse ⟨13, 2, 0, 117365, 69653, 1489, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117365, 69653, 1489, 16384⟩ (by decide) (by decide) raw_cut_03722

theorem raw_cut_03723 : EJMOriginalReplayAssembly.Accepted 13 69654 ⟨117387, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117387, by decide⟩
    (prefixCache 13 69654) (prefixPartial 13 69654)).symm.trans (by
      decide +kernel)

theorem response_cut_03723 : CanonicalResponse ⟨13, 2, 0, 117387, 69654, 593, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117387, 69654, 593, 16384⟩ (by decide) (by decide) raw_cut_03723

theorem raw_cut_03724 : EJMOriginalReplayAssembly.Accepted 13 69655 ⟨414, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨414, by decide⟩
    (prefixCache 13 69655) (prefixPartial 13 69655)).symm.trans (by
      decide +kernel)

theorem response_cut_03724 : CanonicalResponse ⟨13, 1, 0, 414, 69655, 1, 16384⟩ :=
  response_of_raw ⟨13, 1, 0, 414, 69655, 1, 16384⟩ (by decide) (by decide) raw_cut_03724

theorem raw_cut_03725 : EJMOriginalReplayAssembly.Accepted 14 278624 ⟨117436, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117436, by decide⟩
    (prefixCache 14 278624) (prefixPartial 14 278624)).symm.trans (by
      decide +kernel)

theorem response_cut_03725 : CanonicalResponse ⟨14, 2, 0, 117436, 278624, 1265, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117436, 278624, 1265, 4096⟩ (by decide) (by decide) raw_cut_03725

theorem raw_cut_03726 : EJMOriginalReplayAssembly.Accepted 14 278625 ⟨117472, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117472, by decide⟩
    (prefixCache 14 278625) (prefixPartial 14 278625)).symm.trans (by
      decide +kernel)

theorem response_cut_03726 : CanonicalResponse ⟨14, 2, 0, 117472, 278625, 1641, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117472, 278625, 1641, 4096⟩ (by decide) (by decide) raw_cut_03726

theorem raw_cut_03727 : EJMOriginalReplayAssembly.Accepted 14 278626 ⟨117500, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117500, by decide⟩
    (prefixCache 14 278626) (prefixPartial 14 278626)).symm.trans (by
      decide +kernel)

theorem response_cut_03727 : CanonicalResponse ⟨14, 2, 0, 117500, 278626, 1397, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117500, 278626, 1397, 4096⟩ (by decide) (by decide) raw_cut_03727

theorem raw_cut_03728 : EJMOriginalReplayAssembly.Accepted 14 278627 ⟨117530, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117530, by decide⟩
    (prefixCache 14 278627) (prefixPartial 14 278627)).symm.trans (by
      decide +kernel)

theorem response_cut_03728 : CanonicalResponse ⟨14, 2, 0, 117530, 278627, 1453, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117530, 278627, 1453, 4096⟩ (by decide) (by decide) raw_cut_03728

theorem raw_cut_03729 : EJMOriginalReplayAssembly.Accepted 14 278628 ⟨117575, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117575, by decide⟩
    (prefixCache 14 278628) (prefixPartial 14 278628)).symm.trans (by
      decide +kernel)

theorem response_cut_03729 : CanonicalResponse ⟨14, 2, 0, 117575, 278628, 1377, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117575, 278628, 1377, 4096⟩ (by decide) (by decide) raw_cut_03729

theorem raw_cut_03730 : EJMOriginalReplayAssembly.Accepted 14 278629 ⟨117637, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117637, by decide⟩
    (prefixCache 14 278629) (prefixPartial 14 278629)).symm.trans (by
      decide +kernel)

theorem response_cut_03730 : CanonicalResponse ⟨14, 2, 0, 117637, 278629, 1593, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117637, 278629, 1593, 4096⟩ (by decide) (by decide) raw_cut_03730

theorem raw_cut_03731 : EJMOriginalReplayAssembly.Accepted 14 278630 ⟨117677, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117677, by decide⟩
    (prefixCache 14 278630) (prefixPartial 14 278630)).symm.trans (by
      decide +kernel)

theorem response_cut_03731 : CanonicalResponse ⟨14, 2, 0, 117677, 278630, 1269, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117677, 278630, 1269, 4096⟩ (by decide) (by decide) raw_cut_03731

theorem raw_cut_03732 : EJMOriginalReplayAssembly.Accepted 14 278631 ⟨117710, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117710, by decide⟩
    (prefixCache 14 278631) (prefixPartial 14 278631)).symm.trans (by
      decide +kernel)

theorem response_cut_03732 : CanonicalResponse ⟨14, 2, 0, 117710, 278631, 1097, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117710, 278631, 1097, 4096⟩ (by decide) (by decide) raw_cut_03732

theorem raw_cut_03733 : EJMOriginalReplayAssembly.Accepted 13 69658 ⟨117791, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117791, by decide⟩
    (prefixCache 13 69658) (prefixPartial 13 69658)).symm.trans (by
      decide +kernel)

theorem response_cut_03733 : CanonicalResponse ⟨13, 2, 0, 117791, 69658, 3021, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117791, 69658, 3021, 16384⟩ (by decide) (by decide) raw_cut_03733

theorem raw_cut_03734 : EJMOriginalReplayAssembly.Accepted 13 69659 ⟨117833, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨117833, by decide⟩
    (prefixCache 13 69659) (prefixPartial 13 69659)).symm.trans (by
      decide +kernel)

theorem response_cut_03734 : CanonicalResponse ⟨13, 2, 0, 117833, 69659, 1497, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 117833, 69659, 1497, 16384⟩ (by decide) (by decide) raw_cut_03734

theorem raw_cut_03735 : EJMOriginalReplayAssembly.Accepted 12 17415 ⟨893, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨893, by decide⟩
    (prefixCache 12 17415) (prefixPartial 12 17415)).symm.trans (by
      decide +kernel)

theorem response_cut_03735 : CanonicalResponse ⟨12, 1, 0, 893, 17415, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 893, 17415, 1, 65536⟩ (by decide) (by decide) raw_cut_03735

theorem raw_cut_03736 : EJMOriginalReplayAssembly.Accepted 12 17416 ⟨895, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨895, by decide⟩
    (prefixCache 12 17416) (prefixPartial 12 17416)).symm.trans (by
      decide +kernel)

theorem response_cut_03736 : CanonicalResponse ⟨12, 1, 0, 895, 17416, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 895, 17416, 1, 65536⟩ (by decide) (by decide) raw_cut_03736

theorem raw_cut_03737 : EJMOriginalReplayAssembly.Accepted 12 17417 ⟨895, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨895, by decide⟩
    (prefixCache 12 17417) (prefixPartial 12 17417)).symm.trans (by
      decide +kernel)

theorem response_cut_03737 : CanonicalResponse ⟨12, 1, 0, 895, 17417, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 895, 17417, 1, 65536⟩ (by decide) (by decide) raw_cut_03737

theorem raw_cut_03738 : EJMOriginalReplayAssembly.Accepted 14 278688 ⟨117857, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117857, by decide⟩
    (prefixCache 14 278688) (prefixPartial 14 278688)).symm.trans (by
      decide +kernel)

theorem response_cut_03738 : CanonicalResponse ⟨14, 2, 0, 117857, 278688, 361, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117857, 278688, 361, 4096⟩ (by decide) (by decide) raw_cut_03738

theorem raw_cut_03739 : EJMOriginalReplayAssembly.Accepted 14 278689 ⟨117914, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117914, by decide⟩
    (prefixCache 14 278689) (prefixPartial 14 278689)).symm.trans (by
      decide +kernel)

theorem response_cut_03739 : CanonicalResponse ⟨14, 2, 0, 117914, 278689, 1549, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117914, 278689, 1549, 4096⟩ (by decide) (by decide) raw_cut_03739

theorem raw_cut_03740 : EJMOriginalReplayAssembly.Accepted 14 278690 ⟨117943, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117943, by decide⟩
    (prefixCache 14 278690) (prefixPartial 14 278690)).symm.trans (by
      decide +kernel)

theorem response_cut_03740 : CanonicalResponse ⟨14, 2, 0, 117943, 278690, 1161, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117943, 278690, 1161, 4096⟩ (by decide) (by decide) raw_cut_03740

theorem raw_cut_03741 : EJMOriginalReplayAssembly.Accepted 14 278691 ⟨117985, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨117985, by decide⟩
    (prefixCache 14 278691) (prefixPartial 14 278691)).symm.trans (by
      decide +kernel)

theorem response_cut_03741 : CanonicalResponse ⟨14, 2, 0, 117985, 278691, 1149, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 117985, 278691, 1149, 4096⟩ (by decide) (by decide) raw_cut_03741

theorem raw_cut_03742 : EJMOriginalReplayAssembly.Accepted 13 69673 ⟨118103, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118103, by decide⟩
    (prefixCache 13 69673) (prefixPartial 13 69673)).symm.trans (by
      decide +kernel)

theorem response_cut_03742 : CanonicalResponse ⟨13, 2, 0, 118103, 69673, 2761, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118103, 69673, 2761, 16384⟩ (by decide) (by decide) raw_cut_03742

theorem raw_cut_03743 : EJMOriginalReplayAssembly.Accepted 13 69674 ⟨118128, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118128, by decide⟩
    (prefixCache 13 69674) (prefixPartial 13 69674)).symm.trans (by
      decide +kernel)

theorem response_cut_03743 : CanonicalResponse ⟨13, 2, 0, 118128, 69674, 701, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118128, 69674, 701, 16384⟩ (by decide) (by decide) raw_cut_03743

theorem raw_cut_03744 : EJMOriginalReplayAssembly.Accepted 13 69675 ⟨118136, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118136, by decide⟩
    (prefixCache 13 69675) (prefixPartial 13 69675)).symm.trans (by
      decide +kernel)

theorem response_cut_03744 : CanonicalResponse ⟨13, 2, 0, 118136, 69675, 149, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118136, 69675, 149, 16384⟩ (by decide) (by decide) raw_cut_03744

theorem raw_cut_03745 : EJMOriginalReplayAssembly.Accepted 14 278704 ⟨118152, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨118152, by decide⟩
    (prefixCache 14 278704) (prefixPartial 14 278704)).symm.trans (by
      decide +kernel)

theorem response_cut_03745 : CanonicalResponse ⟨14, 2, 0, 118152, 278704, 261, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 118152, 278704, 261, 4096⟩ (by decide) (by decide) raw_cut_03745

theorem raw_cut_03746 : EJMOriginalReplayAssembly.Accepted 14 278705 ⟨118205, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨118205, by decide⟩
    (prefixCache 14 278705) (prefixPartial 14 278705)).symm.trans (by
      decide +kernel)

theorem response_cut_03746 : CanonicalResponse ⟨14, 2, 0, 118205, 278705, 1857, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 118205, 278705, 1857, 4096⟩ (by decide) (by decide) raw_cut_03746

theorem raw_cut_03747 : EJMOriginalReplayAssembly.Accepted 14 278706 ⟨118249, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨118249, by decide⟩
    (prefixCache 14 278706) (prefixPartial 14 278706)).symm.trans (by
      decide +kernel)

theorem response_cut_03747 : CanonicalResponse ⟨14, 2, 0, 118249, 278706, 1433, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 118249, 278706, 1433, 4096⟩ (by decide) (by decide) raw_cut_03747

theorem raw_cut_03748 : EJMOriginalReplayAssembly.Accepted 14 278707 ⟨118293, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨118293, by decide⟩
    (prefixCache 14 278707) (prefixPartial 14 278707)).symm.trans (by
      decide +kernel)

theorem response_cut_03748 : CanonicalResponse ⟨14, 2, 0, 118293, 278707, 1321, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 118293, 278707, 1321, 4096⟩ (by decide) (by decide) raw_cut_03748

theorem raw_cut_03749 : EJMOriginalReplayAssembly.Accepted 13 69677 ⟨118431, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118431, by decide⟩
    (prefixCache 13 69677) (prefixPartial 13 69677)).symm.trans (by
      decide +kernel)

theorem response_cut_03749 : CanonicalResponse ⟨13, 2, 0, 118431, 69677, 2977, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118431, 69677, 2977, 16384⟩ (by decide) (by decide) raw_cut_03749

theorem raw_cut_03750 : EJMOriginalReplayAssembly.Accepted 13 69678 ⟨118470, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118470, by decide⟩
    (prefixCache 13 69678) (prefixPartial 13 69678)).symm.trans (by
      decide +kernel)

theorem response_cut_03750 : CanonicalResponse ⟨13, 2, 0, 118470, 69678, 689, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118470, 69678, 689, 16384⟩ (by decide) (by decide) raw_cut_03750

theorem raw_cut_03751 : EJMOriginalReplayAssembly.Accepted 13 69679 ⟨118485, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118485, by decide⟩
    (prefixCache 13 69679) (prefixPartial 13 69679)).symm.trans (by
      decide +kernel)

theorem response_cut_03751 : CanonicalResponse ⟨13, 2, 0, 118485, 69679, 157, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118485, 69679, 157, 16384⟩ (by decide) (by decide) raw_cut_03751

theorem raw_cut_03752 : EJMOriginalReplayAssembly.Accepted 11 4355 ⟨1736, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨1736, by decide⟩
    (prefixCache 11 4355) (prefixPartial 11 4355)).symm.trans (by
      decide +kernel)

theorem response_cut_03752 : CanonicalResponse ⟨11, 1, 0, 1736, 4355, 1, 262144⟩ :=
  response_of_raw ⟨11, 1, 0, 1736, 4355, 1, 262144⟩ (by decide) (by decide) raw_cut_03752

theorem raw_cut_03753 : EJMOriginalReplayAssembly.Accepted 12 17424 ⟨118489, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨118489, by decide⟩
    (prefixCache 12 17424) (prefixPartial 12 17424)).symm.trans (by
      decide +kernel)

theorem response_cut_03753 : CanonicalResponse ⟨12, 1, 0, 118489, 17424, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 118489, 17424, 1, 65536⟩ (by decide) (by decide) raw_cut_03753

theorem raw_cut_03754 : EJMOriginalReplayAssembly.Accepted 12 17425 ⟨118641, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨118641, by decide⟩
    (prefixCache 12 17425) (prefixPartial 12 17425)).symm.trans (by
      decide +kernel)

theorem response_cut_03754 : CanonicalResponse ⟨12, 2, 0, 118641, 17425, 2425, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 118641, 17425, 2425, 65536⟩ (by decide) (by decide) raw_cut_03754

theorem raw_cut_03755 : EJMOriginalReplayAssembly.Accepted 13 69704 ⟨118715, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118715, by decide⟩
    (prefixCache 13 69704) (prefixPartial 13 69704)).symm.trans (by
      decide +kernel)

theorem response_cut_03755 : CanonicalResponse ⟨13, 2, 0, 118715, 69704, 2673, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118715, 69704, 2673, 16384⟩ (by decide) (by decide) raw_cut_03755

theorem raw_cut_03756 : EJMOriginalReplayAssembly.Accepted 13 69705 ⟨118769, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118769, by decide⟩
    (prefixCache 13 69705) (prefixPartial 13 69705)).symm.trans (by
      decide +kernel)

theorem response_cut_03756 : CanonicalResponse ⟨13, 2, 0, 118769, 69705, 2249, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118769, 69705, 2249, 16384⟩ (by decide) (by decide) raw_cut_03756

theorem raw_cut_03757 : EJMOriginalReplayAssembly.Accepted 13 69706 ⟨118800, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118800, by decide⟩
    (prefixCache 13 69706) (prefixPartial 13 69706)).symm.trans (by
      decide +kernel)

theorem response_cut_03757 : CanonicalResponse ⟨13, 2, 0, 118800, 69706, 1501, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118800, 69706, 1501, 16384⟩ (by decide) (by decide) raw_cut_03757

theorem raw_cut_03758 : EJMOriginalReplayAssembly.Accepted 13 69707 ⟨118818, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨118818, by decide⟩
    (prefixCache 13 69707) (prefixPartial 13 69707)).symm.trans (by
      decide +kernel)

theorem response_cut_03758 : CanonicalResponse ⟨13, 2, 0, 118818, 69707, 921, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 118818, 69707, 921, 16384⟩ (by decide) (by decide) raw_cut_03758

theorem raw_cut_03759 : EJMOriginalReplayAssembly.Accepted 12 17427 ⟨893, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨893, by decide⟩
    (prefixCache 12 17427) (prefixPartial 12 17427)).symm.trans (by
      decide +kernel)

theorem response_cut_03759 : CanonicalResponse ⟨12, 1, 0, 893, 17427, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 893, 17427, 1, 65536⟩ (by decide) (by decide) raw_cut_03759

theorem raw_cut_03760 : EJMOriginalReplayAssembly.Accepted 12 17428 ⟨119014, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨119014, by decide⟩
    (prefixCache 12 17428) (prefixPartial 12 17428)).symm.trans (by
      decide +kernel)

theorem response_cut_03760 : CanonicalResponse ⟨12, 2, 0, 119014, 17428, 3585, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 119014, 17428, 3585, 65536⟩ (by decide) (by decide) raw_cut_03760

theorem raw_cut_03761 : EJMOriginalReplayAssembly.Accepted 13 69716 ⟨119054, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119054, by decide⟩
    (prefixCache 13 69716) (prefixPartial 13 69716)).symm.trans (by
      decide +kernel)

theorem response_cut_03761 : CanonicalResponse ⟨13, 2, 0, 119054, 69716, 1521, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119054, 69716, 1521, 16384⟩ (by decide) (by decide) raw_cut_03761

theorem raw_cut_03762 : EJMOriginalReplayAssembly.Accepted 13 69717 ⟨119112, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119112, by decide⟩
    (prefixCache 13 69717) (prefixPartial 13 69717)).symm.trans (by
      decide +kernel)

theorem response_cut_03762 : CanonicalResponse ⟨13, 2, 0, 119112, 69717, 1709, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119112, 69717, 1709, 16384⟩ (by decide) (by decide) raw_cut_03762

theorem raw_cut_03763 : EJMOriginalReplayAssembly.Accepted 13 69718 ⟨119149, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119149, by decide⟩
    (prefixCache 13 69718) (prefixPartial 13 69718)).symm.trans (by
      decide +kernel)

theorem response_cut_03763 : CanonicalResponse ⟨13, 2, 0, 119149, 69718, 1897, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119149, 69718, 1897, 16384⟩ (by decide) (by decide) raw_cut_03763

theorem raw_cut_03764 : EJMOriginalReplayAssembly.Accepted 13 69719 ⟨414, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨414, by decide⟩
    (prefixCache 13 69719) (prefixPartial 13 69719)).symm.trans (by
      decide +kernel)

theorem response_cut_03764 : CanonicalResponse ⟨13, 1, 0, 414, 69719, 1, 16384⟩ :=
  response_of_raw ⟨13, 1, 0, 414, 69719, 1, 16384⟩ (by decide) (by decide) raw_cut_03764

theorem raw_cut_03765 : EJMOriginalReplayAssembly.Accepted 13 69720 ⟨119268, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119268, by decide⟩
    (prefixCache 13 69720) (prefixPartial 13 69720)).symm.trans (by
      decide +kernel)

theorem response_cut_03765 : CanonicalResponse ⟨13, 2, 0, 119268, 69720, 3657, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119268, 69720, 3657, 16384⟩ (by decide) (by decide) raw_cut_03765

theorem raw_cut_03766 : EJMOriginalReplayAssembly.Accepted 13 69721 ⟨119401, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119401, by decide⟩
    (prefixCache 13 69721) (prefixPartial 13 69721)).symm.trans (by
      decide +kernel)

theorem response_cut_03766 : CanonicalResponse ⟨13, 2, 0, 119401, 69721, 3945, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119401, 69721, 3945, 16384⟩ (by decide) (by decide) raw_cut_03766

theorem raw_cut_03767 : EJMOriginalReplayAssembly.Accepted 13 69722 ⟨119440, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119440, by decide⟩
    (prefixCache 13 69722) (prefixPartial 13 69722)).symm.trans (by
      decide +kernel)

theorem response_cut_03767 : CanonicalResponse ⟨13, 2, 0, 119440, 69722, 2261, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119440, 69722, 2261, 16384⟩ (by decide) (by decide) raw_cut_03767

theorem raw_cut_03768 : EJMOriginalReplayAssembly.Accepted 13 69723 ⟨119473, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119473, by decide⟩
    (prefixCache 13 69723) (prefixPartial 13 69723)).symm.trans (by
      decide +kernel)

theorem response_cut_03768 : CanonicalResponse ⟨13, 2, 0, 119473, 69723, 1229, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119473, 69723, 1229, 16384⟩ (by decide) (by decide) raw_cut_03768

theorem raw_cut_03769 : EJMOriginalReplayAssembly.Accepted 12 17431 ⟨893, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨893, by decide⟩
    (prefixCache 12 17431) (prefixPartial 12 17431)).symm.trans (by
      decide +kernel)

theorem response_cut_03769 : CanonicalResponse ⟨12, 1, 0, 893, 17431, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 893, 17431, 1, 65536⟩ (by decide) (by decide) raw_cut_03769

theorem raw_cut_03770 : EJMOriginalReplayAssembly.Accepted 13 69728 ⟨119513, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119513, by decide⟩
    (prefixCache 13 69728) (prefixPartial 13 69728)).symm.trans (by
      decide +kernel)

theorem response_cut_03770 : CanonicalResponse ⟨13, 2, 0, 119513, 69728, 1289, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119513, 69728, 1289, 16384⟩ (by decide) (by decide) raw_cut_03770

theorem raw_cut_03771 : EJMOriginalReplayAssembly.Accepted 13 69729 ⟨119554, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119554, by decide⟩
    (prefixCache 13 69729) (prefixPartial 13 69729)).symm.trans (by
      decide +kernel)

theorem response_cut_03771 : CanonicalResponse ⟨13, 2, 0, 119554, 69729, 2097, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119554, 69729, 2097, 16384⟩ (by decide) (by decide) raw_cut_03771

theorem raw_cut_03772 : EJMOriginalReplayAssembly.Accepted 13 69730 ⟨119576, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119576, by decide⟩
    (prefixCache 13 69730) (prefixPartial 13 69730)).symm.trans (by
      decide +kernel)

theorem response_cut_03772 : CanonicalResponse ⟨13, 2, 0, 119576, 69730, 1789, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119576, 69730, 1789, 16384⟩ (by decide) (by decide) raw_cut_03772

theorem raw_cut_03773 : EJMOriginalReplayAssembly.Accepted 13 69731 ⟨119589, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119589, by decide⟩
    (prefixCache 13 69731) (prefixPartial 13 69731)).symm.trans (by
      decide +kernel)

theorem response_cut_03773 : CanonicalResponse ⟨13, 2, 0, 119589, 69731, 997, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119589, 69731, 997, 16384⟩ (by decide) (by decide) raw_cut_03773

theorem raw_cut_03774 : EJMOriginalReplayAssembly.Accepted 13 69732 ⟨119636, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119636, by decide⟩
    (prefixCache 13 69732) (prefixPartial 13 69732)).symm.trans (by
      decide +kernel)

theorem response_cut_03774 : CanonicalResponse ⟨13, 2, 0, 119636, 69732, 1985, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119636, 69732, 1985, 16384⟩ (by decide) (by decide) raw_cut_03774

theorem raw_cut_03775 : EJMOriginalReplayAssembly.Accepted 13 69733 ⟨119682, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119682, by decide⟩
    (prefixCache 13 69733) (prefixPartial 13 69733)).symm.trans (by
      decide +kernel)

theorem response_cut_03775 : CanonicalResponse ⟨13, 2, 0, 119682, 69733, 1941, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119682, 69733, 1941, 16384⟩ (by decide) (by decide) raw_cut_03775

theorem raw_cut_03776 : EJMOriginalReplayAssembly.Accepted 13 69734 ⟨119705, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119705, by decide⟩
    (prefixCache 13 69734) (prefixPartial 13 69734)).symm.trans (by
      decide +kernel)

theorem response_cut_03776 : CanonicalResponse ⟨13, 2, 0, 119705, 69734, 1817, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119705, 69734, 1817, 16384⟩ (by decide) (by decide) raw_cut_03776

theorem raw_cut_03777 : EJMOriginalReplayAssembly.Accepted 13 69735 ⟨119717, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119717, by decide⟩
    (prefixCache 13 69735) (prefixPartial 13 69735)).symm.trans (by
      decide +kernel)

theorem response_cut_03777 : CanonicalResponse ⟨13, 2, 0, 119717, 69735, 993, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119717, 69735, 993, 16384⟩ (by decide) (by decide) raw_cut_03777

theorem raw_cut_03778 : EJMOriginalReplayAssembly.Accepted 13 69736 ⟨119757, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119757, by decide⟩
    (prefixCache 13 69736) (prefixPartial 13 69736)).symm.trans (by
      decide +kernel)

theorem response_cut_03778 : CanonicalResponse ⟨13, 2, 0, 119757, 69736, 1673, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119757, 69736, 1673, 16384⟩ (by decide) (by decide) raw_cut_03778

theorem raw_cut_03779 : EJMOriginalReplayAssembly.Accepted 13 69737 ⟨119823, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119823, by decide⟩
    (prefixCache 13 69737) (prefixPartial 13 69737)).symm.trans (by
      decide +kernel)

theorem response_cut_03779 : CanonicalResponse ⟨13, 2, 0, 119823, 69737, 2081, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119823, 69737, 2081, 16384⟩ (by decide) (by decide) raw_cut_03779

theorem raw_cut_03780 : EJMOriginalReplayAssembly.Accepted 13 69738 ⟨119848, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119848, by decide⟩
    (prefixCache 13 69738) (prefixPartial 13 69738)).symm.trans (by
      decide +kernel)

theorem response_cut_03780 : CanonicalResponse ⟨13, 2, 0, 119848, 69738, 1425, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119848, 69738, 1425, 16384⟩ (by decide) (by decide) raw_cut_03780

theorem raw_cut_03781 : EJMOriginalReplayAssembly.Accepted 13 69739 ⟨119863, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119863, by decide⟩
    (prefixCache 13 69739) (prefixPartial 13 69739)).symm.trans (by
      decide +kernel)

theorem response_cut_03781 : CanonicalResponse ⟨13, 2, 0, 119863, 69739, 965, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119863, 69739, 965, 16384⟩ (by decide) (by decide) raw_cut_03781

theorem raw_cut_03782 : EJMOriginalReplayAssembly.Accepted 13 69740 ⟨119899, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119899, by decide⟩
    (prefixCache 13 69740) (prefixPartial 13 69740)).symm.trans (by
      decide +kernel)

theorem response_cut_03782 : CanonicalResponse ⟨13, 2, 0, 119899, 69740, 1833, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119899, 69740, 1833, 16384⟩ (by decide) (by decide) raw_cut_03782

theorem raw_cut_03783 : EJMOriginalReplayAssembly.Accepted 13 69741 ⟨119954, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119954, by decide⟩
    (prefixCache 13 69741) (prefixPartial 13 69741)).symm.trans (by
      decide +kernel)

theorem response_cut_03783 : CanonicalResponse ⟨13, 2, 0, 119954, 69741, 2113, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119954, 69741, 2113, 16384⟩ (by decide) (by decide) raw_cut_03783

theorem raw_cut_03784 : EJMOriginalReplayAssembly.Accepted 13 69742 ⟨119977, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119977, by decide⟩
    (prefixCache 13 69742) (prefixPartial 13 69742)).symm.trans (by
      decide +kernel)

theorem response_cut_03784 : CanonicalResponse ⟨13, 2, 0, 119977, 69742, 1693, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119977, 69742, 1693, 16384⟩ (by decide) (by decide) raw_cut_03784

theorem raw_cut_03785 : EJMOriginalReplayAssembly.Accepted 13 69743 ⟨119994, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨119994, by decide⟩
    (prefixCache 13 69743) (prefixPartial 13 69743)).symm.trans (by
      decide +kernel)

theorem response_cut_03785 : CanonicalResponse ⟨13, 2, 0, 119994, 69743, 897, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 119994, 69743, 897, 16384⟩ (by decide) (by decide) raw_cut_03785

theorem raw_cut_03786 : EJMOriginalReplayAssembly.Accepted 11 4359 ⟨1736, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨1736, by decide⟩
    (prefixCache 11 4359) (prefixPartial 11 4359)).symm.trans (by
      decide +kernel)

theorem response_cut_03786 : CanonicalResponse ⟨11, 1, 0, 1736, 4359, 1, 262144⟩ :=
  response_of_raw ⟨11, 1, 0, 1736, 4359, 1, 262144⟩ (by decide) (by decide) raw_cut_03786

theorem raw_cut_03787 : EJMOriginalReplayAssembly.Accepted 12 17440 ⟨118489, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨118489, by decide⟩
    (prefixCache 12 17440) (prefixPartial 12 17440)).symm.trans (by
      decide +kernel)

theorem response_cut_03787 : CanonicalResponse ⟨12, 1, 0, 118489, 17440, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 118489, 17440, 1, 65536⟩ (by decide) (by decide) raw_cut_03787

theorem raw_cut_03788 : EJMOriginalReplayAssembly.Accepted 12 17441 ⟨119998, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨119998, by decide⟩
    (prefixCache 12 17441) (prefixPartial 12 17441)).symm.trans (by
      decide +kernel)

theorem response_cut_03788 : CanonicalResponse ⟨12, 1, 0, 119998, 17441, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 119998, 17441, 1, 65536⟩ (by decide) (by decide) raw_cut_03788

theorem raw_cut_03789 : EJMOriginalReplayAssembly.Accepted 12 17442 ⟨120209, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨120209, by decide⟩
    (prefixCache 12 17442) (prefixPartial 12 17442)).symm.trans (by
      decide +kernel)

theorem response_cut_03789 : CanonicalResponse ⟨12, 2, 0, 120209, 17442, 3937, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 120209, 17442, 3937, 65536⟩ (by decide) (by decide) raw_cut_03789

theorem raw_cut_03790 : EJMOriginalReplayAssembly.Accepted 12 17443 ⟨120429, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨120429, by decide⟩
    (prefixCache 12 17443) (prefixPartial 12 17443)).symm.trans (by
      decide +kernel)

theorem response_cut_03790 : CanonicalResponse ⟨12, 2, 0, 120429, 17443, 3629, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 120429, 17443, 3629, 65536⟩ (by decide) (by decide) raw_cut_03790

theorem raw_cut_03791 : EJMOriginalReplayAssembly.Accepted 12 17444 ⟨118489, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨118489, by decide⟩
    (prefixCache 12 17444) (prefixPartial 12 17444)).symm.trans (by
      decide +kernel)

theorem response_cut_03791 : CanonicalResponse ⟨12, 1, 0, 118489, 17444, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 118489, 17444, 1, 65536⟩ (by decide) (by decide) raw_cut_03791

theorem raw_cut_03792 : EJMOriginalReplayAssembly.Accepted 13 69780 ⟨120471, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120471, by decide⟩
    (prefixCache 13 69780) (prefixPartial 13 69780)).symm.trans (by
      decide +kernel)

theorem response_cut_03792 : CanonicalResponse ⟨13, 2, 0, 120471, 69780, 1189, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120471, 69780, 1189, 16384⟩ (by decide) (by decide) raw_cut_03792

theorem raw_cut_03793 : EJMOriginalReplayAssembly.Accepted 13 69781 ⟨120522, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120522, by decide⟩
    (prefixCache 13 69781) (prefixPartial 13 69781)).symm.trans (by
      decide +kernel)

theorem response_cut_03793 : CanonicalResponse ⟨13, 2, 0, 120522, 69781, 1813, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120522, 69781, 1813, 16384⟩ (by decide) (by decide) raw_cut_03793

theorem raw_cut_03794 : EJMOriginalReplayAssembly.Accepted 13 69782 ⟨120550, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120550, by decide⟩
    (prefixCache 13 69782) (prefixPartial 13 69782)).symm.trans (by
      decide +kernel)

theorem response_cut_03794 : CanonicalResponse ⟨13, 2, 0, 120550, 69782, 1397, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120550, 69782, 1397, 16384⟩ (by decide) (by decide) raw_cut_03794

theorem raw_cut_03795 : EJMOriginalReplayAssembly.Accepted 13 69783 ⟨120567, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120567, by decide⟩
    (prefixCache 13 69783) (prefixPartial 13 69783)).symm.trans (by
      decide +kernel)

theorem response_cut_03795 : CanonicalResponse ⟨13, 2, 0, 120567, 69783, 781, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120567, 69783, 781, 16384⟩ (by decide) (by decide) raw_cut_03795

theorem raw_cut_03796 : EJMOriginalReplayAssembly.Accepted 13 69784 ⟨120605, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120605, by decide⟩
    (prefixCache 13 69784) (prefixPartial 13 69784)).symm.trans (by
      decide +kernel)

theorem response_cut_03796 : CanonicalResponse ⟨13, 2, 0, 120605, 69784, 1297, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120605, 69784, 1297, 16384⟩ (by decide) (by decide) raw_cut_03796

theorem raw_cut_03797 : EJMOriginalReplayAssembly.Accepted 13 69785 ⟨120679, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120679, by decide⟩
    (prefixCache 13 69785) (prefixPartial 13 69785)).symm.trans (by
      decide +kernel)

theorem response_cut_03797 : CanonicalResponse ⟨13, 2, 0, 120679, 69785, 2141, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120679, 69785, 2141, 16384⟩ (by decide) (by decide) raw_cut_03797

theorem raw_cut_03798 : EJMOriginalReplayAssembly.Accepted 13 69786 ⟨120710, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120710, by decide⟩
    (prefixCache 13 69786) (prefixPartial 13 69786)).symm.trans (by
      decide +kernel)

theorem response_cut_03798 : CanonicalResponse ⟨13, 2, 0, 120710, 69786, 1337, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120710, 69786, 1337, 16384⟩ (by decide) (by decide) raw_cut_03798

theorem raw_cut_03799 : EJMOriginalReplayAssembly.Accepted 13 69787 ⟨120727, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120727, by decide⟩
    (prefixCache 13 69787) (prefixPartial 13 69787)).symm.trans (by
      decide +kernel)

theorem response_cut_03799 : CanonicalResponse ⟨13, 2, 0, 120727, 69787, 845, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120727, 69787, 845, 16384⟩ (by decide) (by decide) raw_cut_03799

theorem raw_cut_03800 : EJMOriginalReplayAssembly.Accepted 13 69788 ⟨120768, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120768, by decide⟩
    (prefixCache 13 69788) (prefixPartial 13 69788)).symm.trans (by
      decide +kernel)

theorem response_cut_03800 : CanonicalResponse ⟨13, 2, 0, 120768, 69788, 1141, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120768, 69788, 1141, 16384⟩ (by decide) (by decide) raw_cut_03800

theorem raw_cut_03801 : EJMOriginalReplayAssembly.Accepted 13 69789 ⟨120831, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120831, by decide⟩
    (prefixCache 13 69789) (prefixPartial 13 69789)).symm.trans (by
      decide +kernel)

theorem response_cut_03801 : CanonicalResponse ⟨13, 2, 0, 120831, 69789, 1953, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120831, 69789, 1953, 16384⟩ (by decide) (by decide) raw_cut_03801

theorem raw_cut_03802 : EJMOriginalReplayAssembly.Accepted 13 69790 ⟨120862, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120862, by decide⟩
    (prefixCache 13 69790) (prefixPartial 13 69790)).symm.trans (by
      decide +kernel)

theorem response_cut_03802 : CanonicalResponse ⟨13, 2, 0, 120862, 69790, 1329, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120862, 69790, 1329, 16384⟩ (by decide) (by decide) raw_cut_03802

theorem raw_cut_03803 : EJMOriginalReplayAssembly.Accepted 13 69791 ⟨120877, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨120877, by decide⟩
    (prefixCache 13 69791) (prefixPartial 13 69791)).symm.trans (by
      decide +kernel)

theorem response_cut_03803 : CanonicalResponse ⟨13, 2, 0, 120877, 69791, 689, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 120877, 69791, 689, 16384⟩ (by decide) (by decide) raw_cut_03803

theorem raw_cut_03804 : EJMOriginalReplayAssembly.Accepted 12 17448 ⟨120987, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨120987, by decide⟩
    (prefixCache 12 17448) (prefixPartial 12 17448)).symm.trans (by
      decide +kernel)

theorem response_cut_03804 : CanonicalResponse ⟨12, 2, 0, 120987, 17448, 2841, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 120987, 17448, 2841, 65536⟩ (by decide) (by decide) raw_cut_03804

theorem raw_cut_03805 : EJMOriginalReplayAssembly.Accepted 13 69796 ⟨121013, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨121013, by decide⟩
    (prefixCache 13 69796) (prefixPartial 13 69796)).symm.trans (by
      decide +kernel)

theorem response_cut_03805 : CanonicalResponse ⟨13, 2, 0, 121013, 69796, 869, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 121013, 69796, 869, 16384⟩ (by decide) (by decide) raw_cut_03805

theorem raw_cut_03806 : EJMOriginalReplayAssembly.Accepted 13 69797 ⟨121053, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨121053, by decide⟩
    (prefixCache 13 69797) (prefixPartial 13 69797)).symm.trans (by
      decide +kernel)

theorem response_cut_03806 : CanonicalResponse ⟨13, 2, 0, 121053, 69797, 1629, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 121053, 69797, 1629, 16384⟩ (by decide) (by decide) raw_cut_03806

theorem raw_cut_03807 : EJMOriginalReplayAssembly.Accepted 13 69798 ⟨121079, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨121079, by decide⟩
    (prefixCache 13 69798) (prefixPartial 13 69798)).symm.trans (by
      decide +kernel)

theorem response_cut_03807 : CanonicalResponse ⟨13, 2, 0, 121079, 69798, 1201, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 121079, 69798, 1201, 16384⟩ (by decide) (by decide) raw_cut_03807

theorem raw_cut_03808 : EJMOriginalReplayAssembly.Accepted 13 69799 ⟨121094, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨121094, by decide⟩
    (prefixCache 13 69799) (prefixPartial 13 69799)).symm.trans (by
      decide +kernel)

theorem response_cut_03808 : CanonicalResponse ⟨13, 2, 0, 121094, 69799, 761, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 121094, 69799, 761, 16384⟩ (by decide) (by decide) raw_cut_03808

theorem raw_cut_03809 : EJMOriginalReplayAssembly.Accepted 12 17450 ⟨121205, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121205, by decide⟩
    (prefixCache 12 17450) (prefixPartial 12 17450)).symm.trans (by
      decide +kernel)

theorem response_cut_03809 : CanonicalResponse ⟨12, 2, 0, 121205, 17450, 4009, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121205, 17450, 4009, 65536⟩ (by decide) (by decide) raw_cut_03809

theorem raw_cut_03810 : EJMOriginalReplayAssembly.Accepted 12 17451 ⟨121315, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121315, by decide⟩
    (prefixCache 12 17451) (prefixPartial 12 17451)).symm.trans (by
      decide +kernel)

theorem response_cut_03810 : CanonicalResponse ⟨12, 2, 0, 121315, 17451, 3989, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121315, 17451, 3989, 65536⟩ (by decide) (by decide) raw_cut_03810

theorem raw_cut_03811 : EJMOriginalReplayAssembly.Accepted 12 17452 ⟨121444, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121444, by decide⟩
    (prefixCache 12 17452) (prefixPartial 12 17452)).symm.trans (by
      decide +kernel)

theorem response_cut_03811 : CanonicalResponse ⟨12, 2, 0, 121444, 17452, 2501, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121444, 17452, 2501, 65536⟩ (by decide) (by decide) raw_cut_03811

theorem raw_cut_03812 : EJMOriginalReplayAssembly.Accepted 12 17453 ⟨121565, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121565, by decide⟩
    (prefixCache 12 17453) (prefixPartial 12 17453)).symm.trans (by
      decide +kernel)

theorem response_cut_03812 : CanonicalResponse ⟨12, 2, 0, 121565, 17453, 3813, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121565, 17453, 3813, 65536⟩ (by decide) (by decide) raw_cut_03812

theorem raw_cut_03813 : EJMOriginalReplayAssembly.Accepted 12 17454 ⟨121714, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121714, by decide⟩
    (prefixCache 12 17454) (prefixPartial 12 17454)).symm.trans (by
      decide +kernel)

theorem response_cut_03813 : CanonicalResponse ⟨12, 2, 0, 121714, 17454, 3725, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121714, 17454, 3725, 65536⟩ (by decide) (by decide) raw_cut_03813

theorem raw_cut_03814 : EJMOriginalReplayAssembly.Accepted 12 17455 ⟨121822, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨121822, by decide⟩
    (prefixCache 12 17455) (prefixPartial 12 17455)).symm.trans (by
      decide +kernel)

theorem response_cut_03814 : CanonicalResponse ⟨12, 2, 0, 121822, 17455, 3033, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 121822, 17455, 3033, 65536⟩ (by decide) (by decide) raw_cut_03814

theorem raw_cut_03815 : EJMOriginalReplayAssembly.Accepted 10 1091 ⟨3440, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 10) ⟨3440, by decide⟩
    (prefixCache 10 1091) (prefixPartial 10 1091)).symm.trans (by
      decide +kernel)

theorem response_cut_03815 : CanonicalResponse ⟨10, 1, 0, 3440, 1091, 1, 1048576⟩ :=
  response_of_raw ⟨10, 1, 0, 3440, 1091, 1, 1048576⟩ (by decide) (by decide) raw_cut_03815

theorem raw_cut_03816 : EJMOriginalReplayAssembly.Accepted 10 1092 ⟨3442, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 10) ⟨3442, by decide⟩
    (prefixCache 10 1092) (prefixPartial 10 1092)).symm.trans (by
      decide +kernel)

theorem response_cut_03816 : CanonicalResponse ⟨10, 1, 0, 3442, 1092, 1, 1048576⟩ :=
  response_of_raw ⟨10, 1, 0, 3442, 1092, 1, 1048576⟩ (by decide) (by decide) raw_cut_03816

theorem raw_cut_03817 : EJMOriginalReplayAssembly.Accepted 11 4372 ⟨121826, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨121826, by decide⟩
    (prefixCache 11 4372) (prefixPartial 11 4372)).symm.trans (by
      decide +kernel)

theorem response_cut_03817 : CanonicalResponse ⟨11, 1, 0, 121826, 4372, 1, 262144⟩ :=
  response_of_raw ⟨11, 1, 0, 121826, 4372, 1, 262144⟩ (by decide) (by decide) raw_cut_03817

theorem raw_cut_03818 : EJMOriginalReplayAssembly.Accepted 11 4373 ⟨122053, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨122053, by decide⟩
    (prefixCache 11 4373) (prefixPartial 11 4373)).symm.trans (by
      decide +kernel)

theorem response_cut_03818 : CanonicalResponse ⟨11, 2, 0, 122053, 4373, 3621, 262144⟩ :=
  response_of_raw ⟨11, 2, 0, 122053, 4373, 3621, 262144⟩ (by decide) (by decide) raw_cut_03818

theorem raw_cut_03819 : EJMOriginalReplayAssembly.Accepted 11 4374 ⟨122213, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨122213, by decide⟩
    (prefixCache 11 4374) (prefixPartial 11 4374)).symm.trans (by
      decide +kernel)

theorem response_cut_03819 : CanonicalResponse ⟨11, 2, 0, 122213, 4374, 2805, 262144⟩ :=
  response_of_raw ⟨11, 2, 0, 122213, 4374, 2805, 262144⟩ (by decide) (by decide) raw_cut_03819

theorem raw_cut_03820 : EJMOriginalReplayAssembly.Accepted 11 4375 ⟨1736, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨1736, by decide⟩
    (prefixCache 11 4375) (prefixPartial 11 4375)).symm.trans (by
      decide +kernel)

theorem response_cut_03820 : CanonicalResponse ⟨11, 1, 0, 1736, 4375, 1, 262144⟩ :=
  response_of_raw ⟨11, 1, 0, 1736, 4375, 1, 262144⟩ (by decide) (by decide) raw_cut_03820

theorem raw_cut_03821 : EJMOriginalReplayAssembly.Accepted 11 4376 ⟨121826, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨121826, by decide⟩
    (prefixCache 11 4376) (prefixPartial 11 4376)).symm.trans (by
      decide +kernel)

theorem response_cut_03821 : CanonicalResponse ⟨11, 1, 0, 121826, 4376, 1, 262144⟩ :=
  response_of_raw ⟨11, 1, 0, 121826, 4376, 1, 262144⟩ (by decide) (by decide) raw_cut_03821

theorem raw_cut_03822 : EJMOriginalReplayAssembly.Accepted 11 4377 ⟨122410, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨122410, by decide⟩
    (prefixCache 11 4377) (prefixPartial 11 4377)).symm.trans (by
      decide +kernel)

theorem response_cut_03822 : CanonicalResponse ⟨11, 2, 0, 122410, 4377, 2817, 262144⟩ :=
  response_of_raw ⟨11, 2, 0, 122410, 4377, 2817, 262144⟩ (by decide) (by decide) raw_cut_03822

theorem raw_cut_03823 : EJMOriginalReplayAssembly.Accepted 12 17512 ⟨122215, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨122215, by decide⟩
    (prefixCache 12 17512) (prefixPartial 12 17512)).symm.trans (by
      decide +kernel)

theorem response_cut_03823 : CanonicalResponse ⟨12, 1, 0, 122215, 17512, 1, 65536⟩ :=
  response_of_raw ⟨12, 1, 0, 122215, 17512, 1, 65536⟩ (by decide) (by decide) raw_cut_03823

theorem raw_cut_03824 : EJMOriginalReplayAssembly.Accepted 12 17513 ⟨122536, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨122536, by decide⟩
    (prefixCache 12 17513) (prefixPartial 12 17513)).symm.trans (by
      decide +kernel)

theorem response_cut_03824 : CanonicalResponse ⟨12, 2, 0, 122536, 17513, 1569, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 122536, 17513, 1569, 65536⟩ (by decide) (by decide) raw_cut_03824

theorem raw_cut_03825 : EJMOriginalReplayAssembly.Accepted 12 17514 ⟨122609, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨122609, by decide⟩
    (prefixCache 12 17514) (prefixPartial 12 17514)).symm.trans (by
      decide +kernel)

theorem response_cut_03825 : CanonicalResponse ⟨12, 2, 0, 122609, 17514, 1585, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 122609, 17514, 1585, 65536⟩ (by decide) (by decide) raw_cut_03825

theorem raw_cut_03826 : EJMOriginalReplayAssembly.Accepted 12 17515 ⟨122660, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨122660, by decide⟩
    (prefixCache 12 17515) (prefixPartial 12 17515)).symm.trans (by
      decide +kernel)

theorem response_cut_03826 : CanonicalResponse ⟨12, 2, 0, 122660, 17515, 1361, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 122660, 17515, 1361, 65536⟩ (by decide) (by decide) raw_cut_03826

theorem raw_cut_03827 : EJMOriginalReplayAssembly.Accepted 11 4379 ⟨122854, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 11) ⟨122854, by decide⟩
    (prefixCache 11 4379) (prefixPartial 11 4379)).symm.trans (by
      decide +kernel)

theorem response_cut_03827 : CanonicalResponse ⟨11, 2, 0, 122854, 4379, 2665, 262144⟩ :=
  response_of_raw ⟨11, 2, 0, 122854, 4379, 2665, 262144⟩ (by decide) (by decide) raw_cut_03827

theorem raw_cut_03828 : EJMOriginalReplayAssembly.Accepted 10 1095 ⟨3440, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 10) ⟨3440, by decide⟩
    (prefixCache 10 1095) (prefixPartial 10 1095)).symm.trans (by
      decide +kernel)

theorem response_cut_03828 : CanonicalResponse ⟨10, 1, 0, 3440, 1095, 1, 1048576⟩ :=
  response_of_raw ⟨10, 1, 0, 3440, 1095, 1, 1048576⟩ (by decide) (by decide) raw_cut_03828

theorem raw_cut_03829 : EJMOriginalReplayAssembly.Accepted 9 274 ⟨122918, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 9) ⟨122918, by decide⟩
    (prefixCache 9 274) (prefixPartial 9 274)).symm.trans (by
      decide +kernel)

theorem response_cut_03829 : CanonicalResponse ⟨9, 2, 0, 122918, 274, 637, 4194304⟩ :=
  response_of_raw ⟨9, 2, 0, 122918, 274, 637, 4194304⟩ (by decide) (by decide) raw_cut_03829

theorem raw_cut_03830 : EJMOriginalReplayAssembly.Accepted 9 275 ⟨4601, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 9) ⟨4601, by decide⟩
    (prefixCache 9 275) (prefixPartial 9 275)).symm.trans (by
      decide +kernel)

theorem response_cut_03830 : CanonicalResponse ⟨9, 1, 0, 4601, 275, 1, 4194304⟩ :=
  response_of_raw ⟨9, 1, 0, 4601, 275, 1, 4194304⟩ (by decide) (by decide) raw_cut_03830

theorem raw_cut_03831 : EJMOriginalReplayAssembly.Accepted 12 17664 ⟨123043, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 12) ⟨123043, by decide⟩
    (prefixCache 12 17664) (prefixPartial 12 17664)).symm.trans (by
      decide +kernel)

theorem response_cut_03831 : CanonicalResponse ⟨12, 2, 0, 123043, 17664, 3481, 65536⟩ :=
  response_of_raw ⟨12, 2, 0, 123043, 17664, 3481, 65536⟩ (by decide) (by decide) raw_cut_03831

theorem raw_cut_03832 : EJMOriginalReplayAssembly.Accepted 13 70660 ⟨123093, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨123093, by decide⟩
    (prefixCache 13 70660) (prefixPartial 13 70660)).symm.trans (by
      decide +kernel)

theorem response_cut_03832 : CanonicalResponse ⟨13, 2, 0, 123093, 70660, 2089, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 123093, 70660, 2089, 16384⟩ (by decide) (by decide) raw_cut_03832

theorem raw_cut_03833 : EJMOriginalReplayAssembly.Accepted 13 70661 ⟨123118, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨123118, by decide⟩
    (prefixCache 13 70661) (prefixPartial 13 70661)).symm.trans (by
      decide +kernel)

theorem response_cut_03833 : CanonicalResponse ⟨13, 2, 0, 123118, 70661, 1421, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 123118, 70661, 1421, 16384⟩ (by decide) (by decide) raw_cut_03833

theorem raw_cut_03834 : EJMOriginalReplayAssembly.Accepted 13 70662 ⟨123140, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨123140, by decide⟩
    (prefixCache 13 70662) (prefixPartial 13 70662)).symm.trans (by
      decide +kernel)

theorem response_cut_03834 : CanonicalResponse ⟨13, 2, 0, 123140, 70662, 1729, 16384⟩ :=
  response_of_raw ⟨13, 2, 0, 123140, 70662, 1729, 16384⟩ (by decide) (by decide) raw_cut_03834

theorem raw_cut_03835 : EJMOriginalReplayAssembly.Accepted 13 70663 ⟨414, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 13) ⟨414, by decide⟩
    (prefixCache 13 70663) (prefixPartial 13 70663)).symm.trans (by
      decide +kernel)

theorem response_cut_03835 : CanonicalResponse ⟨13, 1, 0, 414, 70663, 1, 16384⟩ :=
  response_of_raw ⟨13, 1, 0, 414, 70663, 1, 16384⟩ (by decide) (by decide) raw_cut_03835

theorem raw_cut_03836 : EJMOriginalReplayAssembly.Accepted 14 282656 ⟨123182, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨123182, by decide⟩
    (prefixCache 14 282656) (prefixPartial 14 282656)).symm.trans (by
      decide +kernel)

theorem response_cut_03836 : CanonicalResponse ⟨14, 2, 0, 123182, 282656, 1217, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 123182, 282656, 1217, 4096⟩ (by decide) (by decide) raw_cut_03836

theorem raw_cut_03837 : EJMOriginalReplayAssembly.Accepted 14 282657 ⟨123198, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨123198, by decide⟩
    (prefixCache 14 282657) (prefixPartial 14 282657)).symm.trans (by
      decide +kernel)

theorem response_cut_03837 : CanonicalResponse ⟨14, 2, 0, 123198, 282657, 1089, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 123198, 282657, 1089, 4096⟩ (by decide) (by decide) raw_cut_03837

theorem raw_cut_03838 : EJMOriginalReplayAssembly.Accepted 14 282658 ⟨123220, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨123220, by decide⟩
    (prefixCache 14 282658) (prefixPartial 14 282658)).symm.trans (by
      decide +kernel)

theorem response_cut_03838 : CanonicalResponse ⟨14, 2, 0, 123220, 282658, 1213, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 123220, 282658, 1213, 4096⟩ (by decide) (by decide) raw_cut_03838

theorem raw_cut_03839 : EJMOriginalReplayAssembly.Accepted 14 282659 ⟨123239, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 14) ⟨123239, by decide⟩
    (prefixCache 14 282659) (prefixPartial 14 282659)).symm.trans (by
      decide +kernel)

theorem response_cut_03839 : CanonicalResponse ⟨14, 2, 0, 123239, 282659, 1201, 4096⟩ :=
  response_of_raw ⟨14, 2, 0, 123239, 282659, 1201, 4096⟩ (by decide) (by decide) raw_cut_03839

#print axioms raw_cut_03712
#print axioms response_cut_03712
#print axioms raw_cut_03713
#print axioms response_cut_03713
#print axioms raw_cut_03714
#print axioms response_cut_03714
#print axioms raw_cut_03715
#print axioms response_cut_03715
#print axioms raw_cut_03716
#print axioms response_cut_03716
#print axioms raw_cut_03717
#print axioms response_cut_03717
#print axioms raw_cut_03718
#print axioms response_cut_03718
#print axioms raw_cut_03719
#print axioms response_cut_03719
#print axioms raw_cut_03720
#print axioms response_cut_03720
#print axioms raw_cut_03721
#print axioms response_cut_03721
#print axioms raw_cut_03722
#print axioms response_cut_03722
#print axioms raw_cut_03723
#print axioms response_cut_03723
#print axioms raw_cut_03724
#print axioms response_cut_03724
#print axioms raw_cut_03725
#print axioms response_cut_03725
#print axioms raw_cut_03726
#print axioms response_cut_03726
#print axioms raw_cut_03727
#print axioms response_cut_03727
#print axioms raw_cut_03728
#print axioms response_cut_03728
#print axioms raw_cut_03729
#print axioms response_cut_03729
#print axioms raw_cut_03730
#print axioms response_cut_03730
#print axioms raw_cut_03731
#print axioms response_cut_03731
#print axioms raw_cut_03732
#print axioms response_cut_03732
#print axioms raw_cut_03733
#print axioms response_cut_03733
#print axioms raw_cut_03734
#print axioms response_cut_03734
#print axioms raw_cut_03735
#print axioms response_cut_03735
#print axioms raw_cut_03736
#print axioms response_cut_03736
#print axioms raw_cut_03737
#print axioms response_cut_03737
#print axioms raw_cut_03738
#print axioms response_cut_03738
#print axioms raw_cut_03739
#print axioms response_cut_03739
#print axioms raw_cut_03740
#print axioms response_cut_03740
#print axioms raw_cut_03741
#print axioms response_cut_03741
#print axioms raw_cut_03742
#print axioms response_cut_03742
#print axioms raw_cut_03743
#print axioms response_cut_03743
#print axioms raw_cut_03744
#print axioms response_cut_03744
#print axioms raw_cut_03745
#print axioms response_cut_03745
#print axioms raw_cut_03746
#print axioms response_cut_03746
#print axioms raw_cut_03747
#print axioms response_cut_03747
#print axioms raw_cut_03748
#print axioms response_cut_03748
#print axioms raw_cut_03749
#print axioms response_cut_03749
#print axioms raw_cut_03750
#print axioms response_cut_03750
#print axioms raw_cut_03751
#print axioms response_cut_03751
#print axioms raw_cut_03752
#print axioms response_cut_03752
#print axioms raw_cut_03753
#print axioms response_cut_03753
#print axioms raw_cut_03754
#print axioms response_cut_03754
#print axioms raw_cut_03755
#print axioms response_cut_03755
#print axioms raw_cut_03756
#print axioms response_cut_03756
#print axioms raw_cut_03757
#print axioms response_cut_03757
#print axioms raw_cut_03758
#print axioms response_cut_03758
#print axioms raw_cut_03759
#print axioms response_cut_03759
#print axioms raw_cut_03760
#print axioms response_cut_03760
#print axioms raw_cut_03761
#print axioms response_cut_03761
#print axioms raw_cut_03762
#print axioms response_cut_03762
#print axioms raw_cut_03763
#print axioms response_cut_03763
#print axioms raw_cut_03764
#print axioms response_cut_03764
#print axioms raw_cut_03765
#print axioms response_cut_03765
#print axioms raw_cut_03766
#print axioms response_cut_03766
#print axioms raw_cut_03767
#print axioms response_cut_03767
#print axioms raw_cut_03768
#print axioms response_cut_03768
#print axioms raw_cut_03769
#print axioms response_cut_03769
#print axioms raw_cut_03770
#print axioms response_cut_03770
#print axioms raw_cut_03771
#print axioms response_cut_03771
#print axioms raw_cut_03772
#print axioms response_cut_03772
#print axioms raw_cut_03773
#print axioms response_cut_03773
#print axioms raw_cut_03774
#print axioms response_cut_03774
#print axioms raw_cut_03775
#print axioms response_cut_03775
#print axioms raw_cut_03776
#print axioms response_cut_03776
#print axioms raw_cut_03777
#print axioms response_cut_03777
#print axioms raw_cut_03778
#print axioms response_cut_03778
#print axioms raw_cut_03779
#print axioms response_cut_03779
#print axioms raw_cut_03780
#print axioms response_cut_03780
#print axioms raw_cut_03781
#print axioms response_cut_03781
#print axioms raw_cut_03782
#print axioms response_cut_03782
#print axioms raw_cut_03783
#print axioms response_cut_03783
#print axioms raw_cut_03784
#print axioms response_cut_03784
#print axioms raw_cut_03785
#print axioms response_cut_03785
#print axioms raw_cut_03786
#print axioms response_cut_03786
#print axioms raw_cut_03787
#print axioms response_cut_03787
#print axioms raw_cut_03788
#print axioms response_cut_03788
#print axioms raw_cut_03789
#print axioms response_cut_03789
#print axioms raw_cut_03790
#print axioms response_cut_03790
#print axioms raw_cut_03791
#print axioms response_cut_03791
#print axioms raw_cut_03792
#print axioms response_cut_03792
#print axioms raw_cut_03793
#print axioms response_cut_03793
#print axioms raw_cut_03794
#print axioms response_cut_03794
#print axioms raw_cut_03795
#print axioms response_cut_03795
#print axioms raw_cut_03796
#print axioms response_cut_03796
#print axioms raw_cut_03797
#print axioms response_cut_03797
#print axioms raw_cut_03798
#print axioms response_cut_03798
#print axioms raw_cut_03799
#print axioms response_cut_03799
#print axioms raw_cut_03800
#print axioms response_cut_03800
#print axioms raw_cut_03801
#print axioms response_cut_03801
#print axioms raw_cut_03802
#print axioms response_cut_03802
#print axioms raw_cut_03803
#print axioms response_cut_03803
#print axioms raw_cut_03804
#print axioms response_cut_03804
#print axioms raw_cut_03805
#print axioms response_cut_03805
#print axioms raw_cut_03806
#print axioms response_cut_03806
#print axioms raw_cut_03807
#print axioms response_cut_03807
#print axioms raw_cut_03808
#print axioms response_cut_03808
#print axioms raw_cut_03809
#print axioms response_cut_03809
#print axioms raw_cut_03810
#print axioms response_cut_03810
#print axioms raw_cut_03811
#print axioms response_cut_03811
#print axioms raw_cut_03812
#print axioms response_cut_03812
#print axioms raw_cut_03813
#print axioms response_cut_03813
#print axioms raw_cut_03814
#print axioms response_cut_03814
#print axioms raw_cut_03815
#print axioms response_cut_03815
#print axioms raw_cut_03816
#print axioms response_cut_03816
#print axioms raw_cut_03817
#print axioms response_cut_03817
#print axioms raw_cut_03818
#print axioms response_cut_03818
#print axioms raw_cut_03819
#print axioms response_cut_03819
#print axioms raw_cut_03820
#print axioms response_cut_03820
#print axioms raw_cut_03821
#print axioms response_cut_03821
#print axioms raw_cut_03822
#print axioms response_cut_03822
#print axioms raw_cut_03823
#print axioms response_cut_03823
#print axioms raw_cut_03824
#print axioms response_cut_03824
#print axioms raw_cut_03825
#print axioms response_cut_03825
#print axioms raw_cut_03826
#print axioms response_cut_03826
#print axioms raw_cut_03827
#print axioms response_cut_03827
#print axioms raw_cut_03828
#print axioms response_cut_03828
#print axioms raw_cut_03829
#print axioms response_cut_03829
#print axioms raw_cut_03830
#print axioms response_cut_03830
#print axioms raw_cut_03831
#print axioms response_cut_03831
#print axioms raw_cut_03832
#print axioms response_cut_03832
#print axioms raw_cut_03833
#print axioms response_cut_03833
#print axioms raw_cut_03834
#print axioms response_cut_03834
#print axioms raw_cut_03835
#print axioms response_cut_03835
#print axioms raw_cut_03836
#print axioms response_cut_03836
#print axioms raw_cut_03837
#print axioms response_cut_03837
#print axioms raw_cut_03838
#print axioms response_cut_03838
#print axioms raw_cut_03839
#print axioms response_cut_03839

end D5.S3.Quantum.Entanglement.EJM.FullNodeMemoRaw029
