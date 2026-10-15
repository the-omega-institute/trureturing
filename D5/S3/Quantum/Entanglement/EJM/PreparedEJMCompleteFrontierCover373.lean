/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover372
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35812 : selected 9 ⟨943460, by decide⟩
    (prefixPartial 12 287359) = some ⟨12, 2, 0, 943460, 287359, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_287359_943460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287359 ⟨943460, by decide⟩ :=
  accepted_of_selected 12 287359 ⟨943460, by decide⟩ ⟨12, 2, 0, 943460, 287359, 1853, 65536⟩
    (by decide) selected_cut_35812

theorem unmarked_context_11_71839_943461 : frontier 10 ⟨943461, by decide⟩
    (prefixCache 11 71839) (prefixPartial 11 71839) = false := by
  decide +kernel

theorem node_context_11_71839_943461 : EJMOriginalGlobalDAGData.nodes 10 ⟨943461, by decide⟩ =
    .split (coordinate 11) (![⟨943409, by decide⟩,⟨896706, by decide⟩,⟨943431, by decide⟩,⟨943460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71839_943461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71839 ⟨943461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71839
    ⟨943461, by decide⟩ (by decide) (![⟨943409, by decide⟩,⟨896706, by decide⟩,⟨943431, by decide⟩,⟨943460, by decide⟩]) unmarked_context_11_71839_943461 node_context_11_71839_943461
  intro a
  fin_cases a
  · exact context_12_287356_943409
  · exact context_12_287357_896706
  · exact context_12_287358_943431
  · exact context_12_287359_943460

theorem unmarked_context_10_17959_943462 : frontier 11 ⟨943462, by decide⟩
    (prefixCache 10 17959) (prefixPartial 10 17959) = false := by
  decide +kernel

theorem node_context_10_17959_943462 : EJMOriginalGlobalDAGData.nodes 11 ⟨943462, by decide⟩ =
    .split (coordinate 10) (![⟨943264, by decide⟩,⟨943334, by decide⟩,⟨943387, by decide⟩,⟨943461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17959_943462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17959 ⟨943462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17959
    ⟨943462, by decide⟩ (by decide) (![⟨943264, by decide⟩,⟨943334, by decide⟩,⟨943387, by decide⟩,⟨943461, by decide⟩]) unmarked_context_10_17959_943462 node_context_10_17959_943462
  intro a
  fin_cases a
  · exact context_11_71836_943264
  · exact context_11_71837_943334
  · exact context_11_71838_943387
  · exact context_11_71839_943461

theorem unmarked_context_9_4489_943463 : frontier 12 ⟨943463, by decide⟩
    (prefixCache 9 4489) (prefixPartial 9 4489) = false := by
  decide +kernel

theorem node_context_9_4489_943463 : EJMOriginalGlobalDAGData.nodes 12 ⟨943463, by decide⟩ =
    .split (coordinate 9) (![⟨942885, by decide⟩,⟨893098, by decide⟩,⟨943198, by decide⟩,⟨943462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4489_943463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4489 ⟨943463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4489
    ⟨943463, by decide⟩ (by decide) (![⟨942885, by decide⟩,⟨893098, by decide⟩,⟨943198, by decide⟩,⟨943462, by decide⟩]) unmarked_context_9_4489_943463 node_context_9_4489_943463
  intro a
  fin_cases a
  · exact context_10_17956_942885
  · exact context_10_17957_893098
  · exact context_10_17958_943198
  · exact context_10_17959_943462

theorem selected_cut_35813 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71840) = some ⟨11, 1, 0, 907917, 71840, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71840_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71840 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71840 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71840, 1, 262144⟩
    (by decide) selected_cut_35813

theorem selected_cut_35814 : selected 9 ⟨943489, by decide⟩
    (prefixPartial 12 287364) = some ⟨12, 2, 0, 943489, 287364, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_287364_943489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287364 ⟨943489, by decide⟩ :=
  accepted_of_selected 12 287364 ⟨943489, by decide⟩ ⟨12, 2, 0, 943489, 287364, 1825, 65536⟩
    (by decide) selected_cut_35814

theorem selected_cut_35815 : selected 9 ⟨943513, by decide⟩
    (prefixPartial 12 287365) = some ⟨12, 2, 0, 943513, 287365, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_287365_943513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287365 ⟨943513, by decide⟩ :=
  accepted_of_selected 12 287365 ⟨943513, by decide⟩ ⟨12, 2, 0, 943513, 287365, 1553, 65536⟩
    (by decide) selected_cut_35815

theorem selected_cut_35816 : selected 9 ⟨943535, by decide⟩
    (prefixPartial 12 287366) = some ⟨12, 2, 0, 943535, 287366, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_287366_943535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287366 ⟨943535, by decide⟩ :=
  accepted_of_selected 12 287366 ⟨943535, by decide⟩ ⟨12, 2, 0, 943535, 287366, 1625, 65536⟩
    (by decide) selected_cut_35816

theorem selected_cut_35817 : selected 9 ⟨943559, by decide⟩
    (prefixPartial 12 287367) = some ⟨12, 2, 0, 943559, 287367, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_287367_943559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287367 ⟨943559, by decide⟩ :=
  accepted_of_selected 12 287367 ⟨943559, by decide⟩ ⟨12, 2, 0, 943559, 287367, 1645, 65536⟩
    (by decide) selected_cut_35817

theorem unmarked_context_11_71841_943560 : frontier 10 ⟨943560, by decide⟩
    (prefixCache 11 71841) (prefixPartial 11 71841) = false := by
  decide +kernel

theorem node_context_11_71841_943560 : EJMOriginalGlobalDAGData.nodes 10 ⟨943560, by decide⟩ =
    .split (coordinate 11) (![⟨943489, by decide⟩,⟨943513, by decide⟩,⟨943535, by decide⟩,⟨943559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71841_943560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71841 ⟨943560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71841
    ⟨943560, by decide⟩ (by decide) (![⟨943489, by decide⟩,⟨943513, by decide⟩,⟨943535, by decide⟩,⟨943559, by decide⟩]) unmarked_context_11_71841_943560 node_context_11_71841_943560
  intro a
  fin_cases a
  · exact context_12_287364_943489
  · exact context_12_287365_943513
  · exact context_12_287366_943535
  · exact context_12_287367_943559

theorem selected_cut_35818 : selected 9 ⟨943584, by decide⟩
    (prefixPartial 12 287368) = some ⟨12, 2, 0, 943584, 287368, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_287368_943584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287368 ⟨943584, by decide⟩ :=
  accepted_of_selected 12 287368 ⟨943584, by decide⟩ ⟨12, 2, 0, 943584, 287368, 1861, 65536⟩
    (by decide) selected_cut_35818

theorem selected_cut_35819 : selected 9 ⟨943608, by decide⟩
    (prefixPartial 12 287369) = some ⟨12, 2, 0, 943608, 287369, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_287369_943608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287369 ⟨943608, by decide⟩ :=
  accepted_of_selected 12 287369 ⟨943608, by decide⟩ ⟨12, 2, 0, 943608, 287369, 1681, 65536⟩
    (by decide) selected_cut_35819

theorem selected_cut_35820 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287370) = some ⟨12, 1, 0, 893903, 287370, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287370_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287370 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287370 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287370, 1, 65536⟩
    (by decide) selected_cut_35820

theorem selected_cut_35821 : selected 9 ⟨943635, by decide⟩
    (prefixPartial 12 287371) = some ⟨12, 2, 0, 943635, 287371, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_287371_943635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287371 ⟨943635, by decide⟩ :=
  accepted_of_selected 12 287371 ⟨943635, by decide⟩ ⟨12, 2, 0, 943635, 287371, 1781, 65536⟩
    (by decide) selected_cut_35821

theorem unmarked_context_11_71842_943636 : frontier 10 ⟨943636, by decide⟩
    (prefixCache 11 71842) (prefixPartial 11 71842) = false := by
  decide +kernel

theorem node_context_11_71842_943636 : EJMOriginalGlobalDAGData.nodes 10 ⟨943636, by decide⟩ =
    .split (coordinate 11) (![⟨943584, by decide⟩,⟨943608, by decide⟩,⟨893903, by decide⟩,⟨943635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71842_943636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71842 ⟨943636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71842
    ⟨943636, by decide⟩ (by decide) (![⟨943584, by decide⟩,⟨943608, by decide⟩,⟨893903, by decide⟩,⟨943635, by decide⟩]) unmarked_context_11_71842_943636 node_context_11_71842_943636
  intro a
  fin_cases a
  · exact context_12_287368_943584
  · exact context_12_287369_943608
  · exact context_12_287370_893903
  · exact context_12_287371_943635

theorem selected_cut_35822 : selected 9 ⟨943661, by decide⟩
    (prefixPartial 12 287372) = some ⟨12, 2, 0, 943661, 287372, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_287372_943661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287372 ⟨943661, by decide⟩ :=
  accepted_of_selected 12 287372 ⟨943661, by decide⟩ ⟨12, 2, 0, 943661, 287372, 1769, 65536⟩
    (by decide) selected_cut_35822

theorem selected_cut_35823 : selected 9 ⟨943682, by decide⟩
    (prefixPartial 12 287373) = some ⟨12, 2, 0, 943682, 287373, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_287373_943682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287373 ⟨943682, by decide⟩ :=
  accepted_of_selected 12 287373 ⟨943682, by decide⟩ ⟨12, 2, 0, 943682, 287373, 1505, 65536⟩
    (by decide) selected_cut_35823

theorem selected_cut_35824 : selected 9 ⟨943707, by decide⟩
    (prefixPartial 12 287374) = some ⟨12, 2, 0, 943707, 287374, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_287374_943707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287374 ⟨943707, by decide⟩ :=
  accepted_of_selected 12 287374 ⟨943707, by decide⟩ ⟨12, 2, 0, 943707, 287374, 1485, 65536⟩
    (by decide) selected_cut_35824

theorem selected_cut_35825 : selected 9 ⟨943731, by decide⟩
    (prefixPartial 12 287375) = some ⟨12, 2, 0, 943731, 287375, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_287375_943731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287375 ⟨943731, by decide⟩ :=
  accepted_of_selected 12 287375 ⟨943731, by decide⟩ ⟨12, 2, 0, 943731, 287375, 1613, 65536⟩
    (by decide) selected_cut_35825

theorem unmarked_context_11_71843_943732 : frontier 10 ⟨943732, by decide⟩
    (prefixCache 11 71843) (prefixPartial 11 71843) = false := by
  decide +kernel

theorem node_context_11_71843_943732 : EJMOriginalGlobalDAGData.nodes 10 ⟨943732, by decide⟩ =
    .split (coordinate 11) (![⟨943661, by decide⟩,⟨943682, by decide⟩,⟨943707, by decide⟩,⟨943731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71843_943732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71843 ⟨943732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71843
    ⟨943732, by decide⟩ (by decide) (![⟨943661, by decide⟩,⟨943682, by decide⟩,⟨943707, by decide⟩,⟨943731, by decide⟩]) unmarked_context_11_71843_943732 node_context_11_71843_943732
  intro a
  fin_cases a
  · exact context_12_287372_943661
  · exact context_12_287373_943682
  · exact context_12_287374_943707
  · exact context_12_287375_943731

theorem unmarked_context_10_17960_943733 : frontier 11 ⟨943733, by decide⟩
    (prefixCache 10 17960) (prefixPartial 10 17960) = false := by
  decide +kernel

theorem node_context_10_17960_943733 : EJMOriginalGlobalDAGData.nodes 11 ⟨943733, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨943560, by decide⟩,⟨943636, by decide⟩,⟨943732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17960_943733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17960 ⟨943733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17960
    ⟨943733, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨943560, by decide⟩,⟨943636, by decide⟩,⟨943732, by decide⟩]) unmarked_context_10_17960_943733 node_context_10_17960_943733
  intro a
  fin_cases a
  · exact context_11_71840_907917
  · exact context_11_71841_943560
  · exact context_11_71842_943636
  · exact context_11_71843_943732

theorem selected_cut_35826 : selected 9 ⟨943750, by decide⟩
    (prefixPartial 12 287376) = some ⟨12, 2, 0, 943750, 287376, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_287376_943750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287376 ⟨943750, by decide⟩ :=
  accepted_of_selected 12 287376 ⟨943750, by decide⟩ ⟨12, 2, 0, 943750, 287376, 1329, 65536⟩
    (by decide) selected_cut_35826

theorem selected_cut_35827 : selected 9 ⟨943771, by decide⟩
    (prefixPartial 12 287377) = some ⟨12, 2, 0, 943771, 287377, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_287377_943771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287377 ⟨943771, by decide⟩ :=
  accepted_of_selected 12 287377 ⟨943771, by decide⟩ ⟨12, 2, 0, 943771, 287377, 1381, 65536⟩
    (by decide) selected_cut_35827

theorem selected_cut_35828 : selected 9 ⟨943793, by decide⟩
    (prefixPartial 12 287378) = some ⟨12, 2, 0, 943793, 287378, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_287378_943793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287378 ⟨943793, by decide⟩ :=
  accepted_of_selected 12 287378 ⟨943793, by decide⟩ ⟨12, 2, 0, 943793, 287378, 1285, 65536⟩
    (by decide) selected_cut_35828

theorem selected_cut_35829 : selected 9 ⟨943813, by decide⟩
    (prefixPartial 12 287379) = some ⟨12, 2, 0, 943813, 287379, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_287379_943813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287379 ⟨943813, by decide⟩ :=
  accepted_of_selected 12 287379 ⟨943813, by decide⟩ ⟨12, 2, 0, 943813, 287379, 1437, 65536⟩
    (by decide) selected_cut_35829

theorem unmarked_context_11_71844_943814 : frontier 10 ⟨943814, by decide⟩
    (prefixCache 11 71844) (prefixPartial 11 71844) = false := by
  decide +kernel

theorem node_context_11_71844_943814 : EJMOriginalGlobalDAGData.nodes 10 ⟨943814, by decide⟩ =
    .split (coordinate 11) (![⟨943750, by decide⟩,⟨943771, by decide⟩,⟨943793, by decide⟩,⟨943813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71844_943814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71844 ⟨943814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71844
    ⟨943814, by decide⟩ (by decide) (![⟨943750, by decide⟩,⟨943771, by decide⟩,⟨943793, by decide⟩,⟨943813, by decide⟩]) unmarked_context_11_71844_943814 node_context_11_71844_943814
  intro a
  fin_cases a
  · exact context_12_287376_943750
  · exact context_12_287377_943771
  · exact context_12_287378_943793
  · exact context_12_287379_943813

theorem selected_cut_35830 : selected 9 ⟨943831, by decide⟩
    (prefixPartial 12 287380) = some ⟨12, 2, 0, 943831, 287380, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_287380_943831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287380 ⟨943831, by decide⟩ :=
  accepted_of_selected 12 287380 ⟨943831, by decide⟩ ⟨12, 2, 0, 943831, 287380, 1301, 65536⟩
    (by decide) selected_cut_35830

theorem selected_cut_35831 : selected 9 ⟨943852, by decide⟩
    (prefixPartial 12 287381) = some ⟨12, 2, 0, 943852, 287381, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_287381_943852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287381 ⟨943852, by decide⟩ :=
  accepted_of_selected 12 287381 ⟨943852, by decide⟩ ⟨12, 2, 0, 943852, 287381, 1349, 65536⟩
    (by decide) selected_cut_35831

theorem selected_cut_35832 : selected 9 ⟨943869, by decide⟩
    (prefixPartial 12 287382) = some ⟨12, 2, 0, 943869, 287382, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_287382_943869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287382 ⟨943869, by decide⟩ :=
  accepted_of_selected 12 287382 ⟨943869, by decide⟩ ⟨12, 2, 0, 943869, 287382, 1341, 65536⟩
    (by decide) selected_cut_35832

theorem selected_cut_35833 : selected 9 ⟨943889, by decide⟩
    (prefixPartial 12 287383) = some ⟨12, 2, 0, 943889, 287383, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_287383_943889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287383 ⟨943889, by decide⟩ :=
  accepted_of_selected 12 287383 ⟨943889, by decide⟩ ⟨12, 2, 0, 943889, 287383, 1285, 65536⟩
    (by decide) selected_cut_35833

theorem unmarked_context_11_71845_943890 : frontier 10 ⟨943890, by decide⟩
    (prefixCache 11 71845) (prefixPartial 11 71845) = false := by
  decide +kernel

theorem node_context_11_71845_943890 : EJMOriginalGlobalDAGData.nodes 10 ⟨943890, by decide⟩ =
    .split (coordinate 11) (![⟨943831, by decide⟩,⟨943852, by decide⟩,⟨943869, by decide⟩,⟨943889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71845_943890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71845 ⟨943890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71845
    ⟨943890, by decide⟩ (by decide) (![⟨943831, by decide⟩,⟨943852, by decide⟩,⟨943869, by decide⟩,⟨943889, by decide⟩]) unmarked_context_11_71845_943890 node_context_11_71845_943890
  intro a
  fin_cases a
  · exact context_12_287380_943831
  · exact context_12_287381_943852
  · exact context_12_287382_943869
  · exact context_12_287383_943889

theorem selected_cut_35834 : selected 9 ⟨943907, by decide⟩
    (prefixPartial 12 287384) = some ⟨12, 2, 0, 943907, 287384, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_287384_943907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287384 ⟨943907, by decide⟩ :=
  accepted_of_selected 12 287384 ⟨943907, by decide⟩ ⟨12, 2, 0, 943907, 287384, 1321, 65536⟩
    (by decide) selected_cut_35834

theorem selected_cut_35835 : selected 9 ⟨943928, by decide⟩
    (prefixPartial 12 287385) = some ⟨12, 2, 0, 943928, 287385, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_287385_943928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287385 ⟨943928, by decide⟩ :=
  accepted_of_selected 12 287385 ⟨943928, by decide⟩ ⟨12, 2, 0, 943928, 287385, 1437, 65536⟩
    (by decide) selected_cut_35835

theorem selected_cut_35836 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 287386) = some ⟨12, 1, 0, 893903, 287386, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287386_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287386 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 287386 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 287386, 1, 65536⟩
    (by decide) selected_cut_35836

theorem selected_cut_35837 : selected 9 ⟨943945, by decide⟩
    (prefixPartial 12 287387) = some ⟨12, 2, 0, 943945, 287387, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_287387_943945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287387 ⟨943945, by decide⟩ :=
  accepted_of_selected 12 287387 ⟨943945, by decide⟩ ⟨12, 2, 0, 943945, 287387, 1461, 65536⟩
    (by decide) selected_cut_35837

theorem unmarked_context_11_71846_943946 : frontier 10 ⟨943946, by decide⟩
    (prefixCache 11 71846) (prefixPartial 11 71846) = false := by
  decide +kernel

theorem node_context_11_71846_943946 : EJMOriginalGlobalDAGData.nodes 10 ⟨943946, by decide⟩ =
    .split (coordinate 11) (![⟨943907, by decide⟩,⟨943928, by decide⟩,⟨893903, by decide⟩,⟨943945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71846_943946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71846 ⟨943946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71846
    ⟨943946, by decide⟩ (by decide) (![⟨943907, by decide⟩,⟨943928, by decide⟩,⟨893903, by decide⟩,⟨943945, by decide⟩]) unmarked_context_11_71846_943946 node_context_11_71846_943946
  intro a
  fin_cases a
  · exact context_12_287384_943907
  · exact context_12_287385_943928
  · exact context_12_287386_893903
  · exact context_12_287387_943945

theorem selected_cut_35838 : selected 9 ⟨943960, by decide⟩
    (prefixPartial 12 287388) = some ⟨12, 2, 0, 943960, 287388, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_287388_943960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287388 ⟨943960, by decide⟩ :=
  accepted_of_selected 12 287388 ⟨943960, by decide⟩ ⟨12, 2, 0, 943960, 287388, 1269, 65536⟩
    (by decide) selected_cut_35838

theorem selected_cut_35839 : selected 9 ⟨943980, by decide⟩
    (prefixPartial 12 287389) = some ⟨12, 2, 0, 943980, 287389, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_287389_943980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287389 ⟨943980, by decide⟩ :=
  accepted_of_selected 12 287389 ⟨943980, by decide⟩ ⟨12, 2, 0, 943980, 287389, 1265, 65536⟩
    (by decide) selected_cut_35839

theorem selected_cut_35840 : selected 9 ⟨943998, by decide⟩
    (prefixPartial 12 287390) = some ⟨12, 2, 0, 943998, 287390, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_287390_943998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287390 ⟨943998, by decide⟩ :=
  accepted_of_selected 12 287390 ⟨943998, by decide⟩ ⟨12, 2, 0, 943998, 287390, 1249, 65536⟩
    (by decide) selected_cut_35840

theorem selected_cut_35841 : selected 9 ⟨944014, by decide⟩
    (prefixPartial 12 287391) = some ⟨12, 2, 0, 944014, 287391, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_287391_944014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287391 ⟨944014, by decide⟩ :=
  accepted_of_selected 12 287391 ⟨944014, by decide⟩ ⟨12, 2, 0, 944014, 287391, 1337, 65536⟩
    (by decide) selected_cut_35841

theorem unmarked_context_11_71847_944015 : frontier 10 ⟨944015, by decide⟩
    (prefixCache 11 71847) (prefixPartial 11 71847) = false := by
  decide +kernel

theorem node_context_11_71847_944015 : EJMOriginalGlobalDAGData.nodes 10 ⟨944015, by decide⟩ =
    .split (coordinate 11) (![⟨943960, by decide⟩,⟨943980, by decide⟩,⟨943998, by decide⟩,⟨944014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71847_944015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71847 ⟨944015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71847
    ⟨944015, by decide⟩ (by decide) (![⟨943960, by decide⟩,⟨943980, by decide⟩,⟨943998, by decide⟩,⟨944014, by decide⟩]) unmarked_context_11_71847_944015 node_context_11_71847_944015
  intro a
  fin_cases a
  · exact context_12_287388_943960
  · exact context_12_287389_943980
  · exact context_12_287390_943998
  · exact context_12_287391_944014

theorem unmarked_context_10_17961_944016 : frontier 11 ⟨944016, by decide⟩
    (prefixCache 10 17961) (prefixPartial 10 17961) = false := by
  decide +kernel

theorem node_context_10_17961_944016 : EJMOriginalGlobalDAGData.nodes 11 ⟨944016, by decide⟩ =
    .split (coordinate 10) (![⟨943814, by decide⟩,⟨943890, by decide⟩,⟨943946, by decide⟩,⟨944015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17961_944016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17961 ⟨944016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17961
    ⟨944016, by decide⟩ (by decide) (![⟨943814, by decide⟩,⟨943890, by decide⟩,⟨943946, by decide⟩,⟨944015, by decide⟩]) unmarked_context_10_17961_944016 node_context_10_17961_944016
  intro a
  fin_cases a
  · exact context_11_71844_943814
  · exact context_11_71845_943890
  · exact context_11_71846_943946
  · exact context_11_71847_944015

theorem selected_cut_35842 : selected 10 ⟨944055, by decide⟩
    (prefixPartial 11 71848) = some ⟨11, 2, 0, 944055, 71848, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_71848_944055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71848 ⟨944055, by decide⟩ :=
  accepted_of_selected 11 71848 ⟨944055, by decide⟩ ⟨11, 2, 0, 944055, 71848, 3389, 262144⟩
    (by decide) selected_cut_35842

theorem selected_cut_35843 : selected 10 ⟨944093, by decide⟩
    (prefixPartial 11 71849) = some ⟨11, 2, 0, 944093, 71849, 3001, 262144⟩ := by
  decide +kernel

theorem context_11_71849_944093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71849 ⟨944093, by decide⟩ :=
  accepted_of_selected 11 71849 ⟨944093, by decide⟩ ⟨11, 2, 0, 944093, 71849, 3001, 262144⟩
    (by decide) selected_cut_35843

theorem selected_cut_35844 : selected 10 ⟨944128, by decide⟩
    (prefixPartial 11 71850) = some ⟨11, 2, 0, 944128, 71850, 2921, 262144⟩ := by
  decide +kernel

theorem context_11_71850_944128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71850 ⟨944128, by decide⟩ :=
  accepted_of_selected 11 71850 ⟨944128, by decide⟩ ⟨11, 2, 0, 944128, 71850, 2921, 262144⟩
    (by decide) selected_cut_35844

theorem selected_cut_35845 : selected 9 ⟨944143, by decide⟩
    (prefixPartial 12 287404) = some ⟨12, 2, 0, 944143, 287404, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_287404_944143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287404 ⟨944143, by decide⟩ :=
  accepted_of_selected 12 287404 ⟨944143, by decide⟩ ⟨12, 2, 0, 944143, 287404, 1057, 65536⟩
    (by decide) selected_cut_35845

theorem selected_cut_35846 : selected 9 ⟨944161, by decide⟩
    (prefixPartial 12 287405) = some ⟨12, 2, 0, 944161, 287405, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_287405_944161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287405 ⟨944161, by decide⟩ :=
  accepted_of_selected 12 287405 ⟨944161, by decide⟩ ⟨12, 2, 0, 944161, 287405, 1069, 65536⟩
    (by decide) selected_cut_35846

theorem selected_cut_35847 : selected 9 ⟨944174, by decide⟩
    (prefixPartial 12 287406) = some ⟨12, 2, 0, 944174, 287406, 981, 65536⟩ := by
  decide +kernel

theorem context_12_287406_944174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287406 ⟨944174, by decide⟩ :=
  accepted_of_selected 12 287406 ⟨944174, by decide⟩ ⟨12, 2, 0, 944174, 287406, 981, 65536⟩
    (by decide) selected_cut_35847

theorem selected_cut_35848 : selected 9 ⟨944188, by decide⟩
    (prefixPartial 12 287407) = some ⟨12, 2, 0, 944188, 287407, 1005, 65536⟩ := by
  decide +kernel

theorem context_12_287407_944188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287407 ⟨944188, by decide⟩ :=
  accepted_of_selected 12 287407 ⟨944188, by decide⟩ ⟨12, 2, 0, 944188, 287407, 1005, 65536⟩
    (by decide) selected_cut_35848

theorem unmarked_context_11_71851_944189 : frontier 10 ⟨944189, by decide⟩
    (prefixCache 11 71851) (prefixPartial 11 71851) = false := by
  decide +kernel

theorem node_context_11_71851_944189 : EJMOriginalGlobalDAGData.nodes 10 ⟨944189, by decide⟩ =
    .split (coordinate 11) (![⟨944143, by decide⟩,⟨944161, by decide⟩,⟨944174, by decide⟩,⟨944188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71851_944189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71851 ⟨944189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71851
    ⟨944189, by decide⟩ (by decide) (![⟨944143, by decide⟩,⟨944161, by decide⟩,⟨944174, by decide⟩,⟨944188, by decide⟩]) unmarked_context_11_71851_944189 node_context_11_71851_944189
  intro a
  fin_cases a
  · exact context_12_287404_944143
  · exact context_12_287405_944161
  · exact context_12_287406_944174
  · exact context_12_287407_944188

theorem unmarked_context_10_17962_944190 : frontier 11 ⟨944190, by decide⟩
    (prefixCache 10 17962) (prefixPartial 10 17962) = false := by
  decide +kernel

theorem node_context_10_17962_944190 : EJMOriginalGlobalDAGData.nodes 11 ⟨944190, by decide⟩ =
    .split (coordinate 10) (![⟨944055, by decide⟩,⟨944093, by decide⟩,⟨944128, by decide⟩,⟨944189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17962_944190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17962 ⟨944190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17962
    ⟨944190, by decide⟩ (by decide) (![⟨944055, by decide⟩,⟨944093, by decide⟩,⟨944128, by decide⟩,⟨944189, by decide⟩]) unmarked_context_10_17962_944190 node_context_10_17962_944190
  intro a
  fin_cases a
  · exact context_11_71848_944055
  · exact context_11_71849_944093
  · exact context_11_71850_944128
  · exact context_11_71851_944189

theorem selected_cut_35849 : selected 10 ⟨944218, by decide⟩
    (prefixPartial 11 71852) = some ⟨11, 2, 0, 944218, 71852, 3125, 262144⟩ := by
  decide +kernel

theorem context_11_71852_944218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71852 ⟨944218, by decide⟩ :=
  accepted_of_selected 11 71852 ⟨944218, by decide⟩ ⟨11, 2, 0, 944218, 71852, 3125, 262144⟩
    (by decide) selected_cut_35849

theorem selected_cut_35850 : selected 10 ⟨944262, by decide⟩
    (prefixPartial 11 71853) = some ⟨11, 2, 0, 944262, 71853, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_71853_944262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71853 ⟨944262, by decide⟩ :=
  accepted_of_selected 11 71853 ⟨944262, by decide⟩ ⟨11, 2, 0, 944262, 71853, 3149, 262144⟩
    (by decide) selected_cut_35850

theorem selected_cut_35851 : selected 10 ⟨944292, by decide⟩
    (prefixPartial 11 71854) = some ⟨11, 2, 0, 944292, 71854, 2257, 262144⟩ := by
  decide +kernel

theorem context_11_71854_944292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71854 ⟨944292, by decide⟩ :=
  accepted_of_selected 11 71854 ⟨944292, by decide⟩ ⟨11, 2, 0, 944292, 71854, 2257, 262144⟩
    (by decide) selected_cut_35851

theorem selected_cut_35852 : selected 10 ⟨944329, by decide⟩
    (prefixPartial 11 71855) = some ⟨11, 2, 0, 944329, 71855, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_71855_944329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71855 ⟨944329, by decide⟩ :=
  accepted_of_selected 11 71855 ⟨944329, by decide⟩ ⟨11, 2, 0, 944329, 71855, 2845, 262144⟩
    (by decide) selected_cut_35852

theorem unmarked_context_10_17963_944330 : frontier 11 ⟨944330, by decide⟩
    (prefixCache 10 17963) (prefixPartial 10 17963) = false := by
  decide +kernel

theorem node_context_10_17963_944330 : EJMOriginalGlobalDAGData.nodes 11 ⟨944330, by decide⟩ =
    .split (coordinate 10) (![⟨944218, by decide⟩,⟨944262, by decide⟩,⟨944292, by decide⟩,⟨944329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17963_944330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17963 ⟨944330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17963
    ⟨944330, by decide⟩ (by decide) (![⟨944218, by decide⟩,⟨944262, by decide⟩,⟨944292, by decide⟩,⟨944329, by decide⟩]) unmarked_context_10_17963_944330 node_context_10_17963_944330
  intro a
  fin_cases a
  · exact context_11_71852_944218
  · exact context_11_71853_944262
  · exact context_11_71854_944292
  · exact context_11_71855_944329

theorem unmarked_context_9_4490_944331 : frontier 12 ⟨944331, by decide⟩
    (prefixCache 9 4490) (prefixPartial 9 4490) = false := by
  decide +kernel

theorem node_context_9_4490_944331 : EJMOriginalGlobalDAGData.nodes 12 ⟨944331, by decide⟩ =
    .split (coordinate 9) (![⟨943733, by decide⟩,⟨944016, by decide⟩,⟨944190, by decide⟩,⟨944330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4490_944331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4490 ⟨944331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4490
    ⟨944331, by decide⟩ (by decide) (![⟨943733, by decide⟩,⟨944016, by decide⟩,⟨944190, by decide⟩,⟨944330, by decide⟩]) unmarked_context_9_4490_944331 node_context_9_4490_944331
  intro a
  fin_cases a
  · exact context_10_17960_943733
  · exact context_10_17961_944016
  · exact context_10_17962_944190
  · exact context_10_17963_944330

theorem selected_cut_35853 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71856) = some ⟨11, 1, 0, 907917, 71856, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71856_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71856 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71856 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71856, 1, 262144⟩
    (by decide) selected_cut_35853

theorem selected_cut_35854 : selected 10 ⟨944353, by decide⟩
    (prefixPartial 11 71857) = some ⟨11, 2, 0, 944353, 71857, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_71857_944353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71857 ⟨944353, by decide⟩ :=
  accepted_of_selected 11 71857 ⟨944353, by decide⟩ ⟨11, 2, 0, 944353, 71857, 2265, 262144⟩
    (by decide) selected_cut_35854

theorem selected_cut_35855 : selected 10 ⟨944370, by decide⟩
    (prefixPartial 11 71858) = some ⟨11, 2, 0, 944370, 71858, 1737, 262144⟩ := by
  decide +kernel

theorem context_11_71858_944370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71858 ⟨944370, by decide⟩ :=
  accepted_of_selected 11 71858 ⟨944370, by decide⟩ ⟨11, 2, 0, 944370, 71858, 1737, 262144⟩
    (by decide) selected_cut_35855

theorem selected_cut_35856 : selected 10 ⟨944398, by decide⟩
    (prefixPartial 11 71859) = some ⟨11, 2, 0, 944398, 71859, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_71859_944398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71859 ⟨944398, by decide⟩ :=
  accepted_of_selected 11 71859 ⟨944398, by decide⟩ ⟨11, 2, 0, 944398, 71859, 2233, 262144⟩
    (by decide) selected_cut_35856

theorem unmarked_context_10_17964_944399 : frontier 11 ⟨944399, by decide⟩
    (prefixCache 10 17964) (prefixPartial 10 17964) = false := by
  decide +kernel

theorem node_context_10_17964_944399 : EJMOriginalGlobalDAGData.nodes 11 ⟨944399, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨944353, by decide⟩,⟨944370, by decide⟩,⟨944398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17964_944399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17964 ⟨944399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17964
    ⟨944399, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨944353, by decide⟩,⟨944370, by decide⟩,⟨944398, by decide⟩]) unmarked_context_10_17964_944399 node_context_10_17964_944399
  intro a
  fin_cases a
  · exact context_11_71856_907917
  · exact context_11_71857_944353
  · exact context_11_71858_944370
  · exact context_11_71859_944398

theorem selected_cut_35857 : selected 10 ⟨944419, by decide⟩
    (prefixPartial 11 71860) = some ⟨11, 2, 0, 944419, 71860, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_71860_944419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71860 ⟨944419, by decide⟩ :=
  accepted_of_selected 11 71860 ⟨944419, by decide⟩ ⟨11, 2, 0, 944419, 71860, 1813, 262144⟩
    (by decide) selected_cut_35857

theorem selected_cut_35858 : selected 10 ⟨944434, by decide⟩
    (prefixPartial 11 71861) = some ⟨11, 2, 0, 944434, 71861, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_71861_944434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71861 ⟨944434, by decide⟩ :=
  accepted_of_selected 11 71861 ⟨944434, by decide⟩ ⟨11, 2, 0, 944434, 71861, 1537, 262144⟩
    (by decide) selected_cut_35858

theorem selected_cut_35859 : selected 10 ⟨944446, by decide⟩
    (prefixPartial 11 71862) = some ⟨11, 2, 0, 944446, 71862, 1081, 262144⟩ := by
  decide +kernel

theorem context_11_71862_944446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71862 ⟨944446, by decide⟩ :=
  accepted_of_selected 11 71862 ⟨944446, by decide⟩ ⟨11, 2, 0, 944446, 71862, 1081, 262144⟩
    (by decide) selected_cut_35859

theorem selected_cut_35860 : selected 10 ⟨944466, by decide⟩
    (prefixPartial 11 71863) = some ⟨11, 2, 0, 944466, 71863, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_71863_944466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71863 ⟨944466, by decide⟩ :=
  accepted_of_selected 11 71863 ⟨944466, by decide⟩ ⟨11, 2, 0, 944466, 71863, 1425, 262144⟩
    (by decide) selected_cut_35860

theorem unmarked_context_10_17965_944467 : frontier 11 ⟨944467, by decide⟩
    (prefixCache 10 17965) (prefixPartial 10 17965) = false := by
  decide +kernel

theorem node_context_10_17965_944467 : EJMOriginalGlobalDAGData.nodes 11 ⟨944467, by decide⟩ =
    .split (coordinate 10) (![⟨944419, by decide⟩,⟨944434, by decide⟩,⟨944446, by decide⟩,⟨944466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17965_944467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17965 ⟨944467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17965
    ⟨944467, by decide⟩ (by decide) (![⟨944419, by decide⟩,⟨944434, by decide⟩,⟨944446, by decide⟩,⟨944466, by decide⟩]) unmarked_context_10_17965_944467 node_context_10_17965_944467
  intro a
  fin_cases a
  · exact context_11_71860_944419
  · exact context_11_71861_944434
  · exact context_11_71862_944446
  · exact context_11_71863_944466

theorem selected_cut_35861 : selected 11 ⟨944517, by decide⟩
    (prefixPartial 10 17966) = some ⟨10, 2, 0, 944517, 17966, 3489, 1048576⟩ := by
  decide +kernel

theorem context_10_17966_944517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17966 ⟨944517, by decide⟩ :=
  accepted_of_selected 10 17966 ⟨944517, by decide⟩ ⟨10, 2, 0, 944517, 17966, 3489, 1048576⟩
    (by decide) selected_cut_35861

theorem selected_cut_35862 : selected 11 ⟨944540, by decide⟩
    (prefixPartial 10 17967) = some ⟨10, 2, 0, 944540, 17967, 1041, 1048576⟩ := by
  decide +kernel

theorem context_10_17967_944540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17967 ⟨944540, by decide⟩ :=
  accepted_of_selected 10 17967 ⟨944540, by decide⟩ ⟨10, 2, 0, 944540, 17967, 1041, 1048576⟩
    (by decide) selected_cut_35862

theorem unmarked_context_9_4491_944541 : frontier 12 ⟨944541, by decide⟩
    (prefixCache 9 4491) (prefixPartial 9 4491) = false := by
  decide +kernel

theorem node_context_9_4491_944541 : EJMOriginalGlobalDAGData.nodes 12 ⟨944541, by decide⟩ =
    .split (coordinate 9) (![⟨944399, by decide⟩,⟨944467, by decide⟩,⟨944517, by decide⟩,⟨944540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4491_944541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4491 ⟨944541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4491
    ⟨944541, by decide⟩ (by decide) (![⟨944399, by decide⟩,⟨944467, by decide⟩,⟨944517, by decide⟩,⟨944540, by decide⟩]) unmarked_context_9_4491_944541 node_context_9_4491_944541
  intro a
  fin_cases a
  · exact context_10_17964_944399
  · exact context_10_17965_944467
  · exact context_10_17966_944517
  · exact context_10_17967_944540

theorem unmarked_context_8_1122_944542 : frontier 13 ⟨944542, by decide⟩
    (prefixCache 8 1122) (prefixPartial 8 1122) = false := by
  decide +kernel

theorem node_context_8_1122_944542 : EJMOriginalGlobalDAGData.nodes 13 ⟨944542, by decide⟩ =
    .split (coordinate 8) (![⟨942586, by decide⟩,⟨943463, by decide⟩,⟨944331, by decide⟩,⟨944541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1122_944542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1122 ⟨944542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1122
    ⟨944542, by decide⟩ (by decide) (![⟨942586, by decide⟩,⟨943463, by decide⟩,⟨944331, by decide⟩,⟨944541, by decide⟩]) unmarked_context_8_1122_944542 node_context_8_1122_944542
  intro a
  fin_cases a
  · exact context_9_4488_942586
  · exact context_9_4489_943463
  · exact context_9_4490_944331
  · exact context_9_4491_944541

theorem selected_cut_35863 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 71872) = some ⟨11, 1, 0, 167448, 71872, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71872_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71872 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 71872 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 71872, 1, 262144⟩
    (by decide) selected_cut_35863

theorem selected_cut_35864 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 287492) = some ⟨12, 1, 0, 34034, 287492, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287492_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287492 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 287492 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 287492, 1, 65536⟩
    (by decide) selected_cut_35864

theorem selected_cut_35865 : selected 9 ⟨944619, by decide⟩
    (prefixPartial 12 287493) = some ⟨12, 2, 0, 944619, 287493, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_287493_944619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287493 ⟨944619, by decide⟩ :=
  accepted_of_selected 12 287493 ⟨944619, by decide⟩ ⟨12, 2, 0, 944619, 287493, 3793, 65536⟩
    (by decide) selected_cut_35865

theorem selected_cut_35866 : selected 9 ⟨944690, by decide⟩
    (prefixPartial 12 287494) = some ⟨12, 2, 0, 944690, 287494, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_287494_944690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287494 ⟨944690, by decide⟩ :=
  accepted_of_selected 12 287494 ⟨944690, by decide⟩ ⟨12, 2, 0, 944690, 287494, 3717, 65536⟩
    (by decide) selected_cut_35866

theorem selected_cut_35867 : selected 8 ⟨944732, by decide⟩
    (prefixPartial 13 1149980) = some ⟨13, 2, 0, 944732, 1149980, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_1149980_944732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149980 ⟨944732, by decide⟩ :=
  accepted_of_selected 13 1149980 ⟨944732, by decide⟩ ⟨13, 2, 0, 944732, 1149980, 1969, 16384⟩
    (by decide) selected_cut_35867

theorem selected_cut_35868 : selected 8 ⟨944742, by decide⟩
    (prefixPartial 13 1149981) = some ⟨13, 2, 0, 944742, 1149981, 609, 16384⟩ := by
  decide +kernel

theorem context_13_1149981_944742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149981 ⟨944742, by decide⟩ :=
  accepted_of_selected 13 1149981 ⟨944742, by decide⟩ ⟨13, 2, 0, 944742, 1149981, 609, 16384⟩
    (by decide) selected_cut_35868

theorem selected_cut_35869 : selected 8 ⟨944758, by decide⟩
    (prefixPartial 13 1149982) = some ⟨13, 2, 0, 944758, 1149982, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_1149982_944758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149982 ⟨944758, by decide⟩ :=
  accepted_of_selected 13 1149982 ⟨944758, by decide⟩ ⟨13, 2, 0, 944758, 1149982, 1013, 16384⟩
    (by decide) selected_cut_35869

theorem selected_cut_35870 : selected 8 ⟨944764, by decide⟩
    (prefixPartial 13 1149983) = some ⟨13, 2, 0, 944764, 1149983, 561, 16384⟩ := by
  decide +kernel

theorem context_13_1149983_944764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149983 ⟨944764, by decide⟩ :=
  accepted_of_selected 13 1149983 ⟨944764, by decide⟩ ⟨13, 2, 0, 944764, 1149983, 561, 16384⟩
    (by decide) selected_cut_35870

theorem unmarked_context_12_287495_944765 : frontier 9 ⟨944765, by decide⟩
    (prefixCache 12 287495) (prefixPartial 12 287495) = false := by
  decide +kernel

theorem node_context_12_287495_944765 : EJMOriginalGlobalDAGData.nodes 9 ⟨944765, by decide⟩ =
    .split (coordinate 12) (![⟨944732, by decide⟩,⟨944742, by decide⟩,⟨944758, by decide⟩,⟨944764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287495_944765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287495 ⟨944765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287495
    ⟨944765, by decide⟩ (by decide) (![⟨944732, by decide⟩,⟨944742, by decide⟩,⟨944758, by decide⟩,⟨944764, by decide⟩]) unmarked_context_12_287495_944765 node_context_12_287495_944765
  intro a
  fin_cases a
  · exact context_13_1149980_944732
  · exact context_13_1149981_944742
  · exact context_13_1149982_944758
  · exact context_13_1149983_944764

theorem unmarked_context_11_71873_944766 : frontier 10 ⟨944766, by decide⟩
    (prefixCache 11 71873) (prefixPartial 11 71873) = false := by
  decide +kernel

theorem node_context_11_71873_944766 : EJMOriginalGlobalDAGData.nodes 10 ⟨944766, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨944619, by decide⟩,⟨944690, by decide⟩,⟨944765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71873_944766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71873 ⟨944766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71873
    ⟨944766, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨944619, by decide⟩,⟨944690, by decide⟩,⟨944765, by decide⟩]) unmarked_context_11_71873_944766 node_context_11_71873_944766
  intro a
  fin_cases a
  · exact context_12_287492_34034
  · exact context_12_287493_944619
  · exact context_12_287494_944690
  · exact context_12_287495_944765

theorem selected_cut_35871 : selected 8 ⟨944820, by decide⟩
    (prefixPartial 13 1149984) = some ⟨13, 2, 0, 944820, 1149984, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_1149984_944820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149984 ⟨944820, by decide⟩ :=
  accepted_of_selected 13 1149984 ⟨944820, by decide⟩ ⟨13, 2, 0, 944820, 1149984, 2233, 16384⟩
    (by decide) selected_cut_35871

theorem selected_cut_35872 : selected 8 ⟨944854, by decide⟩
    (prefixPartial 13 1149985) = some ⟨13, 2, 0, 944854, 1149985, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_1149985_944854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149985 ⟨944854, by decide⟩ :=
  accepted_of_selected 13 1149985 ⟨944854, by decide⟩ ⟨13, 2, 0, 944854, 1149985, 1229, 16384⟩
    (by decide) selected_cut_35872

theorem selected_cut_35873 : selected 8 ⟨944882, by decide⟩
    (prefixPartial 13 1149986) = some ⟨13, 2, 0, 944882, 1149986, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_1149986_944882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149986 ⟨944882, by decide⟩ :=
  accepted_of_selected 13 1149986 ⟨944882, by decide⟩ ⟨13, 2, 0, 944882, 1149986, 1257, 16384⟩
    (by decide) selected_cut_35873

theorem selected_cut_35874 : selected 8 ⟨944894, by decide⟩
    (prefixPartial 13 1149987) = some ⟨13, 2, 0, 944894, 1149987, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1149987_944894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149987 ⟨944894, by decide⟩ :=
  accepted_of_selected 13 1149987 ⟨944894, by decide⟩ ⟨13, 2, 0, 944894, 1149987, 685, 16384⟩
    (by decide) selected_cut_35874

theorem unmarked_context_12_287496_944895 : frontier 9 ⟨944895, by decide⟩
    (prefixCache 12 287496) (prefixPartial 12 287496) = false := by
  decide +kernel

theorem node_context_12_287496_944895 : EJMOriginalGlobalDAGData.nodes 9 ⟨944895, by decide⟩ =
    .split (coordinate 12) (![⟨944820, by decide⟩,⟨944854, by decide⟩,⟨944882, by decide⟩,⟨944894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287496_944895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287496 ⟨944895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287496
    ⟨944895, by decide⟩ (by decide) (![⟨944820, by decide⟩,⟨944854, by decide⟩,⟨944882, by decide⟩,⟨944894, by decide⟩]) unmarked_context_12_287496_944895 node_context_12_287496_944895
  intro a
  fin_cases a
  · exact context_13_1149984_944820
  · exact context_13_1149985_944854
  · exact context_13_1149986_944882
  · exact context_13_1149987_944894

theorem selected_cut_35875 : selected 8 ⟨944926, by decide⟩
    (prefixPartial 13 1149988) = some ⟨13, 2, 0, 944926, 1149988, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_1149988_944926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149988 ⟨944926, by decide⟩ :=
  accepted_of_selected 13 1149988 ⟨944926, by decide⟩ ⟨13, 2, 0, 944926, 1149988, 1581, 16384⟩
    (by decide) selected_cut_35875

theorem selected_cut_35876 : selected 8 ⟨944949, by decide⟩
    (prefixPartial 13 1149989) = some ⟨13, 2, 0, 944949, 1149989, 961, 16384⟩ := by
  decide +kernel

theorem context_13_1149989_944949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149989 ⟨944949, by decide⟩ :=
  accepted_of_selected 13 1149989 ⟨944949, by decide⟩ ⟨13, 2, 0, 944949, 1149989, 961, 16384⟩
    (by decide) selected_cut_35876

theorem selected_cut_35877 : selected 8 ⟨944963, by decide⟩
    (prefixPartial 13 1149990) = some ⟨13, 2, 0, 944963, 1149990, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_1149990_944963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149990 ⟨944963, by decide⟩ :=
  accepted_of_selected 13 1149990 ⟨944963, by decide⟩ ⟨13, 2, 0, 944963, 1149990, 1021, 16384⟩
    (by decide) selected_cut_35877

theorem selected_cut_35878 : selected 8 ⟨944972, by decide⟩
    (prefixPartial 13 1149991) = some ⟨13, 2, 0, 944972, 1149991, 605, 16384⟩ := by
  decide +kernel

theorem context_13_1149991_944972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149991 ⟨944972, by decide⟩ :=
  accepted_of_selected 13 1149991 ⟨944972, by decide⟩ ⟨13, 2, 0, 944972, 1149991, 605, 16384⟩
    (by decide) selected_cut_35878

theorem unmarked_context_12_287497_944973 : frontier 9 ⟨944973, by decide⟩
    (prefixCache 12 287497) (prefixPartial 12 287497) = false := by
  decide +kernel

theorem node_context_12_287497_944973 : EJMOriginalGlobalDAGData.nodes 9 ⟨944973, by decide⟩ =
    .split (coordinate 12) (![⟨944926, by decide⟩,⟨944949, by decide⟩,⟨944963, by decide⟩,⟨944972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287497_944973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287497 ⟨944973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287497
    ⟨944973, by decide⟩ (by decide) (![⟨944926, by decide⟩,⟨944949, by decide⟩,⟨944963, by decide⟩,⟨944972, by decide⟩]) unmarked_context_12_287497_944973 node_context_12_287497_944973
  intro a
  fin_cases a
  · exact context_13_1149988_944926
  · exact context_13_1149989_944949
  · exact context_13_1149990_944963
  · exact context_13_1149991_944972

theorem selected_cut_35879 : selected 9 ⟨945035, by decide⟩
    (prefixPartial 12 287498) = some ⟨12, 2, 0, 945035, 287498, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_287498_945035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287498 ⟨945035, by decide⟩ :=
  accepted_of_selected 12 287498 ⟨945035, by decide⟩ ⟨12, 2, 0, 945035, 287498, 3737, 65536⟩
    (by decide) selected_cut_35879

theorem selected_cut_35880 : selected 8 ⟨945068, by decide⟩
    (prefixPartial 13 1149996) = some ⟨13, 2, 0, 945068, 1149996, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_1149996_945068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149996 ⟨945068, by decide⟩ :=
  accepted_of_selected 13 1149996 ⟨945068, by decide⟩ ⟨13, 2, 0, 945068, 1149996, 1937, 16384⟩
    (by decide) selected_cut_35880

theorem selected_cut_35881 : selected 8 ⟨945088, by decide⟩
    (prefixPartial 13 1149997) = some ⟨13, 2, 0, 945088, 1149997, 957, 16384⟩ := by
  decide +kernel

theorem context_13_1149997_945088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149997 ⟨945088, by decide⟩ :=
  accepted_of_selected 13 1149997 ⟨945088, by decide⟩ ⟨13, 2, 0, 945088, 1149997, 957, 16384⟩
    (by decide) selected_cut_35881

theorem selected_cut_35882 : selected 8 ⟨945102, by decide⟩
    (prefixPartial 13 1149998) = some ⟨13, 2, 0, 945102, 1149998, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_1149998_945102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149998 ⟨945102, by decide⟩ :=
  accepted_of_selected 13 1149998 ⟨945102, by decide⟩ ⟨13, 2, 0, 945102, 1149998, 1041, 16384⟩
    (by decide) selected_cut_35882

theorem selected_cut_35883 : selected 8 ⟨945109, by decide⟩
    (prefixPartial 13 1149999) = some ⟨13, 2, 0, 945109, 1149999, 609, 16384⟩ := by
  decide +kernel

theorem context_13_1149999_945109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1149999 ⟨945109, by decide⟩ :=
  accepted_of_selected 13 1149999 ⟨945109, by decide⟩ ⟨13, 2, 0, 945109, 1149999, 609, 16384⟩
    (by decide) selected_cut_35883

theorem unmarked_context_12_287499_945110 : frontier 9 ⟨945110, by decide⟩
    (prefixCache 12 287499) (prefixPartial 12 287499) = false := by
  decide +kernel

theorem node_context_12_287499_945110 : EJMOriginalGlobalDAGData.nodes 9 ⟨945110, by decide⟩ =
    .split (coordinate 12) (![⟨945068, by decide⟩,⟨945088, by decide⟩,⟨945102, by decide⟩,⟨945109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287499_945110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287499 ⟨945110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287499
    ⟨945110, by decide⟩ (by decide) (![⟨945068, by decide⟩,⟨945088, by decide⟩,⟨945102, by decide⟩,⟨945109, by decide⟩]) unmarked_context_12_287499_945110 node_context_12_287499_945110
  intro a
  fin_cases a
  · exact context_13_1149996_945068
  · exact context_13_1149997_945088
  · exact context_13_1149998_945102
  · exact context_13_1149999_945109

theorem unmarked_context_11_71874_945111 : frontier 10 ⟨945111, by decide⟩
    (prefixCache 11 71874) (prefixPartial 11 71874) = false := by
  decide +kernel

theorem node_context_11_71874_945111 : EJMOriginalGlobalDAGData.nodes 10 ⟨945111, by decide⟩ =
    .split (coordinate 11) (![⟨944895, by decide⟩,⟨944973, by decide⟩,⟨945035, by decide⟩,⟨945110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71874_945111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71874 ⟨945111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71874
    ⟨945111, by decide⟩ (by decide) (![⟨944895, by decide⟩,⟨944973, by decide⟩,⟨945035, by decide⟩,⟨945110, by decide⟩]) unmarked_context_11_71874_945111 node_context_11_71874_945111
  intro a
  fin_cases a
  · exact context_12_287496_944895
  · exact context_12_287497_944973
  · exact context_12_287498_945035
  · exact context_12_287499_945110

theorem selected_cut_35884 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 287500) = some ⟨12, 1, 0, 292651, 287500, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287500_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287500 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 287500 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 287500, 1, 65536⟩
    (by decide) selected_cut_35884

theorem selected_cut_35885 : selected 9 ⟨945163, by decide⟩
    (prefixPartial 12 287501) = some ⟨12, 2, 0, 945163, 287501, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_287501_945163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287501 ⟨945163, by decide⟩ :=
  accepted_of_selected 12 287501 ⟨945163, by decide⟩ ⟨12, 2, 0, 945163, 287501, 3389, 65536⟩
    (by decide) selected_cut_35885

theorem selected_cut_35886 : selected 9 ⟨945224, by decide⟩
    (prefixPartial 12 287502) = some ⟨12, 2, 0, 945224, 287502, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_287502_945224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287502 ⟨945224, by decide⟩ :=
  accepted_of_selected 12 287502 ⟨945224, by decide⟩ ⟨12, 2, 0, 945224, 287502, 3625, 65536⟩
    (by decide) selected_cut_35886

theorem selected_cut_35887 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 287503) = some ⟨12, 1, 0, 903806, 287503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287503_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287503 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 287503 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 287503, 1, 65536⟩
    (by decide) selected_cut_35887

theorem unmarked_context_11_71875_945225 : frontier 10 ⟨945225, by decide⟩
    (prefixCache 11 71875) (prefixPartial 11 71875) = false := by
  decide +kernel

theorem node_context_11_71875_945225 : EJMOriginalGlobalDAGData.nodes 10 ⟨945225, by decide⟩ =
    .split (coordinate 11) (![⟨292651, by decide⟩,⟨945163, by decide⟩,⟨945224, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71875_945225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71875 ⟨945225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71875
    ⟨945225, by decide⟩ (by decide) (![⟨292651, by decide⟩,⟨945163, by decide⟩,⟨945224, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71875_945225 node_context_11_71875_945225
  intro a
  fin_cases a
  · exact context_12_287500_292651
  · exact context_12_287501_945163
  · exact context_12_287502_945224
  · exact context_12_287503_903806

theorem unmarked_context_10_17968_945226 : frontier 11 ⟨945226, by decide⟩
    (prefixCache 10 17968) (prefixPartial 10 17968) = false := by
  decide +kernel

theorem node_context_10_17968_945226 : EJMOriginalGlobalDAGData.nodes 11 ⟨945226, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨944766, by decide⟩,⟨945111, by decide⟩,⟨945225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17968_945226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17968 ⟨945226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17968
    ⟨945226, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨944766, by decide⟩,⟨945111, by decide⟩,⟨945225, by decide⟩]) unmarked_context_10_17968_945226 node_context_10_17968_945226
  intro a
  fin_cases a
  · exact context_11_71872_167448
  · exact context_11_71873_944766
  · exact context_11_71874_945111
  · exact context_11_71875_945225

theorem selected_cut_35888 : selected 9 ⟨945292, by decide⟩
    (prefixPartial 12 287504) = some ⟨12, 2, 0, 945292, 287504, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_287504_945292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287504 ⟨945292, by decide⟩ :=
  accepted_of_selected 12 287504 ⟨945292, by decide⟩ ⟨12, 2, 0, 945292, 287504, 3857, 65536⟩
    (by decide) selected_cut_35888

theorem selected_cut_35889 : selected 9 ⟨945344, by decide⟩
    (prefixPartial 12 287505) = some ⟨12, 2, 0, 945344, 287505, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_287505_945344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287505 ⟨945344, by decide⟩ :=
  accepted_of_selected 12 287505 ⟨945344, by decide⟩ ⟨12, 2, 0, 945344, 287505, 3349, 65536⟩
    (by decide) selected_cut_35889

theorem selected_cut_35890 : selected 9 ⟨945392, by decide⟩
    (prefixPartial 12 287506) = some ⟨12, 2, 0, 945392, 287506, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_287506_945392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287506 ⟨945392, by decide⟩ :=
  accepted_of_selected 12 287506 ⟨945392, by decide⟩ ⟨12, 2, 0, 945392, 287506, 3385, 65536⟩
    (by decide) selected_cut_35890

theorem selected_cut_35891 : selected 9 ⟨945449, by decide⟩
    (prefixPartial 12 287507) = some ⟨12, 2, 0, 945449, 287507, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_287507_945449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287507 ⟨945449, by decide⟩ :=
  accepted_of_selected 12 287507 ⟨945449, by decide⟩ ⟨12, 2, 0, 945449, 287507, 3601, 65536⟩
    (by decide) selected_cut_35891

theorem unmarked_context_11_71876_945450 : frontier 10 ⟨945450, by decide⟩
    (prefixCache 11 71876) (prefixPartial 11 71876) = false := by
  decide +kernel

theorem node_context_11_71876_945450 : EJMOriginalGlobalDAGData.nodes 10 ⟨945450, by decide⟩ =
    .split (coordinate 11) (![⟨945292, by decide⟩,⟨945344, by decide⟩,⟨945392, by decide⟩,⟨945449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71876_945450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71876 ⟨945450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71876
    ⟨945450, by decide⟩ (by decide) (![⟨945292, by decide⟩,⟨945344, by decide⟩,⟨945392, by decide⟩,⟨945449, by decide⟩]) unmarked_context_11_71876_945450 node_context_11_71876_945450
  intro a
  fin_cases a
  · exact context_12_287504_945292
  · exact context_12_287505_945344
  · exact context_12_287506_945392
  · exact context_12_287507_945449

theorem selected_cut_35892 : selected 9 ⟨945523, by decide⟩
    (prefixPartial 12 287508) = some ⟨12, 2, 0, 945523, 287508, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_287508_945523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287508 ⟨945523, by decide⟩ :=
  accepted_of_selected 12 287508 ⟨945523, by decide⟩ ⟨12, 2, 0, 945523, 287508, 4009, 65536⟩
    (by decide) selected_cut_35892

theorem selected_cut_35893 : selected 9 ⟨945581, by decide⟩
    (prefixPartial 12 287509) = some ⟨12, 2, 0, 945581, 287509, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_287509_945581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287509 ⟨945581, by decide⟩ :=
  accepted_of_selected 12 287509 ⟨945581, by decide⟩ ⟨12, 2, 0, 945581, 287509, 3549, 65536⟩
    (by decide) selected_cut_35893

theorem selected_cut_35894 : selected 9 ⟨945631, by decide⟩
    (prefixPartial 12 287510) = some ⟨12, 2, 0, 945631, 287510, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_287510_945631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287510 ⟨945631, by decide⟩ :=
  accepted_of_selected 12 287510 ⟨945631, by decide⟩ ⟨12, 2, 0, 945631, 287510, 3421, 65536⟩
    (by decide) selected_cut_35894

theorem selected_cut_35895 : selected 9 ⟨945687, by decide⟩
    (prefixPartial 12 287511) = some ⟨12, 2, 0, 945687, 287511, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_287511_945687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287511 ⟨945687, by decide⟩ :=
  accepted_of_selected 12 287511 ⟨945687, by decide⟩ ⟨12, 2, 0, 945687, 287511, 3637, 65536⟩
    (by decide) selected_cut_35895

theorem unmarked_context_11_71877_945688 : frontier 10 ⟨945688, by decide⟩
    (prefixCache 11 71877) (prefixPartial 11 71877) = false := by
  decide +kernel

theorem node_context_11_71877_945688 : EJMOriginalGlobalDAGData.nodes 10 ⟨945688, by decide⟩ =
    .split (coordinate 11) (![⟨945523, by decide⟩,⟨945581, by decide⟩,⟨945631, by decide⟩,⟨945687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71877_945688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71877 ⟨945688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71877
    ⟨945688, by decide⟩ (by decide) (![⟨945523, by decide⟩,⟨945581, by decide⟩,⟨945631, by decide⟩,⟨945687, by decide⟩]) unmarked_context_11_71877_945688 node_context_11_71877_945688
  intro a
  fin_cases a
  · exact context_12_287508_945523
  · exact context_12_287509_945581
  · exact context_12_287510_945631
  · exact context_12_287511_945687

theorem selected_cut_35896 : selected 8 ⟨945724, by decide⟩
    (prefixPartial 13 1150048) = some ⟨13, 2, 0, 945724, 1150048, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_1150048_945724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150048 ⟨945724, by decide⟩ :=
  accepted_of_selected 13 1150048 ⟨945724, by decide⟩ ⟨13, 2, 0, 945724, 1150048, 1845, 16384⟩
    (by decide) selected_cut_35896

theorem selected_cut_35897 : selected 8 ⟨945750, by decide⟩
    (prefixPartial 13 1150049) = some ⟨13, 2, 0, 945750, 1150049, 925, 16384⟩ := by
  decide +kernel

theorem context_13_1150049_945750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150049 ⟨945750, by decide⟩ :=
  accepted_of_selected 13 1150049 ⟨945750, by decide⟩ ⟨13, 2, 0, 945750, 1150049, 925, 16384⟩
    (by decide) selected_cut_35897

theorem selected_cut_35898 : selected 8 ⟨945772, by decide⟩
    (prefixPartial 13 1150050) = some ⟨13, 2, 0, 945772, 1150050, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_1150050_945772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150050 ⟨945772, by decide⟩ :=
  accepted_of_selected 13 1150050 ⟨945772, by decide⟩ ⟨13, 2, 0, 945772, 1150050, 1133, 16384⟩
    (by decide) selected_cut_35898

theorem selected_cut_35899 : selected 8 ⟨945781, by decide⟩
    (prefixPartial 13 1150051) = some ⟨13, 2, 0, 945781, 1150051, 689, 16384⟩ := by
  decide +kernel

theorem context_13_1150051_945781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150051 ⟨945781, by decide⟩ :=
  accepted_of_selected 13 1150051 ⟨945781, by decide⟩ ⟨13, 2, 0, 945781, 1150051, 689, 16384⟩
    (by decide) selected_cut_35899

theorem unmarked_context_12_287512_945782 : frontier 9 ⟨945782, by decide⟩
    (prefixCache 12 287512) (prefixPartial 12 287512) = false := by
  decide +kernel

theorem node_context_12_287512_945782 : EJMOriginalGlobalDAGData.nodes 9 ⟨945782, by decide⟩ =
    .split (coordinate 12) (![⟨945724, by decide⟩,⟨945750, by decide⟩,⟨945772, by decide⟩,⟨945781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287512_945782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287512 ⟨945782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287512
    ⟨945782, by decide⟩ (by decide) (![⟨945724, by decide⟩,⟨945750, by decide⟩,⟨945772, by decide⟩,⟨945781, by decide⟩]) unmarked_context_12_287512_945782 node_context_12_287512_945782
  intro a
  fin_cases a
  · exact context_13_1150048_945724
  · exact context_13_1150049_945750
  · exact context_13_1150050_945772
  · exact context_13_1150051_945781

theorem selected_cut_35900 : selected 9 ⟨945855, by decide⟩
    (prefixPartial 12 287513) = some ⟨12, 2, 0, 945855, 287513, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_287513_945855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287513 ⟨945855, by decide⟩ :=
  accepted_of_selected 12 287513 ⟨945855, by decide⟩ ⟨12, 2, 0, 945855, 287513, 4013, 65536⟩
    (by decide) selected_cut_35900

theorem selected_cut_35901 : selected 9 ⟨945915, by decide⟩
    (prefixPartial 12 287514) = some ⟨12, 2, 0, 945915, 287514, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_287514_945915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287514 ⟨945915, by decide⟩ :=
  accepted_of_selected 12 287514 ⟨945915, by decide⟩ ⟨12, 2, 0, 945915, 287514, 3625, 65536⟩
    (by decide) selected_cut_35901

theorem selected_cut_35902 : selected 8 ⟨945945, by decide⟩
    (prefixPartial 13 1150060) = some ⟨13, 2, 0, 945945, 1150060, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_1150060_945945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150060 ⟨945945, by decide⟩ :=
  accepted_of_selected 13 1150060 ⟨945945, by decide⟩ ⟨13, 2, 0, 945945, 1150060, 1617, 16384⟩
    (by decide) selected_cut_35902

theorem selected_cut_35903 : selected 8 ⟨945963, by decide⟩
    (prefixPartial 13 1150061) = some ⟨13, 2, 0, 945963, 1150061, 885, 16384⟩ := by
  decide +kernel

theorem context_13_1150061_945963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150061 ⟨945963, by decide⟩ :=
  accepted_of_selected 13 1150061 ⟨945963, by decide⟩ ⟨13, 2, 0, 945963, 1150061, 885, 16384⟩
    (by decide) selected_cut_35903

theorem selected_cut_35904 : selected 8 ⟨945977, by decide⟩
    (prefixPartial 13 1150062) = some ⟨13, 2, 0, 945977, 1150062, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_1150062_945977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150062 ⟨945977, by decide⟩ :=
  accepted_of_selected 13 1150062 ⟨945977, by decide⟩ ⟨13, 2, 0, 945977, 1150062, 1093, 16384⟩
    (by decide) selected_cut_35904

theorem selected_cut_35905 : selected 8 ⟨945984, by decide⟩
    (prefixPartial 13 1150063) = some ⟨13, 2, 0, 945984, 1150063, 585, 16384⟩ := by
  decide +kernel

theorem context_13_1150063_945984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1150063 ⟨945984, by decide⟩ :=
  accepted_of_selected 13 1150063 ⟨945984, by decide⟩ ⟨13, 2, 0, 945984, 1150063, 585, 16384⟩
    (by decide) selected_cut_35905

theorem unmarked_context_12_287515_945985 : frontier 9 ⟨945985, by decide⟩
    (prefixCache 12 287515) (prefixPartial 12 287515) = false := by
  decide +kernel

theorem node_context_12_287515_945985 : EJMOriginalGlobalDAGData.nodes 9 ⟨945985, by decide⟩ =
    .split (coordinate 12) (![⟨945945, by decide⟩,⟨945963, by decide⟩,⟨945977, by decide⟩,⟨945984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_287515_945985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287515 ⟨945985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 287515
    ⟨945985, by decide⟩ (by decide) (![⟨945945, by decide⟩,⟨945963, by decide⟩,⟨945977, by decide⟩,⟨945984, by decide⟩]) unmarked_context_12_287515_945985 node_context_12_287515_945985
  intro a
  fin_cases a
  · exact context_13_1150060_945945
  · exact context_13_1150061_945963
  · exact context_13_1150062_945977
  · exact context_13_1150063_945984

theorem unmarked_context_11_71878_945986 : frontier 10 ⟨945986, by decide⟩
    (prefixCache 11 71878) (prefixPartial 11 71878) = false := by
  decide +kernel

theorem node_context_11_71878_945986 : EJMOriginalGlobalDAGData.nodes 10 ⟨945986, by decide⟩ =
    .split (coordinate 11) (![⟨945782, by decide⟩,⟨945855, by decide⟩,⟨945915, by decide⟩,⟨945985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71878_945986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71878 ⟨945986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71878
    ⟨945986, by decide⟩ (by decide) (![⟨945782, by decide⟩,⟨945855, by decide⟩,⟨945915, by decide⟩,⟨945985, by decide⟩]) unmarked_context_11_71878_945986 node_context_11_71878_945986
  intro a
  fin_cases a
  · exact context_12_287512_945782
  · exact context_12_287513_945855
  · exact context_12_287514_945915
  · exact context_12_287515_945985

theorem selected_cut_35906 : selected 9 ⟨946046, by decide⟩
    (prefixPartial 12 287516) = some ⟨12, 2, 0, 946046, 287516, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_287516_946046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287516 ⟨946046, by decide⟩ :=
  accepted_of_selected 12 287516 ⟨946046, by decide⟩ ⟨12, 2, 0, 946046, 287516, 3721, 65536⟩
    (by decide) selected_cut_35906

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
