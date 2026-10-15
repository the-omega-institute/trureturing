/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover322
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31011 : selected 8 ⟨789806, by decide⟩
    (prefixPartial 13 421971) = some ⟨13, 2, 0, 789806, 421971, 821, 16384⟩ := by
  decide +kernel

theorem context_13_421971_789806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421971 ⟨789806, by decide⟩ :=
  accepted_of_selected 13 421971 ⟨789806, by decide⟩ ⟨13, 2, 0, 789806, 421971, 821, 16384⟩
    (by decide) selected_cut_31011

theorem unmarked_context_12_105492_789807 : frontier 9 ⟨789807, by decide⟩
    (prefixCache 12 105492) (prefixPartial 12 105492) = false := by
  decide +kernel

theorem node_context_12_105492_789807 : EJMOriginalGlobalDAGData.nodes 9 ⟨789807, by decide⟩ =
    .split (coordinate 12) (![⟨789718, by decide⟩,⟨789763, by decide⟩,⟨789794, by decide⟩,⟨789806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105492_789807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105492 ⟨789807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105492
    ⟨789807, by decide⟩ (by decide) (![⟨789718, by decide⟩,⟨789763, by decide⟩,⟨789794, by decide⟩,⟨789806, by decide⟩]) unmarked_context_12_105492_789807 node_context_12_105492_789807
  intro a
  fin_cases a
  · exact context_13_421968_789718
  · exact context_13_421969_789763
  · exact context_13_421970_789794
  · exact context_13_421971_789806

theorem selected_cut_31012 : selected 8 ⟨789842, by decide⟩
    (prefixPartial 13 421972) = some ⟨13, 2, 0, 789842, 421972, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_421972_789842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421972 ⟨789842, by decide⟩ :=
  accepted_of_selected 13 421972 ⟨789842, by decide⟩ ⟨13, 2, 0, 789842, 421972, 1561, 16384⟩
    (by decide) selected_cut_31012

theorem selected_cut_31013 : selected 8 ⟨789876, by decide⟩
    (prefixPartial 13 421973) = some ⟨13, 2, 0, 789876, 421973, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_421973_789876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421973 ⟨789876, by decide⟩ :=
  accepted_of_selected 13 421973 ⟨789876, by decide⟩ ⟨13, 2, 0, 789876, 421973, 2013, 16384⟩
    (by decide) selected_cut_31013

theorem selected_cut_31014 : selected 8 ⟨789902, by decide⟩
    (prefixPartial 13 421974) = some ⟨13, 2, 0, 789902, 421974, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_421974_789902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421974 ⟨789902, by decide⟩ :=
  accepted_of_selected 13 421974 ⟨789902, by decide⟩ ⟨13, 2, 0, 789902, 421974, 1473, 16384⟩
    (by decide) selected_cut_31014

theorem selected_cut_31015 : selected 8 ⟨789909, by decide⟩
    (prefixPartial 13 421975) = some ⟨13, 2, 0, 789909, 421975, 801, 16384⟩ := by
  decide +kernel

theorem context_13_421975_789909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421975 ⟨789909, by decide⟩ :=
  accepted_of_selected 13 421975 ⟨789909, by decide⟩ ⟨13, 2, 0, 789909, 421975, 801, 16384⟩
    (by decide) selected_cut_31015

theorem unmarked_context_12_105493_789910 : frontier 9 ⟨789910, by decide⟩
    (prefixCache 12 105493) (prefixPartial 12 105493) = false := by
  decide +kernel

theorem node_context_12_105493_789910 : EJMOriginalGlobalDAGData.nodes 9 ⟨789910, by decide⟩ =
    .split (coordinate 12) (![⟨789842, by decide⟩,⟨789876, by decide⟩,⟨789902, by decide⟩,⟨789909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105493_789910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105493 ⟨789910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105493
    ⟨789910, by decide⟩ (by decide) (![⟨789842, by decide⟩,⟨789876, by decide⟩,⟨789902, by decide⟩,⟨789909, by decide⟩]) unmarked_context_12_105493_789910 node_context_12_105493_789910
  intro a
  fin_cases a
  · exact context_13_421972_789842
  · exact context_13_421973_789876
  · exact context_13_421974_789902
  · exact context_13_421975_789909

theorem selected_cut_31016 : selected 8 ⟨789944, by decide⟩
    (prefixPartial 13 421976) = some ⟨13, 2, 0, 789944, 421976, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_421976_789944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421976 ⟨789944, by decide⟩ :=
  accepted_of_selected 13 421976 ⟨789944, by decide⟩ ⟨13, 2, 0, 789944, 421976, 1657, 16384⟩
    (by decide) selected_cut_31016

theorem selected_cut_31017 : selected 8 ⟨789983, by decide⟩
    (prefixPartial 13 421977) = some ⟨13, 2, 0, 789983, 421977, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_421977_789983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421977 ⟨789983, by decide⟩ :=
  accepted_of_selected 13 421977 ⟨789983, by decide⟩ ⟨13, 2, 0, 789983, 421977, 2409, 16384⟩
    (by decide) selected_cut_31017

theorem selected_cut_31018 : selected 8 ⟨790003, by decide⟩
    (prefixPartial 13 421978) = some ⟨13, 2, 0, 790003, 421978, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_421978_790003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421978 ⟨790003, by decide⟩ :=
  accepted_of_selected 13 421978 ⟨790003, by decide⟩ ⟨13, 2, 0, 790003, 421978, 1313, 16384⟩
    (by decide) selected_cut_31018

theorem selected_cut_31019 : selected 8 ⟨790012, by decide⟩
    (prefixPartial 13 421979) = some ⟨13, 2, 0, 790012, 421979, 957, 16384⟩ := by
  decide +kernel

theorem context_13_421979_790012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421979 ⟨790012, by decide⟩ :=
  accepted_of_selected 13 421979 ⟨790012, by decide⟩ ⟨13, 2, 0, 790012, 421979, 957, 16384⟩
    (by decide) selected_cut_31019

theorem unmarked_context_12_105494_790013 : frontier 9 ⟨790013, by decide⟩
    (prefixCache 12 105494) (prefixPartial 12 105494) = false := by
  decide +kernel

theorem node_context_12_105494_790013 : EJMOriginalGlobalDAGData.nodes 9 ⟨790013, by decide⟩ =
    .split (coordinate 12) (![⟨789944, by decide⟩,⟨789983, by decide⟩,⟨790003, by decide⟩,⟨790012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105494_790013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105494 ⟨790013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105494
    ⟨790013, by decide⟩ (by decide) (![⟨789944, by decide⟩,⟨789983, by decide⟩,⟨790003, by decide⟩,⟨790012, by decide⟩]) unmarked_context_12_105494_790013 node_context_12_105494_790013
  intro a
  fin_cases a
  · exact context_13_421976_789944
  · exact context_13_421977_789983
  · exact context_13_421978_790003
  · exact context_13_421979_790012

theorem selected_cut_31020 : selected 8 ⟨790050, by decide⟩
    (prefixPartial 13 421980) = some ⟨13, 2, 0, 790050, 421980, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_421980_790050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421980 ⟨790050, by decide⟩ :=
  accepted_of_selected 13 421980 ⟨790050, by decide⟩ ⟨13, 2, 0, 790050, 421980, 1777, 16384⟩
    (by decide) selected_cut_31020

theorem selected_cut_31021 : selected 8 ⟨790091, by decide⟩
    (prefixPartial 13 421981) = some ⟨13, 2, 0, 790091, 421981, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_421981_790091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421981 ⟨790091, by decide⟩ :=
  accepted_of_selected 13 421981 ⟨790091, by decide⟩ ⟨13, 2, 0, 790091, 421981, 2329, 16384⟩
    (by decide) selected_cut_31021

theorem selected_cut_31022 : selected 8 ⟨790128, by decide⟩
    (prefixPartial 13 421982) = some ⟨13, 2, 0, 790128, 421982, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_421982_790128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421982 ⟨790128, by decide⟩ :=
  accepted_of_selected 13 421982 ⟨790128, by decide⟩ ⟨13, 2, 0, 790128, 421982, 1713, 16384⟩
    (by decide) selected_cut_31022

theorem selected_cut_31023 : selected 8 ⟨790140, by decide⟩
    (prefixPartial 13 421983) = some ⟨13, 2, 0, 790140, 421983, 925, 16384⟩ := by
  decide +kernel

theorem context_13_421983_790140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421983 ⟨790140, by decide⟩ :=
  accepted_of_selected 13 421983 ⟨790140, by decide⟩ ⟨13, 2, 0, 790140, 421983, 925, 16384⟩
    (by decide) selected_cut_31023

theorem unmarked_context_12_105495_790141 : frontier 9 ⟨790141, by decide⟩
    (prefixCache 12 105495) (prefixPartial 12 105495) = false := by
  decide +kernel

theorem node_context_12_105495_790141 : EJMOriginalGlobalDAGData.nodes 9 ⟨790141, by decide⟩ =
    .split (coordinate 12) (![⟨790050, by decide⟩,⟨790091, by decide⟩,⟨790128, by decide⟩,⟨790140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105495_790141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105495 ⟨790141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105495
    ⟨790141, by decide⟩ (by decide) (![⟨790050, by decide⟩,⟨790091, by decide⟩,⟨790128, by decide⟩,⟨790140, by decide⟩]) unmarked_context_12_105495_790141 node_context_12_105495_790141
  intro a
  fin_cases a
  · exact context_13_421980_790050
  · exact context_13_421981_790091
  · exact context_13_421982_790128
  · exact context_13_421983_790140

theorem unmarked_context_11_26373_790142 : frontier 10 ⟨790142, by decide⟩
    (prefixCache 11 26373) (prefixPartial 11 26373) = false := by
  decide +kernel

theorem node_context_11_26373_790142 : EJMOriginalGlobalDAGData.nodes 10 ⟨790142, by decide⟩ =
    .split (coordinate 11) (![⟨789807, by decide⟩,⟨789910, by decide⟩,⟨790013, by decide⟩,⟨790141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26373_790142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26373 ⟨790142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26373
    ⟨790142, by decide⟩ (by decide) (![⟨789807, by decide⟩,⟨789910, by decide⟩,⟨790013, by decide⟩,⟨790141, by decide⟩]) unmarked_context_11_26373_790142 node_context_11_26373_790142
  intro a
  fin_cases a
  · exact context_12_105492_789807
  · exact context_12_105493_789910
  · exact context_12_105494_790013
  · exact context_12_105495_790141

theorem selected_cut_31024 : selected 8 ⟨790162, by decide⟩
    (prefixPartial 13 421984) = some ⟨13, 2, 0, 790162, 421984, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_421984_790162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421984 ⟨790162, by decide⟩ :=
  accepted_of_selected 13 421984 ⟨790162, by decide⟩ ⟨13, 2, 0, 790162, 421984, 1257, 16384⟩
    (by decide) selected_cut_31024

theorem selected_cut_31025 : selected 8 ⟨790195, by decide⟩
    (prefixPartial 13 421985) = some ⟨13, 2, 0, 790195, 421985, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_421985_790195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421985 ⟨790195, by decide⟩ :=
  accepted_of_selected 13 421985 ⟨790195, by decide⟩ ⟨13, 2, 0, 790195, 421985, 2121, 16384⟩
    (by decide) selected_cut_31025

theorem selected_cut_31026 : selected 8 ⟨790222, by decide⟩
    (prefixPartial 13 421986) = some ⟨13, 2, 0, 790222, 421986, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_421986_790222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421986 ⟨790222, by decide⟩ :=
  accepted_of_selected 13 421986 ⟨790222, by decide⟩ ⟨13, 2, 0, 790222, 421986, 1509, 16384⟩
    (by decide) selected_cut_31026

theorem selected_cut_31027 : selected 8 ⟨790229, by decide⟩
    (prefixPartial 13 421987) = some ⟨13, 2, 0, 790229, 421987, 705, 16384⟩ := by
  decide +kernel

theorem context_13_421987_790229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421987 ⟨790229, by decide⟩ :=
  accepted_of_selected 13 421987 ⟨790229, by decide⟩ ⟨13, 2, 0, 790229, 421987, 705, 16384⟩
    (by decide) selected_cut_31027

theorem unmarked_context_12_105496_790230 : frontier 9 ⟨790230, by decide⟩
    (prefixCache 12 105496) (prefixPartial 12 105496) = false := by
  decide +kernel

theorem node_context_12_105496_790230 : EJMOriginalGlobalDAGData.nodes 9 ⟨790230, by decide⟩ =
    .split (coordinate 12) (![⟨790162, by decide⟩,⟨790195, by decide⟩,⟨790222, by decide⟩,⟨790229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105496_790230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105496 ⟨790230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105496
    ⟨790230, by decide⟩ (by decide) (![⟨790162, by decide⟩,⟨790195, by decide⟩,⟨790222, by decide⟩,⟨790229, by decide⟩]) unmarked_context_12_105496_790230 node_context_12_105496_790230
  intro a
  fin_cases a
  · exact context_13_421984_790162
  · exact context_13_421985_790195
  · exact context_13_421986_790222
  · exact context_13_421987_790229

theorem selected_cut_31028 : selected 8 ⟨790262, by decide⟩
    (prefixPartial 13 421988) = some ⟨13, 2, 0, 790262, 421988, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_421988_790262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421988 ⟨790262, by decide⟩ :=
  accepted_of_selected 13 421988 ⟨790262, by decide⟩ ⟨13, 2, 0, 790262, 421988, 1677, 16384⟩
    (by decide) selected_cut_31028

theorem selected_cut_31029 : selected 8 ⟨790299, by decide⟩
    (prefixPartial 13 421989) = some ⟨13, 2, 0, 790299, 421989, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_421989_790299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421989 ⟨790299, by decide⟩ :=
  accepted_of_selected 13 421989 ⟨790299, by decide⟩ ⟨13, 2, 0, 790299, 421989, 2245, 16384⟩
    (by decide) selected_cut_31029

theorem selected_cut_31030 : selected 8 ⟨790328, by decide⟩
    (prefixPartial 13 421990) = some ⟨13, 2, 0, 790328, 421990, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_421990_790328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421990 ⟨790328, by decide⟩ :=
  accepted_of_selected 13 421990 ⟨790328, by decide⟩ ⟨13, 2, 0, 790328, 421990, 1609, 16384⟩
    (by decide) selected_cut_31030

theorem selected_cut_31031 : selected 8 ⟨790336, by decide⟩
    (prefixPartial 13 421991) = some ⟨13, 2, 0, 790336, 421991, 825, 16384⟩ := by
  decide +kernel

theorem context_13_421991_790336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421991 ⟨790336, by decide⟩ :=
  accepted_of_selected 13 421991 ⟨790336, by decide⟩ ⟨13, 2, 0, 790336, 421991, 825, 16384⟩
    (by decide) selected_cut_31031

theorem unmarked_context_12_105497_790337 : frontier 9 ⟨790337, by decide⟩
    (prefixCache 12 105497) (prefixPartial 12 105497) = false := by
  decide +kernel

theorem node_context_12_105497_790337 : EJMOriginalGlobalDAGData.nodes 9 ⟨790337, by decide⟩ =
    .split (coordinate 12) (![⟨790262, by decide⟩,⟨790299, by decide⟩,⟨790328, by decide⟩,⟨790336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105497_790337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105497 ⟨790337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105497
    ⟨790337, by decide⟩ (by decide) (![⟨790262, by decide⟩,⟨790299, by decide⟩,⟨790328, by decide⟩,⟨790336, by decide⟩]) unmarked_context_12_105497_790337 node_context_12_105497_790337
  intro a
  fin_cases a
  · exact context_13_421988_790262
  · exact context_13_421989_790299
  · exact context_13_421990_790328
  · exact context_13_421991_790336

theorem selected_cut_31032 : selected 8 ⟨790362, by decide⟩
    (prefixPartial 13 421992) = some ⟨13, 2, 0, 790362, 421992, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_421992_790362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421992 ⟨790362, by decide⟩ :=
  accepted_of_selected 13 421992 ⟨790362, by decide⟩ ⟨13, 2, 0, 790362, 421992, 1433, 16384⟩
    (by decide) selected_cut_31032

theorem selected_cut_31033 : selected 8 ⟨790396, by decide⟩
    (prefixPartial 13 421993) = some ⟨13, 2, 0, 790396, 421993, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_421993_790396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421993 ⟨790396, by decide⟩ :=
  accepted_of_selected 13 421993 ⟨790396, by decide⟩ ⟨13, 2, 0, 790396, 421993, 2133, 16384⟩
    (by decide) selected_cut_31033

theorem selected_cut_31034 : selected 8 ⟨790415, by decide⟩
    (prefixPartial 13 421994) = some ⟨13, 2, 0, 790415, 421994, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_421994_790415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421994 ⟨790415, by decide⟩ :=
  accepted_of_selected 13 421994 ⟨790415, by decide⟩ ⟨13, 2, 0, 790415, 421994, 1137, 16384⟩
    (by decide) selected_cut_31034

theorem selected_cut_31035 : selected 8 ⟨790423, by decide⟩
    (prefixPartial 13 421995) = some ⟨13, 2, 0, 790423, 421995, 825, 16384⟩ := by
  decide +kernel

theorem context_13_421995_790423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421995 ⟨790423, by decide⟩ :=
  accepted_of_selected 13 421995 ⟨790423, by decide⟩ ⟨13, 2, 0, 790423, 421995, 825, 16384⟩
    (by decide) selected_cut_31035

theorem unmarked_context_12_105498_790424 : frontier 9 ⟨790424, by decide⟩
    (prefixCache 12 105498) (prefixPartial 12 105498) = false := by
  decide +kernel

theorem node_context_12_105498_790424 : EJMOriginalGlobalDAGData.nodes 9 ⟨790424, by decide⟩ =
    .split (coordinate 12) (![⟨790362, by decide⟩,⟨790396, by decide⟩,⟨790415, by decide⟩,⟨790423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105498_790424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105498 ⟨790424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105498
    ⟨790424, by decide⟩ (by decide) (![⟨790362, by decide⟩,⟨790396, by decide⟩,⟨790415, by decide⟩,⟨790423, by decide⟩]) unmarked_context_12_105498_790424 node_context_12_105498_790424
  intro a
  fin_cases a
  · exact context_13_421992_790362
  · exact context_13_421993_790396
  · exact context_13_421994_790415
  · exact context_13_421995_790423

theorem selected_cut_31036 : selected 8 ⟨790459, by decide⟩
    (prefixPartial 13 421996) = some ⟨13, 2, 0, 790459, 421996, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_421996_790459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421996 ⟨790459, by decide⟩ :=
  accepted_of_selected 13 421996 ⟨790459, by decide⟩ ⟨13, 2, 0, 790459, 421996, 1621, 16384⟩
    (by decide) selected_cut_31036

theorem selected_cut_31037 : selected 8 ⟨790490, by decide⟩
    (prefixPartial 13 421997) = some ⟨13, 2, 0, 790490, 421997, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_421997_790490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421997 ⟨790490, by decide⟩ :=
  accepted_of_selected 13 421997 ⟨790490, by decide⟩ ⟨13, 2, 0, 790490, 421997, 2265, 16384⟩
    (by decide) selected_cut_31037

theorem selected_cut_31038 : selected 8 ⟨790523, by decide⟩
    (prefixPartial 13 421998) = some ⟨13, 2, 0, 790523, 421998, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_421998_790523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421998 ⟨790523, by decide⟩ :=
  accepted_of_selected 13 421998 ⟨790523, by decide⟩ ⟨13, 2, 0, 790523, 421998, 1701, 16384⟩
    (by decide) selected_cut_31038

theorem selected_cut_31039 : selected 8 ⟨790532, by decide⟩
    (prefixPartial 13 421999) = some ⟨13, 2, 0, 790532, 421999, 869, 16384⟩ := by
  decide +kernel

theorem context_13_421999_790532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421999 ⟨790532, by decide⟩ :=
  accepted_of_selected 13 421999 ⟨790532, by decide⟩ ⟨13, 2, 0, 790532, 421999, 869, 16384⟩
    (by decide) selected_cut_31039

theorem unmarked_context_12_105499_790533 : frontier 9 ⟨790533, by decide⟩
    (prefixCache 12 105499) (prefixPartial 12 105499) = false := by
  decide +kernel

theorem node_context_12_105499_790533 : EJMOriginalGlobalDAGData.nodes 9 ⟨790533, by decide⟩ =
    .split (coordinate 12) (![⟨790459, by decide⟩,⟨790490, by decide⟩,⟨790523, by decide⟩,⟨790532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105499_790533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105499 ⟨790533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105499
    ⟨790533, by decide⟩ (by decide) (![⟨790459, by decide⟩,⟨790490, by decide⟩,⟨790523, by decide⟩,⟨790532, by decide⟩]) unmarked_context_12_105499_790533 node_context_12_105499_790533
  intro a
  fin_cases a
  · exact context_13_421996_790459
  · exact context_13_421997_790490
  · exact context_13_421998_790523
  · exact context_13_421999_790532

theorem unmarked_context_11_26374_790534 : frontier 10 ⟨790534, by decide⟩
    (prefixCache 11 26374) (prefixPartial 11 26374) = false := by
  decide +kernel

theorem node_context_11_26374_790534 : EJMOriginalGlobalDAGData.nodes 10 ⟨790534, by decide⟩ =
    .split (coordinate 11) (![⟨790230, by decide⟩,⟨790337, by decide⟩,⟨790424, by decide⟩,⟨790533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26374_790534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26374 ⟨790534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26374
    ⟨790534, by decide⟩ (by decide) (![⟨790230, by decide⟩,⟨790337, by decide⟩,⟨790424, by decide⟩,⟨790533, by decide⟩]) unmarked_context_11_26374_790534 node_context_11_26374_790534
  intro a
  fin_cases a
  · exact context_12_105496_790230
  · exact context_12_105497_790337
  · exact context_12_105498_790424
  · exact context_12_105499_790533

theorem selected_cut_31040 : selected 8 ⟨790552, by decide⟩
    (prefixPartial 13 422000) = some ⟨13, 2, 0, 790552, 422000, 985, 16384⟩ := by
  decide +kernel

theorem context_13_422000_790552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422000 ⟨790552, by decide⟩ :=
  accepted_of_selected 13 422000 ⟨790552, by decide⟩ ⟨13, 2, 0, 790552, 422000, 985, 16384⟩
    (by decide) selected_cut_31040

theorem selected_cut_31041 : selected 8 ⟨790583, by decide⟩
    (prefixPartial 13 422001) = some ⟨13, 2, 0, 790583, 422001, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_422001_790583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422001 ⟨790583, by decide⟩ :=
  accepted_of_selected 13 422001 ⟨790583, by decide⟩ ⟨13, 2, 0, 790583, 422001, 1853, 16384⟩
    (by decide) selected_cut_31041

theorem selected_cut_31042 : selected 8 ⟨790603, by decide⟩
    (prefixPartial 13 422002) = some ⟨13, 2, 0, 790603, 422002, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_422002_790603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422002 ⟨790603, by decide⟩ :=
  accepted_of_selected 13 422002 ⟨790603, by decide⟩ ⟨13, 2, 0, 790603, 422002, 1365, 16384⟩
    (by decide) selected_cut_31042

theorem selected_cut_31043 : selected 8 ⟨790610, by decide⟩
    (prefixPartial 13 422003) = some ⟨13, 2, 0, 790610, 422003, 749, 16384⟩ := by
  decide +kernel

theorem context_13_422003_790610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422003 ⟨790610, by decide⟩ :=
  accepted_of_selected 13 422003 ⟨790610, by decide⟩ ⟨13, 2, 0, 790610, 422003, 749, 16384⟩
    (by decide) selected_cut_31043

theorem unmarked_context_12_105500_790611 : frontier 9 ⟨790611, by decide⟩
    (prefixCache 12 105500) (prefixPartial 12 105500) = false := by
  decide +kernel

theorem node_context_12_105500_790611 : EJMOriginalGlobalDAGData.nodes 9 ⟨790611, by decide⟩ =
    .split (coordinate 12) (![⟨790552, by decide⟩,⟨790583, by decide⟩,⟨790603, by decide⟩,⟨790610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105500_790611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105500 ⟨790611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105500
    ⟨790611, by decide⟩ (by decide) (![⟨790552, by decide⟩,⟨790583, by decide⟩,⟨790603, by decide⟩,⟨790610, by decide⟩]) unmarked_context_12_105500_790611 node_context_12_105500_790611
  intro a
  fin_cases a
  · exact context_13_422000_790552
  · exact context_13_422001_790583
  · exact context_13_422002_790603
  · exact context_13_422003_790610

theorem selected_cut_31044 : selected 8 ⟨790640, by decide⟩
    (prefixPartial 13 422004) = some ⟨13, 2, 0, 790640, 422004, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_422004_790640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422004 ⟨790640, by decide⟩ :=
  accepted_of_selected 13 422004 ⟨790640, by decide⟩ ⟨13, 2, 0, 790640, 422004, 1393, 16384⟩
    (by decide) selected_cut_31044

theorem selected_cut_31045 : selected 8 ⟨790678, by decide⟩
    (prefixPartial 13 422005) = some ⟨13, 2, 0, 790678, 422005, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_422005_790678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422005 ⟨790678, by decide⟩ :=
  accepted_of_selected 13 422005 ⟨790678, by decide⟩ ⟨13, 2, 0, 790678, 422005, 2053, 16384⟩
    (by decide) selected_cut_31045

theorem selected_cut_31046 : selected 8 ⟨790707, by decide⟩
    (prefixPartial 13 422006) = some ⟨13, 2, 0, 790707, 422006, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_422006_790707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422006 ⟨790707, by decide⟩ :=
  accepted_of_selected 13 422006 ⟨790707, by decide⟩ ⟨13, 2, 0, 790707, 422006, 1569, 16384⟩
    (by decide) selected_cut_31046

theorem selected_cut_31047 : selected 8 ⟨790715, by decide⟩
    (prefixPartial 13 422007) = some ⟨13, 2, 0, 790715, 422007, 833, 16384⟩ := by
  decide +kernel

theorem context_13_422007_790715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422007 ⟨790715, by decide⟩ :=
  accepted_of_selected 13 422007 ⟨790715, by decide⟩ ⟨13, 2, 0, 790715, 422007, 833, 16384⟩
    (by decide) selected_cut_31047

theorem unmarked_context_12_105501_790716 : frontier 9 ⟨790716, by decide⟩
    (prefixCache 12 105501) (prefixPartial 12 105501) = false := by
  decide +kernel

theorem node_context_12_105501_790716 : EJMOriginalGlobalDAGData.nodes 9 ⟨790716, by decide⟩ =
    .split (coordinate 12) (![⟨790640, by decide⟩,⟨790678, by decide⟩,⟨790707, by decide⟩,⟨790715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105501_790716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105501 ⟨790716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105501
    ⟨790716, by decide⟩ (by decide) (![⟨790640, by decide⟩,⟨790678, by decide⟩,⟨790707, by decide⟩,⟨790715, by decide⟩]) unmarked_context_12_105501_790716 node_context_12_105501_790716
  intro a
  fin_cases a
  · exact context_13_422004_790640
  · exact context_13_422005_790678
  · exact context_13_422006_790707
  · exact context_13_422007_790715

theorem selected_cut_31048 : selected 8 ⟨790739, by decide⟩
    (prefixPartial 13 422008) = some ⟨13, 2, 0, 790739, 422008, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_422008_790739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422008 ⟨790739, by decide⟩ :=
  accepted_of_selected 13 422008 ⟨790739, by decide⟩ ⟨13, 2, 0, 790739, 422008, 1249, 16384⟩
    (by decide) selected_cut_31048

theorem selected_cut_31049 : selected 8 ⟨790771, by decide⟩
    (prefixPartial 13 422009) = some ⟨13, 2, 0, 790771, 422009, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_422009_790771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422009 ⟨790771, by decide⟩ :=
  accepted_of_selected 13 422009 ⟨790771, by decide⟩ ⟨13, 2, 0, 790771, 422009, 1953, 16384⟩
    (by decide) selected_cut_31049

theorem selected_cut_31050 : selected 8 ⟨790790, by decide⟩
    (prefixPartial 13 422010) = some ⟨13, 2, 0, 790790, 422010, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_422010_790790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422010 ⟨790790, by decide⟩ :=
  accepted_of_selected 13 422010 ⟨790790, by decide⟩ ⟨13, 2, 0, 790790, 422010, 1253, 16384⟩
    (by decide) selected_cut_31050

theorem selected_cut_31051 : selected 8 ⟨790795, by decide⟩
    (prefixPartial 13 422011) = some ⟨13, 2, 0, 790795, 422011, 853, 16384⟩ := by
  decide +kernel

theorem context_13_422011_790795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422011 ⟨790795, by decide⟩ :=
  accepted_of_selected 13 422011 ⟨790795, by decide⟩ ⟨13, 2, 0, 790795, 422011, 853, 16384⟩
    (by decide) selected_cut_31051

theorem unmarked_context_12_105502_790796 : frontier 9 ⟨790796, by decide⟩
    (prefixCache 12 105502) (prefixPartial 12 105502) = false := by
  decide +kernel

theorem node_context_12_105502_790796 : EJMOriginalGlobalDAGData.nodes 9 ⟨790796, by decide⟩ =
    .split (coordinate 12) (![⟨790739, by decide⟩,⟨790771, by decide⟩,⟨790790, by decide⟩,⟨790795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105502_790796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105502 ⟨790796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105502
    ⟨790796, by decide⟩ (by decide) (![⟨790739, by decide⟩,⟨790771, by decide⟩,⟨790790, by decide⟩,⟨790795, by decide⟩]) unmarked_context_12_105502_790796 node_context_12_105502_790796
  intro a
  fin_cases a
  · exact context_13_422008_790739
  · exact context_13_422009_790771
  · exact context_13_422010_790790
  · exact context_13_422011_790795

theorem selected_cut_31052 : selected 8 ⟨790827, by decide⟩
    (prefixPartial 13 422012) = some ⟨13, 2, 0, 790827, 422012, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_422012_790827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422012 ⟨790827, by decide⟩ :=
  accepted_of_selected 13 422012 ⟨790827, by decide⟩ ⟨13, 2, 0, 790827, 422012, 1121, 16384⟩
    (by decide) selected_cut_31052

theorem selected_cut_31053 : selected 8 ⟨790854, by decide⟩
    (prefixPartial 13 422013) = some ⟨13, 2, 0, 790854, 422013, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_422013_790854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422013 ⟨790854, by decide⟩ :=
  accepted_of_selected 13 422013 ⟨790854, by decide⟩ ⟨13, 2, 0, 790854, 422013, 1797, 16384⟩
    (by decide) selected_cut_31053

theorem selected_cut_31054 : selected 8 ⟨790879, by decide⟩
    (prefixPartial 13 422014) = some ⟨13, 2, 0, 790879, 422014, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_422014_790879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422014 ⟨790879, by decide⟩ :=
  accepted_of_selected 13 422014 ⟨790879, by decide⟩ ⟨13, 2, 0, 790879, 422014, 1485, 16384⟩
    (by decide) selected_cut_31054

theorem selected_cut_31055 : selected 8 ⟨790884, by decide⟩
    (prefixPartial 13 422015) = some ⟨13, 2, 0, 790884, 422015, 817, 16384⟩ := by
  decide +kernel

theorem context_13_422015_790884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422015 ⟨790884, by decide⟩ :=
  accepted_of_selected 13 422015 ⟨790884, by decide⟩ ⟨13, 2, 0, 790884, 422015, 817, 16384⟩
    (by decide) selected_cut_31055

theorem unmarked_context_12_105503_790885 : frontier 9 ⟨790885, by decide⟩
    (prefixCache 12 105503) (prefixPartial 12 105503) = false := by
  decide +kernel

theorem node_context_12_105503_790885 : EJMOriginalGlobalDAGData.nodes 9 ⟨790885, by decide⟩ =
    .split (coordinate 12) (![⟨790827, by decide⟩,⟨790854, by decide⟩,⟨790879, by decide⟩,⟨790884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105503_790885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105503 ⟨790885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105503
    ⟨790885, by decide⟩ (by decide) (![⟨790827, by decide⟩,⟨790854, by decide⟩,⟨790879, by decide⟩,⟨790884, by decide⟩]) unmarked_context_12_105503_790885 node_context_12_105503_790885
  intro a
  fin_cases a
  · exact context_13_422012_790827
  · exact context_13_422013_790854
  · exact context_13_422014_790879
  · exact context_13_422015_790884

theorem unmarked_context_11_26375_790886 : frontier 10 ⟨790886, by decide⟩
    (prefixCache 11 26375) (prefixPartial 11 26375) = false := by
  decide +kernel

theorem node_context_11_26375_790886 : EJMOriginalGlobalDAGData.nodes 10 ⟨790886, by decide⟩ =
    .split (coordinate 11) (![⟨790611, by decide⟩,⟨790716, by decide⟩,⟨790796, by decide⟩,⟨790885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26375_790886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26375 ⟨790886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26375
    ⟨790886, by decide⟩ (by decide) (![⟨790611, by decide⟩,⟨790716, by decide⟩,⟨790796, by decide⟩,⟨790885, by decide⟩]) unmarked_context_11_26375_790886 node_context_11_26375_790886
  intro a
  fin_cases a
  · exact context_12_105500_790611
  · exact context_12_105501_790716
  · exact context_12_105502_790796
  · exact context_12_105503_790885

theorem unmarked_context_10_6593_790887 : frontier 11 ⟨790887, by decide⟩
    (prefixCache 10 6593) (prefixPartial 10 6593) = false := by
  decide +kernel

theorem node_context_10_6593_790887 : EJMOriginalGlobalDAGData.nodes 11 ⟨790887, by decide⟩ =
    .split (coordinate 10) (![⟨789695, by decide⟩,⟨790142, by decide⟩,⟨790534, by decide⟩,⟨790886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6593_790887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6593 ⟨790887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6593
    ⟨790887, by decide⟩ (by decide) (![⟨789695, by decide⟩,⟨790142, by decide⟩,⟨790534, by decide⟩,⟨790886, by decide⟩]) unmarked_context_10_6593_790887 node_context_10_6593_790887
  intro a
  fin_cases a
  · exact context_11_26372_789695
  · exact context_11_26373_790142
  · exact context_11_26374_790534
  · exact context_11_26375_790886

theorem selected_cut_31056 : selected 9 ⟨790888, by decide⟩
    (prefixPartial 12 105504) = some ⟨12, 1, 0, 790888, 105504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105504_790888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105504 ⟨790888, by decide⟩ :=
  accepted_of_selected 12 105504 ⟨790888, by decide⟩ ⟨12, 1, 0, 790888, 105504, 1, 65536⟩
    (by decide) selected_cut_31056

theorem selected_cut_31057 : selected 8 ⟨790928, by decide⟩
    (prefixPartial 13 422020) = some ⟨13, 2, 0, 790928, 422020, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_422020_790928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422020 ⟨790928, by decide⟩ :=
  accepted_of_selected 13 422020 ⟨790928, by decide⟩ ⟨13, 2, 0, 790928, 422020, 1281, 16384⟩
    (by decide) selected_cut_31057

theorem selected_cut_31058 : selected 8 ⟨790972, by decide⟩
    (prefixPartial 13 422021) = some ⟨13, 2, 0, 790972, 422021, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_422021_790972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422021 ⟨790972, by decide⟩ :=
  accepted_of_selected 13 422021 ⟨790972, by decide⟩ ⟨13, 2, 0, 790972, 422021, 2089, 16384⟩
    (by decide) selected_cut_31058

theorem selected_cut_31059 : selected 8 ⟨790993, by decide⟩
    (prefixPartial 13 422022) = some ⟨13, 2, 0, 790993, 422022, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_422022_790993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422022 ⟨790993, by decide⟩ :=
  accepted_of_selected 13 422022 ⟨790993, by decide⟩ ⟨13, 2, 0, 790993, 422022, 1161, 16384⟩
    (by decide) selected_cut_31059

theorem selected_cut_31060 : selected 8 ⟨791003, by decide⟩
    (prefixPartial 13 422023) = some ⟨13, 2, 0, 791003, 422023, 845, 16384⟩ := by
  decide +kernel

theorem context_13_422023_791003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422023 ⟨791003, by decide⟩ :=
  accepted_of_selected 13 422023 ⟨791003, by decide⟩ ⟨13, 2, 0, 791003, 422023, 845, 16384⟩
    (by decide) selected_cut_31060

theorem unmarked_context_12_105505_791004 : frontier 9 ⟨791004, by decide⟩
    (prefixCache 12 105505) (prefixPartial 12 105505) = false := by
  decide +kernel

theorem node_context_12_105505_791004 : EJMOriginalGlobalDAGData.nodes 9 ⟨791004, by decide⟩ =
    .split (coordinate 12) (![⟨790928, by decide⟩,⟨790972, by decide⟩,⟨790993, by decide⟩,⟨791003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105505_791004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105505 ⟨791004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105505
    ⟨791004, by decide⟩ (by decide) (![⟨790928, by decide⟩,⟨790972, by decide⟩,⟨790993, by decide⟩,⟨791003, by decide⟩]) unmarked_context_12_105505_791004 node_context_12_105505_791004
  intro a
  fin_cases a
  · exact context_13_422020_790928
  · exact context_13_422021_790972
  · exact context_13_422022_790993
  · exact context_13_422023_791003

theorem selected_cut_31061 : selected 8 ⟨791032, by decide⟩
    (prefixPartial 13 422024) = some ⟨13, 2, 0, 791032, 422024, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_422024_791032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422024 ⟨791032, by decide⟩ :=
  accepted_of_selected 13 422024 ⟨791032, by decide⟩ ⟨13, 2, 0, 791032, 422024, 1089, 16384⟩
    (by decide) selected_cut_31061

theorem selected_cut_31062 : selected 8 ⟨791066, by decide⟩
    (prefixPartial 13 422025) = some ⟨13, 2, 0, 791066, 422025, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_422025_791066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422025 ⟨791066, by decide⟩ :=
  accepted_of_selected 13 422025 ⟨791066, by decide⟩ ⟨13, 2, 0, 791066, 422025, 2209, 16384⟩
    (by decide) selected_cut_31062

theorem selected_cut_31063 : selected 8 ⟨791084, by decide⟩
    (prefixPartial 13 422026) = some ⟨13, 2, 0, 791084, 422026, 965, 16384⟩ := by
  decide +kernel

theorem context_13_422026_791084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422026 ⟨791084, by decide⟩ :=
  accepted_of_selected 13 422026 ⟨791084, by decide⟩ ⟨13, 2, 0, 791084, 422026, 965, 16384⟩
    (by decide) selected_cut_31063

theorem selected_cut_31064 : selected 8 ⟨791092, by decide⟩
    (prefixPartial 13 422027) = some ⟨13, 2, 0, 791092, 422027, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_422027_791092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422027 ⟨791092, by decide⟩ :=
  accepted_of_selected 13 422027 ⟨791092, by decide⟩ ⟨13, 2, 0, 791092, 422027, 1017, 16384⟩
    (by decide) selected_cut_31064

theorem unmarked_context_12_105506_791093 : frontier 9 ⟨791093, by decide⟩
    (prefixCache 12 105506) (prefixPartial 12 105506) = false := by
  decide +kernel

theorem node_context_12_105506_791093 : EJMOriginalGlobalDAGData.nodes 9 ⟨791093, by decide⟩ =
    .split (coordinate 12) (![⟨791032, by decide⟩,⟨791066, by decide⟩,⟨791084, by decide⟩,⟨791092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105506_791093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105506 ⟨791093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105506
    ⟨791093, by decide⟩ (by decide) (![⟨791032, by decide⟩,⟨791066, by decide⟩,⟨791084, by decide⟩,⟨791092, by decide⟩]) unmarked_context_12_105506_791093 node_context_12_105506_791093
  intro a
  fin_cases a
  · exact context_13_422024_791032
  · exact context_13_422025_791066
  · exact context_13_422026_791084
  · exact context_13_422027_791092

theorem selected_cut_31065 : selected 8 ⟨791120, by decide⟩
    (prefixPartial 13 422028) = some ⟨13, 2, 0, 791120, 422028, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_422028_791120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422028 ⟨791120, by decide⟩ :=
  accepted_of_selected 13 422028 ⟨791120, by decide⟩ ⟨13, 2, 0, 791120, 422028, 1093, 16384⟩
    (by decide) selected_cut_31065

theorem selected_cut_31066 : selected 8 ⟨791150, by decide⟩
    (prefixPartial 13 422029) = some ⟨13, 2, 0, 791150, 422029, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_422029_791150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422029 ⟨791150, by decide⟩ :=
  accepted_of_selected 13 422029 ⟨791150, by decide⟩ ⟨13, 2, 0, 791150, 422029, 2033, 16384⟩
    (by decide) selected_cut_31066

theorem selected_cut_31067 : selected 8 ⟨791174, by decide⟩
    (prefixPartial 13 422030) = some ⟨13, 2, 0, 791174, 422030, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_422030_791174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422030 ⟨791174, by decide⟩ :=
  accepted_of_selected 13 422030 ⟨791174, by decide⟩ ⟨13, 2, 0, 791174, 422030, 1289, 16384⟩
    (by decide) selected_cut_31067

theorem selected_cut_31068 : selected 8 ⟨791186, by decide⟩
    (prefixPartial 13 422031) = some ⟨13, 2, 0, 791186, 422031, 961, 16384⟩ := by
  decide +kernel

theorem context_13_422031_791186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422031 ⟨791186, by decide⟩ :=
  accepted_of_selected 13 422031 ⟨791186, by decide⟩ ⟨13, 2, 0, 791186, 422031, 961, 16384⟩
    (by decide) selected_cut_31068

theorem unmarked_context_12_105507_791187 : frontier 9 ⟨791187, by decide⟩
    (prefixCache 12 105507) (prefixPartial 12 105507) = false := by
  decide +kernel

theorem node_context_12_105507_791187 : EJMOriginalGlobalDAGData.nodes 9 ⟨791187, by decide⟩ =
    .split (coordinate 12) (![⟨791120, by decide⟩,⟨791150, by decide⟩,⟨791174, by decide⟩,⟨791186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105507_791187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105507 ⟨791187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105507
    ⟨791187, by decide⟩ (by decide) (![⟨791120, by decide⟩,⟨791150, by decide⟩,⟨791174, by decide⟩,⟨791186, by decide⟩]) unmarked_context_12_105507_791187 node_context_12_105507_791187
  intro a
  fin_cases a
  · exact context_13_422028_791120
  · exact context_13_422029_791150
  · exact context_13_422030_791174
  · exact context_13_422031_791186

theorem unmarked_context_11_26376_791188 : frontier 10 ⟨791188, by decide⟩
    (prefixCache 11 26376) (prefixPartial 11 26376) = false := by
  decide +kernel

theorem node_context_11_26376_791188 : EJMOriginalGlobalDAGData.nodes 10 ⟨791188, by decide⟩ =
    .split (coordinate 11) (![⟨790888, by decide⟩,⟨791004, by decide⟩,⟨791093, by decide⟩,⟨791187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26376_791188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26376 ⟨791188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26376
    ⟨791188, by decide⟩ (by decide) (![⟨790888, by decide⟩,⟨791004, by decide⟩,⟨791093, by decide⟩,⟨791187, by decide⟩]) unmarked_context_11_26376_791188 node_context_11_26376_791188
  intro a
  fin_cases a
  · exact context_12_105504_790888
  · exact context_12_105505_791004
  · exact context_12_105506_791093
  · exact context_12_105507_791187

theorem selected_cut_31069 : selected 8 ⟨791214, by decide⟩
    (prefixPartial 13 422032) = some ⟨13, 2, 0, 791214, 422032, 937, 16384⟩ := by
  decide +kernel

theorem context_13_422032_791214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422032 ⟨791214, by decide⟩ :=
  accepted_of_selected 13 422032 ⟨791214, by decide⟩ ⟨13, 2, 0, 791214, 422032, 937, 16384⟩
    (by decide) selected_cut_31069

theorem selected_cut_31070 : selected 8 ⟨791245, by decide⟩
    (prefixPartial 13 422033) = some ⟨13, 2, 0, 791245, 422033, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_422033_791245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422033 ⟨791245, by decide⟩ :=
  accepted_of_selected 13 422033 ⟨791245, by decide⟩ ⟨13, 2, 0, 791245, 422033, 1945, 16384⟩
    (by decide) selected_cut_31070

theorem selected_cut_31071 : selected 8 ⟨791271, by decide⟩
    (prefixPartial 13 422034) = some ⟨13, 2, 0, 791271, 422034, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_422034_791271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422034 ⟨791271, by decide⟩ :=
  accepted_of_selected 13 422034 ⟨791271, by decide⟩ ⟨13, 2, 0, 791271, 422034, 1441, 16384⟩
    (by decide) selected_cut_31071

theorem selected_cut_31072 : selected 8 ⟨791280, by decide⟩
    (prefixPartial 13 422035) = some ⟨13, 2, 0, 791280, 422035, 897, 16384⟩ := by
  decide +kernel

theorem context_13_422035_791280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422035 ⟨791280, by decide⟩ :=
  accepted_of_selected 13 422035 ⟨791280, by decide⟩ ⟨13, 2, 0, 791280, 422035, 897, 16384⟩
    (by decide) selected_cut_31072

theorem unmarked_context_12_105508_791281 : frontier 9 ⟨791281, by decide⟩
    (prefixCache 12 105508) (prefixPartial 12 105508) = false := by
  decide +kernel

theorem node_context_12_105508_791281 : EJMOriginalGlobalDAGData.nodes 9 ⟨791281, by decide⟩ =
    .split (coordinate 12) (![⟨791214, by decide⟩,⟨791245, by decide⟩,⟨791271, by decide⟩,⟨791280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105508_791281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105508 ⟨791281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105508
    ⟨791281, by decide⟩ (by decide) (![⟨791214, by decide⟩,⟨791245, by decide⟩,⟨791271, by decide⟩,⟨791280, by decide⟩]) unmarked_context_12_105508_791281 node_context_12_105508_791281
  intro a
  fin_cases a
  · exact context_13_422032_791214
  · exact context_13_422033_791245
  · exact context_13_422034_791271
  · exact context_13_422035_791280

theorem selected_cut_31073 : selected 8 ⟨791310, by decide⟩
    (prefixPartial 13 422036) = some ⟨13, 2, 0, 791310, 422036, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_422036_791310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422036 ⟨791310, by decide⟩ :=
  accepted_of_selected 13 422036 ⟨791310, by decide⟩ ⟨13, 2, 0, 791310, 422036, 1145, 16384⟩
    (by decide) selected_cut_31073

theorem selected_cut_31074 : selected 8 ⟨791349, by decide⟩
    (prefixPartial 13 422037) = some ⟨13, 2, 0, 791349, 422037, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_422037_791349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422037 ⟨791349, by decide⟩ :=
  accepted_of_selected 13 422037 ⟨791349, by decide⟩ ⟨13, 2, 0, 791349, 422037, 1949, 16384⟩
    (by decide) selected_cut_31074

theorem selected_cut_31075 : selected 8 ⟨791369, by decide⟩
    (prefixPartial 13 422038) = some ⟨13, 2, 0, 791369, 422038, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_422038_791369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422038 ⟨791369, by decide⟩ :=
  accepted_of_selected 13 422038 ⟨791369, by decide⟩ ⟨13, 2, 0, 791369, 422038, 1309, 16384⟩
    (by decide) selected_cut_31075

theorem selected_cut_31076 : selected 8 ⟨791378, by decide⟩
    (prefixPartial 13 422039) = some ⟨13, 2, 0, 791378, 422039, 817, 16384⟩ := by
  decide +kernel

theorem context_13_422039_791378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422039 ⟨791378, by decide⟩ :=
  accepted_of_selected 13 422039 ⟨791378, by decide⟩ ⟨13, 2, 0, 791378, 422039, 817, 16384⟩
    (by decide) selected_cut_31076

theorem unmarked_context_12_105509_791379 : frontier 9 ⟨791379, by decide⟩
    (prefixCache 12 105509) (prefixPartial 12 105509) = false := by
  decide +kernel

theorem node_context_12_105509_791379 : EJMOriginalGlobalDAGData.nodes 9 ⟨791379, by decide⟩ =
    .split (coordinate 12) (![⟨791310, by decide⟩,⟨791349, by decide⟩,⟨791369, by decide⟩,⟨791378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105509_791379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105509 ⟨791379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105509
    ⟨791379, by decide⟩ (by decide) (![⟨791310, by decide⟩,⟨791349, by decide⟩,⟨791369, by decide⟩,⟨791378, by decide⟩]) unmarked_context_12_105509_791379 node_context_12_105509_791379
  intro a
  fin_cases a
  · exact context_13_422036_791310
  · exact context_13_422037_791349
  · exact context_13_422038_791369
  · exact context_13_422039_791378

theorem selected_cut_31077 : selected 8 ⟨791410, by decide⟩
    (prefixPartial 13 422040) = some ⟨13, 2, 0, 791410, 422040, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_422040_791410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422040 ⟨791410, by decide⟩ :=
  accepted_of_selected 13 422040 ⟨791410, by decide⟩ ⟨13, 2, 0, 791410, 422040, 1121, 16384⟩
    (by decide) selected_cut_31077

theorem selected_cut_31078 : selected 8 ⟨791456, by decide⟩
    (prefixPartial 13 422041) = some ⟨13, 2, 0, 791456, 422041, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_422041_791456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422041 ⟨791456, by decide⟩ :=
  accepted_of_selected 13 422041 ⟨791456, by decide⟩ ⟨13, 2, 0, 791456, 422041, 2377, 16384⟩
    (by decide) selected_cut_31078

theorem selected_cut_31079 : selected 8 ⟨791481, by decide⟩
    (prefixPartial 13 422042) = some ⟨13, 2, 0, 791481, 422042, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_422042_791481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422042 ⟨791481, by decide⟩ :=
  accepted_of_selected 13 422042 ⟨791481, by decide⟩ ⟨13, 2, 0, 791481, 422042, 1221, 16384⟩
    (by decide) selected_cut_31079

theorem selected_cut_31080 : selected 8 ⟨791492, by decide⟩
    (prefixPartial 13 422043) = some ⟨13, 2, 0, 791492, 422043, 937, 16384⟩ := by
  decide +kernel

theorem context_13_422043_791492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422043 ⟨791492, by decide⟩ :=
  accepted_of_selected 13 422043 ⟨791492, by decide⟩ ⟨13, 2, 0, 791492, 422043, 937, 16384⟩
    (by decide) selected_cut_31080

theorem unmarked_context_12_105510_791493 : frontier 9 ⟨791493, by decide⟩
    (prefixCache 12 105510) (prefixPartial 12 105510) = false := by
  decide +kernel

theorem node_context_12_105510_791493 : EJMOriginalGlobalDAGData.nodes 9 ⟨791493, by decide⟩ =
    .split (coordinate 12) (![⟨791410, by decide⟩,⟨791456, by decide⟩,⟨791481, by decide⟩,⟨791492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105510_791493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105510 ⟨791493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105510
    ⟨791493, by decide⟩ (by decide) (![⟨791410, by decide⟩,⟨791456, by decide⟩,⟨791481, by decide⟩,⟨791492, by decide⟩]) unmarked_context_12_105510_791493 node_context_12_105510_791493
  intro a
  fin_cases a
  · exact context_13_422040_791410
  · exact context_13_422041_791456
  · exact context_13_422042_791481
  · exact context_13_422043_791492

theorem selected_cut_31081 : selected 8 ⟨791517, by decide⟩
    (prefixPartial 13 422044) = some ⟨13, 2, 0, 791517, 422044, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_422044_791517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422044 ⟨791517, by decide⟩ :=
  accepted_of_selected 13 422044 ⟨791517, by decide⟩ ⟨13, 2, 0, 791517, 422044, 1145, 16384⟩
    (by decide) selected_cut_31081

theorem selected_cut_31082 : selected 8 ⟨791559, by decide⟩
    (prefixPartial 13 422045) = some ⟨13, 2, 0, 791559, 422045, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_422045_791559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422045 ⟨791559, by decide⟩ :=
  accepted_of_selected 13 422045 ⟨791559, by decide⟩ ⟨13, 2, 0, 791559, 422045, 2273, 16384⟩
    (by decide) selected_cut_31082

theorem selected_cut_31083 : selected 8 ⟨791594, by decide⟩
    (prefixPartial 13 422046) = some ⟨13, 2, 0, 791594, 422046, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_422046_791594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422046 ⟨791594, by decide⟩ :=
  accepted_of_selected 13 422046 ⟨791594, by decide⟩ ⟨13, 2, 0, 791594, 422046, 1593, 16384⟩
    (by decide) selected_cut_31083

theorem selected_cut_31084 : selected 8 ⟨791603, by decide⟩
    (prefixPartial 13 422047) = some ⟨13, 2, 0, 791603, 422047, 901, 16384⟩ := by
  decide +kernel

theorem context_13_422047_791603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422047 ⟨791603, by decide⟩ :=
  accepted_of_selected 13 422047 ⟨791603, by decide⟩ ⟨13, 2, 0, 791603, 422047, 901, 16384⟩
    (by decide) selected_cut_31084

theorem unmarked_context_12_105511_791604 : frontier 9 ⟨791604, by decide⟩
    (prefixCache 12 105511) (prefixPartial 12 105511) = false := by
  decide +kernel

theorem node_context_12_105511_791604 : EJMOriginalGlobalDAGData.nodes 9 ⟨791604, by decide⟩ =
    .split (coordinate 12) (![⟨791517, by decide⟩,⟨791559, by decide⟩,⟨791594, by decide⟩,⟨791603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105511_791604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105511 ⟨791604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105511
    ⟨791604, by decide⟩ (by decide) (![⟨791517, by decide⟩,⟨791559, by decide⟩,⟨791594, by decide⟩,⟨791603, by decide⟩]) unmarked_context_12_105511_791604 node_context_12_105511_791604
  intro a
  fin_cases a
  · exact context_13_422044_791517
  · exact context_13_422045_791559
  · exact context_13_422046_791594
  · exact context_13_422047_791603

theorem unmarked_context_11_26377_791605 : frontier 10 ⟨791605, by decide⟩
    (prefixCache 11 26377) (prefixPartial 11 26377) = false := by
  decide +kernel

theorem node_context_11_26377_791605 : EJMOriginalGlobalDAGData.nodes 10 ⟨791605, by decide⟩ =
    .split (coordinate 11) (![⟨791281, by decide⟩,⟨791379, by decide⟩,⟨791493, by decide⟩,⟨791604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26377_791605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26377 ⟨791605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26377
    ⟨791605, by decide⟩ (by decide) (![⟨791281, by decide⟩,⟨791379, by decide⟩,⟨791493, by decide⟩,⟨791604, by decide⟩]) unmarked_context_11_26377_791605 node_context_11_26377_791605
  intro a
  fin_cases a
  · exact context_12_105508_791281
  · exact context_12_105509_791379
  · exact context_12_105510_791493
  · exact context_12_105511_791604

theorem selected_cut_31085 : selected 8 ⟨791627, by decide⟩
    (prefixPartial 13 422048) = some ⟨13, 2, 0, 791627, 422048, 857, 16384⟩ := by
  decide +kernel

theorem context_13_422048_791627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422048 ⟨791627, by decide⟩ :=
  accepted_of_selected 13 422048 ⟨791627, by decide⟩ ⟨13, 2, 0, 791627, 422048, 857, 16384⟩
    (by decide) selected_cut_31085

theorem selected_cut_31086 : selected 8 ⟨791653, by decide⟩
    (prefixPartial 13 422049) = some ⟨13, 2, 0, 791653, 422049, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_422049_791653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422049 ⟨791653, by decide⟩ :=
  accepted_of_selected 13 422049 ⟨791653, by decide⟩ ⟨13, 2, 0, 791653, 422049, 2093, 16384⟩
    (by decide) selected_cut_31086

theorem selected_cut_31087 : selected 8 ⟨791671, by decide⟩
    (prefixPartial 13 422050) = some ⟨13, 2, 0, 791671, 422050, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_422050_791671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422050 ⟨791671, by decide⟩ :=
  accepted_of_selected 13 422050 ⟨791671, by decide⟩ ⟨13, 2, 0, 791671, 422050, 1493, 16384⟩
    (by decide) selected_cut_31087

theorem selected_cut_31088 : selected 8 ⟨791681, by decide⟩
    (prefixPartial 13 422051) = some ⟨13, 2, 0, 791681, 422051, 765, 16384⟩ := by
  decide +kernel

theorem context_13_422051_791681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422051 ⟨791681, by decide⟩ :=
  accepted_of_selected 13 422051 ⟨791681, by decide⟩ ⟨13, 2, 0, 791681, 422051, 765, 16384⟩
    (by decide) selected_cut_31088

theorem unmarked_context_12_105512_791682 : frontier 9 ⟨791682, by decide⟩
    (prefixCache 12 105512) (prefixPartial 12 105512) = false := by
  decide +kernel

theorem node_context_12_105512_791682 : EJMOriginalGlobalDAGData.nodes 9 ⟨791682, by decide⟩ =
    .split (coordinate 12) (![⟨791627, by decide⟩,⟨791653, by decide⟩,⟨791671, by decide⟩,⟨791681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105512_791682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105512 ⟨791682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105512
    ⟨791682, by decide⟩ (by decide) (![⟨791627, by decide⟩,⟨791653, by decide⟩,⟨791671, by decide⟩,⟨791681, by decide⟩]) unmarked_context_12_105512_791682 node_context_12_105512_791682
  intro a
  fin_cases a
  · exact context_13_422048_791627
  · exact context_13_422049_791653
  · exact context_13_422050_791671
  · exact context_13_422051_791681

theorem selected_cut_31089 : selected 8 ⟨791703, by decide⟩
    (prefixPartial 13 422052) = some ⟨13, 2, 0, 791703, 422052, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_422052_791703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422052 ⟨791703, by decide⟩ :=
  accepted_of_selected 13 422052 ⟨791703, by decide⟩ ⟨13, 2, 0, 791703, 422052, 1021, 16384⟩
    (by decide) selected_cut_31089

theorem selected_cut_31090 : selected 8 ⟨791746, by decide⟩
    (prefixPartial 13 422053) = some ⟨13, 2, 0, 791746, 422053, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_422053_791746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422053 ⟨791746, by decide⟩ :=
  accepted_of_selected 13 422053 ⟨791746, by decide⟩ ⟨13, 2, 0, 791746, 422053, 2365, 16384⟩
    (by decide) selected_cut_31090

theorem selected_cut_31091 : selected 8 ⟨791769, by decide⟩
    (prefixPartial 13 422054) = some ⟨13, 2, 0, 791769, 422054, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_422054_791769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422054 ⟨791769, by decide⟩ :=
  accepted_of_selected 13 422054 ⟨791769, by decide⟩ ⟨13, 2, 0, 791769, 422054, 1513, 16384⟩
    (by decide) selected_cut_31091

theorem selected_cut_31092 : selected 8 ⟨791777, by decide⟩
    (prefixPartial 13 422055) = some ⟨13, 2, 0, 791777, 422055, 757, 16384⟩ := by
  decide +kernel

theorem context_13_422055_791777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422055 ⟨791777, by decide⟩ :=
  accepted_of_selected 13 422055 ⟨791777, by decide⟩ ⟨13, 2, 0, 791777, 422055, 757, 16384⟩
    (by decide) selected_cut_31092

theorem unmarked_context_12_105513_791778 : frontier 9 ⟨791778, by decide⟩
    (prefixCache 12 105513) (prefixPartial 12 105513) = false := by
  decide +kernel

theorem node_context_12_105513_791778 : EJMOriginalGlobalDAGData.nodes 9 ⟨791778, by decide⟩ =
    .split (coordinate 12) (![⟨791703, by decide⟩,⟨791746, by decide⟩,⟨791769, by decide⟩,⟨791777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105513_791778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105513 ⟨791778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105513
    ⟨791778, by decide⟩ (by decide) (![⟨791703, by decide⟩,⟨791746, by decide⟩,⟨791769, by decide⟩,⟨791777, by decide⟩]) unmarked_context_12_105513_791778 node_context_12_105513_791778
  intro a
  fin_cases a
  · exact context_13_422052_791703
  · exact context_13_422053_791746
  · exact context_13_422054_791769
  · exact context_13_422055_791777

theorem selected_cut_31093 : selected 8 ⟨791798, by decide⟩
    (prefixPartial 13 422056) = some ⟨13, 2, 0, 791798, 422056, 813, 16384⟩ := by
  decide +kernel

theorem context_13_422056_791798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422056 ⟨791798, by decide⟩ :=
  accepted_of_selected 13 422056 ⟨791798, by decide⟩ ⟨13, 2, 0, 791798, 422056, 813, 16384⟩
    (by decide) selected_cut_31093

theorem selected_cut_31094 : selected 8 ⟨791842, by decide⟩
    (prefixPartial 13 422057) = some ⟨13, 2, 0, 791842, 422057, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_422057_791842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422057 ⟨791842, by decide⟩ :=
  accepted_of_selected 13 422057 ⟨791842, by decide⟩ ⟨13, 2, 0, 791842, 422057, 2429, 16384⟩
    (by decide) selected_cut_31094

theorem selected_cut_31095 : selected 8 ⟨791862, by decide⟩
    (prefixPartial 13 422058) = some ⟨13, 2, 0, 791862, 422058, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_422058_791862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422058 ⟨791862, by decide⟩ :=
  accepted_of_selected 13 422058 ⟨791862, by decide⟩ ⟨13, 2, 0, 791862, 422058, 1097, 16384⟩
    (by decide) selected_cut_31095

theorem selected_cut_31096 : selected 8 ⟨791871, by decide⟩
    (prefixPartial 13 422059) = some ⟨13, 2, 0, 791871, 422059, 777, 16384⟩ := by
  decide +kernel

theorem context_13_422059_791871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422059 ⟨791871, by decide⟩ :=
  accepted_of_selected 13 422059 ⟨791871, by decide⟩ ⟨13, 2, 0, 791871, 422059, 777, 16384⟩
    (by decide) selected_cut_31096

theorem unmarked_context_12_105514_791872 : frontier 9 ⟨791872, by decide⟩
    (prefixCache 12 105514) (prefixPartial 12 105514) = false := by
  decide +kernel

theorem node_context_12_105514_791872 : EJMOriginalGlobalDAGData.nodes 9 ⟨791872, by decide⟩ =
    .split (coordinate 12) (![⟨791798, by decide⟩,⟨791842, by decide⟩,⟨791862, by decide⟩,⟨791871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105514_791872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105514 ⟨791872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105514
    ⟨791872, by decide⟩ (by decide) (![⟨791798, by decide⟩,⟨791842, by decide⟩,⟨791862, by decide⟩,⟨791871, by decide⟩]) unmarked_context_12_105514_791872 node_context_12_105514_791872
  intro a
  fin_cases a
  · exact context_13_422056_791798
  · exact context_13_422057_791842
  · exact context_13_422058_791862
  · exact context_13_422059_791871

theorem selected_cut_31097 : selected 8 ⟨791887, by decide⟩
    (prefixPartial 13 422060) = some ⟨13, 2, 0, 791887, 422060, 889, 16384⟩ := by
  decide +kernel

theorem context_13_422060_791887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422060 ⟨791887, by decide⟩ :=
  accepted_of_selected 13 422060 ⟨791887, by decide⟩ ⟨13, 2, 0, 791887, 422060, 889, 16384⟩
    (by decide) selected_cut_31097

theorem selected_cut_31098 : selected 8 ⟨791922, by decide⟩
    (prefixPartial 13 422061) = some ⟨13, 2, 0, 791922, 422061, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_422061_791922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422061 ⟨791922, by decide⟩ :=
  accepted_of_selected 13 422061 ⟨791922, by decide⟩ ⟨13, 2, 0, 791922, 422061, 2333, 16384⟩
    (by decide) selected_cut_31098

theorem selected_cut_31099 : selected 8 ⟨791952, by decide⟩
    (prefixPartial 13 422062) = some ⟨13, 2, 0, 791952, 422062, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_422062_791952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422062 ⟨791952, by decide⟩ :=
  accepted_of_selected 13 422062 ⟨791952, by decide⟩ ⟨13, 2, 0, 791952, 422062, 1561, 16384⟩
    (by decide) selected_cut_31099

theorem selected_cut_31100 : selected 8 ⟨791960, by decide⟩
    (prefixPartial 13 422063) = some ⟨13, 2, 0, 791960, 422063, 817, 16384⟩ := by
  decide +kernel

theorem context_13_422063_791960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422063 ⟨791960, by decide⟩ :=
  accepted_of_selected 13 422063 ⟨791960, by decide⟩ ⟨13, 2, 0, 791960, 422063, 817, 16384⟩
    (by decide) selected_cut_31100

theorem unmarked_context_12_105515_791961 : frontier 9 ⟨791961, by decide⟩
    (prefixCache 12 105515) (prefixPartial 12 105515) = false := by
  decide +kernel

theorem node_context_12_105515_791961 : EJMOriginalGlobalDAGData.nodes 9 ⟨791961, by decide⟩ =
    .split (coordinate 12) (![⟨791887, by decide⟩,⟨791922, by decide⟩,⟨791952, by decide⟩,⟨791960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105515_791961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105515 ⟨791961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105515
    ⟨791961, by decide⟩ (by decide) (![⟨791887, by decide⟩,⟨791922, by decide⟩,⟨791952, by decide⟩,⟨791960, by decide⟩]) unmarked_context_12_105515_791961 node_context_12_105515_791961
  intro a
  fin_cases a
  · exact context_13_422060_791887
  · exact context_13_422061_791922
  · exact context_13_422062_791952
  · exact context_13_422063_791960

theorem unmarked_context_11_26378_791962 : frontier 10 ⟨791962, by decide⟩
    (prefixCache 11 26378) (prefixPartial 11 26378) = false := by
  decide +kernel

theorem node_context_11_26378_791962 : EJMOriginalGlobalDAGData.nodes 10 ⟨791962, by decide⟩ =
    .split (coordinate 11) (![⟨791682, by decide⟩,⟨791778, by decide⟩,⟨791872, by decide⟩,⟨791961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26378_791962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26378 ⟨791962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26378
    ⟨791962, by decide⟩ (by decide) (![⟨791682, by decide⟩,⟨791778, by decide⟩,⟨791872, by decide⟩,⟨791961, by decide⟩]) unmarked_context_11_26378_791962 node_context_11_26378_791962
  intro a
  fin_cases a
  · exact context_12_105512_791682
  · exact context_12_105513_791778
  · exact context_12_105514_791872
  · exact context_12_105515_791961

theorem selected_cut_31101 : selected 8 ⟨791979, by decide⟩
    (prefixPartial 13 422064) = some ⟨13, 2, 0, 791979, 422064, 521, 16384⟩ := by
  decide +kernel

theorem context_13_422064_791979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422064 ⟨791979, by decide⟩ :=
  accepted_of_selected 13 422064 ⟨791979, by decide⟩ ⟨13, 2, 0, 791979, 422064, 521, 16384⟩
    (by decide) selected_cut_31101

theorem selected_cut_31102 : selected 8 ⟨792005, by decide⟩
    (prefixPartial 13 422065) = some ⟨13, 2, 0, 792005, 422065, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_422065_792005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422065 ⟨792005, by decide⟩ :=
  accepted_of_selected 13 422065 ⟨792005, by decide⟩ ⟨13, 2, 0, 792005, 422065, 1997, 16384⟩
    (by decide) selected_cut_31102

theorem selected_cut_31103 : selected 8 ⟨792025, by decide⟩
    (prefixPartial 13 422066) = some ⟨13, 2, 0, 792025, 422066, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_422066_792025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422066 ⟨792025, by decide⟩ :=
  accepted_of_selected 13 422066 ⟨792025, by decide⟩ ⟨13, 2, 0, 792025, 422066, 1317, 16384⟩
    (by decide) selected_cut_31103

theorem selected_cut_31104 : selected 8 ⟨792032, by decide⟩
    (prefixPartial 13 422067) = some ⟨13, 2, 0, 792032, 422067, 725, 16384⟩ := by
  decide +kernel

theorem context_13_422067_792032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422067 ⟨792032, by decide⟩ :=
  accepted_of_selected 13 422067 ⟨792032, by decide⟩ ⟨13, 2, 0, 792032, 422067, 725, 16384⟩
    (by decide) selected_cut_31104

theorem unmarked_context_12_105516_792033 : frontier 9 ⟨792033, by decide⟩
    (prefixCache 12 105516) (prefixPartial 12 105516) = false := by
  decide +kernel

theorem node_context_12_105516_792033 : EJMOriginalGlobalDAGData.nodes 9 ⟨792033, by decide⟩ =
    .split (coordinate 12) (![⟨791979, by decide⟩,⟨792005, by decide⟩,⟨792025, by decide⟩,⟨792032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105516_792033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105516 ⟨792033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105516
    ⟨792033, by decide⟩ (by decide) (![⟨791979, by decide⟩,⟨792005, by decide⟩,⟨792025, by decide⟩,⟨792032, by decide⟩]) unmarked_context_12_105516_792033 node_context_12_105516_792033
  intro a
  fin_cases a
  · exact context_13_422064_791979
  · exact context_13_422065_792005
  · exact context_13_422066_792025
  · exact context_13_422067_792032

theorem selected_cut_31105 : selected 8 ⟨792049, by decide⟩
    (prefixPartial 13 422068) = some ⟨13, 2, 0, 792049, 422068, 741, 16384⟩ := by
  decide +kernel

theorem context_13_422068_792049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422068 ⟨792049, by decide⟩ :=
  accepted_of_selected 13 422068 ⟨792049, by decide⟩ ⟨13, 2, 0, 792049, 422068, 741, 16384⟩
    (by decide) selected_cut_31105

theorem selected_cut_31106 : selected 8 ⟨792085, by decide⟩
    (prefixPartial 13 422069) = some ⟨13, 2, 0, 792085, 422069, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_422069_792085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422069 ⟨792085, by decide⟩ :=
  accepted_of_selected 13 422069 ⟨792085, by decide⟩ ⟨13, 2, 0, 792085, 422069, 2249, 16384⟩
    (by decide) selected_cut_31106

theorem selected_cut_31107 : selected 8 ⟨792106, by decide⟩
    (prefixPartial 13 422070) = some ⟨13, 2, 0, 792106, 422070, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_422070_792106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422070 ⟨792106, by decide⟩ :=
  accepted_of_selected 13 422070 ⟨792106, by decide⟩ ⟨13, 2, 0, 792106, 422070, 1441, 16384⟩
    (by decide) selected_cut_31107

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
