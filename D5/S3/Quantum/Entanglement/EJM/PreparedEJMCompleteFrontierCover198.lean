/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover197
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19011 : selected 8 ⟨487459, by decide⟩
    (prefixPartial 13 287961) = some ⟨13, 2, 0, 487459, 287961, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_287961_487459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287961 ⟨487459, by decide⟩ :=
  accepted_of_selected 13 287961 ⟨487459, by decide⟩ ⟨13, 2, 0, 487459, 287961, 2949, 16384⟩
    (by decide) selected_cut_19011

theorem selected_cut_19012 : selected 8 ⟨487485, by decide⟩
    (prefixPartial 13 287962) = some ⟨13, 2, 0, 487485, 287962, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_287962_487485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287962 ⟨487485, by decide⟩ :=
  accepted_of_selected 13 287962 ⟨487485, by decide⟩ ⟨13, 2, 0, 487485, 287962, 2149, 16384⟩
    (by decide) selected_cut_19012

theorem selected_cut_19013 : selected 8 ⟨487495, by decide⟩
    (prefixPartial 13 287963) = some ⟨13, 2, 0, 487495, 287963, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_287963_487495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287963 ⟨487495, by decide⟩ :=
  accepted_of_selected 13 287963 ⟨487495, by decide⟩ ⟨13, 2, 0, 487495, 287963, 1201, 16384⟩
    (by decide) selected_cut_19013

theorem unmarked_context_12_71990_487496 : frontier 9 ⟨487496, by decide⟩
    (prefixCache 12 71990) (prefixPartial 12 71990) = false := by
  decide +kernel

theorem node_context_12_71990_487496 : EJMOriginalGlobalDAGData.nodes 9 ⟨487496, by decide⟩ =
    .split (coordinate 12) (![⟨487426, by decide⟩,⟨487459, by decide⟩,⟨487485, by decide⟩,⟨487495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71990_487496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71990 ⟨487496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71990
    ⟨487496, by decide⟩ (by decide) (![⟨487426, by decide⟩,⟨487459, by decide⟩,⟨487485, by decide⟩,⟨487495, by decide⟩]) unmarked_context_12_71990_487496 node_context_12_71990_487496
  intro a
  fin_cases a
  · exact context_13_287960_487426
  · exact context_13_287961_487459
  · exact context_13_287962_487485
  · exact context_13_287963_487495

theorem selected_cut_19014 : selected 8 ⟨487510, by decide⟩
    (prefixPartial 13 287964) = some ⟨13, 2, 0, 487510, 287964, 761, 16384⟩ := by
  decide +kernel

theorem context_13_287964_487510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287964 ⟨487510, by decide⟩ :=
  accepted_of_selected 13 287964 ⟨487510, by decide⟩ ⟨13, 2, 0, 487510, 287964, 761, 16384⟩
    (by decide) selected_cut_19014

theorem selected_cut_19015 : selected 8 ⟨487552, by decide⟩
    (prefixPartial 13 287965) = some ⟨13, 2, 0, 487552, 287965, 3093, 16384⟩ := by
  decide +kernel

theorem context_13_287965_487552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287965 ⟨487552, by decide⟩ :=
  accepted_of_selected 13 287965 ⟨487552, by decide⟩ ⟨13, 2, 0, 487552, 287965, 3093, 16384⟩
    (by decide) selected_cut_19015

theorem selected_cut_19016 : selected 8 ⟨487586, by decide⟩
    (prefixPartial 13 287966) = some ⟨13, 2, 0, 487586, 287966, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_287966_487586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287966 ⟨487586, by decide⟩ :=
  accepted_of_selected 13 287966 ⟨487586, by decide⟩ ⟨13, 2, 0, 487586, 287966, 2201, 16384⟩
    (by decide) selected_cut_19016

theorem selected_cut_19017 : selected 8 ⟨487595, by decide⟩
    (prefixPartial 13 287967) = some ⟨13, 2, 0, 487595, 287967, 885, 16384⟩ := by
  decide +kernel

theorem context_13_287967_487595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287967 ⟨487595, by decide⟩ :=
  accepted_of_selected 13 287967 ⟨487595, by decide⟩ ⟨13, 2, 0, 487595, 287967, 885, 16384⟩
    (by decide) selected_cut_19017

theorem unmarked_context_12_71991_487596 : frontier 9 ⟨487596, by decide⟩
    (prefixCache 12 71991) (prefixPartial 12 71991) = false := by
  decide +kernel

theorem node_context_12_71991_487596 : EJMOriginalGlobalDAGData.nodes 9 ⟨487596, by decide⟩ =
    .split (coordinate 12) (![⟨487510, by decide⟩,⟨487552, by decide⟩,⟨487586, by decide⟩,⟨487595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71991_487596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71991 ⟨487596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71991
    ⟨487596, by decide⟩ (by decide) (![⟨487510, by decide⟩,⟨487552, by decide⟩,⟨487586, by decide⟩,⟨487595, by decide⟩]) unmarked_context_12_71991_487596 node_context_12_71991_487596
  intro a
  fin_cases a
  · exact context_13_287964_487510
  · exact context_13_287965_487552
  · exact context_13_287966_487586
  · exact context_13_287967_487595

theorem unmarked_context_11_17997_487597 : frontier 10 ⟨487597, by decide⟩
    (prefixCache 11 17997) (prefixPartial 11 17997) = false := by
  decide +kernel

theorem node_context_11_17997_487597 : EJMOriginalGlobalDAGData.nodes 10 ⟨487597, by decide⟩ =
    .split (coordinate 11) (![⟨487229, by decide⟩,⟨487415, by decide⟩,⟨487496, by decide⟩,⟨487596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17997_487597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17997 ⟨487597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17997
    ⟨487597, by decide⟩ (by decide) (![⟨487229, by decide⟩,⟨487415, by decide⟩,⟨487496, by decide⟩,⟨487596, by decide⟩]) unmarked_context_11_17997_487597 node_context_11_17997_487597
  intro a
  fin_cases a
  · exact context_12_71988_487229
  · exact context_12_71989_487415
  · exact context_12_71990_487496
  · exact context_12_71991_487596

theorem selected_cut_19018 : selected 8 ⟨487611, by decide⟩
    (prefixPartial 13 287968) = some ⟨13, 2, 0, 487611, 287968, 861, 16384⟩ := by
  decide +kernel

theorem context_13_287968_487611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287968 ⟨487611, by decide⟩ :=
  accepted_of_selected 13 287968 ⟨487611, by decide⟩ ⟨13, 2, 0, 487611, 287968, 861, 16384⟩
    (by decide) selected_cut_19018

theorem selected_cut_19019 : selected 8 ⟨487663, by decide⟩
    (prefixPartial 13 287969) = some ⟨13, 2, 0, 487663, 287969, 3685, 16384⟩ := by
  decide +kernel

theorem context_13_287969_487663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287969 ⟨487663, by decide⟩ :=
  accepted_of_selected 13 287969 ⟨487663, by decide⟩ ⟨13, 2, 0, 487663, 287969, 3685, 16384⟩
    (by decide) selected_cut_19019

theorem selected_cut_19020 : selected 8 ⟨487720, by decide⟩
    (prefixPartial 13 287970) = some ⟨13, 2, 0, 487720, 287970, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_287970_487720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287970 ⟨487720, by decide⟩ :=
  accepted_of_selected 13 287970 ⟨487720, by decide⟩ ⟨13, 2, 0, 487720, 287970, 2865, 16384⟩
    (by decide) selected_cut_19020

theorem selected_cut_19021 : selected 8 ⟨487754, by decide⟩
    (prefixPartial 13 287971) = some ⟨13, 2, 0, 487754, 287971, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_287971_487754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287971 ⟨487754, by decide⟩ :=
  accepted_of_selected 13 287971 ⟨487754, by decide⟩ ⟨13, 2, 0, 487754, 287971, 1433, 16384⟩
    (by decide) selected_cut_19021

theorem unmarked_context_12_71992_487755 : frontier 9 ⟨487755, by decide⟩
    (prefixCache 12 71992) (prefixPartial 12 71992) = false := by
  decide +kernel

theorem node_context_12_71992_487755 : EJMOriginalGlobalDAGData.nodes 9 ⟨487755, by decide⟩ =
    .split (coordinate 12) (![⟨487611, by decide⟩,⟨487663, by decide⟩,⟨487720, by decide⟩,⟨487754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71992_487755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71992 ⟨487755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71992
    ⟨487755, by decide⟩ (by decide) (![⟨487611, by decide⟩,⟨487663, by decide⟩,⟨487720, by decide⟩,⟨487754, by decide⟩]) unmarked_context_12_71992_487755 node_context_12_71992_487755
  intro a
  fin_cases a
  · exact context_13_287968_487611
  · exact context_13_287969_487663
  · exact context_13_287970_487720
  · exact context_13_287971_487754

theorem selected_cut_19022 : selected 8 ⟨487764, by decide⟩
    (prefixPartial 13 287972) = some ⟨13, 2, 0, 487764, 287972, 449, 16384⟩ := by
  decide +kernel

theorem context_13_287972_487764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287972 ⟨487764, by decide⟩ :=
  accepted_of_selected 13 287972 ⟨487764, by decide⟩ ⟨13, 2, 0, 487764, 287972, 449, 16384⟩
    (by decide) selected_cut_19022

theorem selected_cut_19023 : selected 8 ⟨487794, by decide⟩
    (prefixPartial 13 287973) = some ⟨13, 2, 0, 487794, 287973, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_287973_487794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287973 ⟨487794, by decide⟩ :=
  accepted_of_selected 13 287973 ⟨487794, by decide⟩ ⟨13, 2, 0, 487794, 287973, 2381, 16384⟩
    (by decide) selected_cut_19023

theorem selected_cut_19024 : selected 8 ⟨487812, by decide⟩
    (prefixPartial 13 287974) = some ⟨13, 2, 0, 487812, 287974, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_287974_487812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287974 ⟨487812, by decide⟩ :=
  accepted_of_selected 13 287974 ⟨487812, by decide⟩ ⟨13, 2, 0, 487812, 287974, 2009, 16384⟩
    (by decide) selected_cut_19024

theorem selected_cut_19025 : selected 8 ⟨487821, by decide⟩
    (prefixPartial 13 287975) = some ⟨13, 2, 0, 487821, 287975, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_287975_487821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287975 ⟨487821, by decide⟩ :=
  accepted_of_selected 13 287975 ⟨487821, by decide⟩ ⟨13, 2, 0, 487821, 287975, 1141, 16384⟩
    (by decide) selected_cut_19025

theorem unmarked_context_12_71993_487822 : frontier 9 ⟨487822, by decide⟩
    (prefixCache 12 71993) (prefixPartial 12 71993) = false := by
  decide +kernel

theorem node_context_12_71993_487822 : EJMOriginalGlobalDAGData.nodes 9 ⟨487822, by decide⟩ =
    .split (coordinate 12) (![⟨487764, by decide⟩,⟨487794, by decide⟩,⟨487812, by decide⟩,⟨487821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71993_487822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71993 ⟨487822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71993
    ⟨487822, by decide⟩ (by decide) (![⟨487764, by decide⟩,⟨487794, by decide⟩,⟨487812, by decide⟩,⟨487821, by decide⟩]) unmarked_context_12_71993_487822 node_context_12_71993_487822
  intro a
  fin_cases a
  · exact context_13_287972_487764
  · exact context_13_287973_487794
  · exact context_13_287974_487812
  · exact context_13_287975_487821

theorem selected_cut_19026 : selected 8 ⟨487831, by decide⟩
    (prefixPartial 13 287976) = some ⟨13, 2, 0, 487831, 287976, 493, 16384⟩ := by
  decide +kernel

theorem context_13_287976_487831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287976 ⟨487831, by decide⟩ :=
  accepted_of_selected 13 287976 ⟨487831, by decide⟩ ⟨13, 2, 0, 487831, 287976, 493, 16384⟩
    (by decide) selected_cut_19026

theorem selected_cut_19027 : selected 8 ⟨487862, by decide⟩
    (prefixPartial 13 287977) = some ⟨13, 2, 0, 487862, 287977, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_287977_487862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287977 ⟨487862, by decide⟩ :=
  accepted_of_selected 13 287977 ⟨487862, by decide⟩ ⟨13, 2, 0, 487862, 287977, 2785, 16384⟩
    (by decide) selected_cut_19027

theorem selected_cut_19028 : selected 8 ⟨487897, by decide⟩
    (prefixPartial 13 287978) = some ⟨13, 2, 0, 487897, 287978, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_287978_487897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287978 ⟨487897, by decide⟩ :=
  accepted_of_selected 13 287978 ⟨487897, by decide⟩ ⟨13, 2, 0, 487897, 287978, 2333, 16384⟩
    (by decide) selected_cut_19028

theorem selected_cut_19029 : selected 8 ⟨487907, by decide⟩
    (prefixPartial 13 287979) = some ⟨13, 2, 0, 487907, 287979, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_287979_487907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287979 ⟨487907, by decide⟩ :=
  accepted_of_selected 13 287979 ⟨487907, by decide⟩ ⟨13, 2, 0, 487907, 287979, 1205, 16384⟩
    (by decide) selected_cut_19029

theorem unmarked_context_12_71994_487908 : frontier 9 ⟨487908, by decide⟩
    (prefixCache 12 71994) (prefixPartial 12 71994) = false := by
  decide +kernel

theorem node_context_12_71994_487908 : EJMOriginalGlobalDAGData.nodes 9 ⟨487908, by decide⟩ =
    .split (coordinate 12) (![⟨487831, by decide⟩,⟨487862, by decide⟩,⟨487897, by decide⟩,⟨487907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71994_487908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71994 ⟨487908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71994
    ⟨487908, by decide⟩ (by decide) (![⟨487831, by decide⟩,⟨487862, by decide⟩,⟨487897, by decide⟩,⟨487907, by decide⟩]) unmarked_context_12_71994_487908 node_context_12_71994_487908
  intro a
  fin_cases a
  · exact context_13_287976_487831
  · exact context_13_287977_487862
  · exact context_13_287978_487897
  · exact context_13_287979_487907

theorem selected_cut_19030 : selected 8 ⟨487917, by decide⟩
    (prefixPartial 13 287980) = some ⟨13, 2, 0, 487917, 287980, 421, 16384⟩ := by
  decide +kernel

theorem context_13_287980_487917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287980 ⟨487917, by decide⟩ :=
  accepted_of_selected 13 287980 ⟨487917, by decide⟩ ⟨13, 2, 0, 487917, 287980, 421, 16384⟩
    (by decide) selected_cut_19030

theorem selected_cut_19031 : selected 8 ⟨487954, by decide⟩
    (prefixPartial 13 287981) = some ⟨13, 2, 0, 487954, 287981, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_287981_487954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287981 ⟨487954, by decide⟩ :=
  accepted_of_selected 13 287981 ⟨487954, by decide⟩ ⟨13, 2, 0, 487954, 287981, 3041, 16384⟩
    (by decide) selected_cut_19031

theorem selected_cut_19032 : selected 8 ⟨487991, by decide⟩
    (prefixPartial 13 287982) = some ⟨13, 2, 0, 487991, 287982, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_287982_487991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287982 ⟨487991, by decide⟩ :=
  accepted_of_selected 13 287982 ⟨487991, by decide⟩ ⟨13, 2, 0, 487991, 287982, 2309, 16384⟩
    (by decide) selected_cut_19032

theorem selected_cut_19033 : selected 8 ⟨487999, by decide⟩
    (prefixPartial 13 287983) = some ⟨13, 2, 0, 487999, 287983, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_287983_487999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287983 ⟨487999, by decide⟩ :=
  accepted_of_selected 13 287983 ⟨487999, by decide⟩ ⟨13, 2, 0, 487999, 287983, 1049, 16384⟩
    (by decide) selected_cut_19033

theorem unmarked_context_12_71995_488000 : frontier 9 ⟨488000, by decide⟩
    (prefixCache 12 71995) (prefixPartial 12 71995) = false := by
  decide +kernel

theorem node_context_12_71995_488000 : EJMOriginalGlobalDAGData.nodes 9 ⟨488000, by decide⟩ =
    .split (coordinate 12) (![⟨487917, by decide⟩,⟨487954, by decide⟩,⟨487991, by decide⟩,⟨487999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71995_488000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71995 ⟨488000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71995
    ⟨488000, by decide⟩ (by decide) (![⟨487917, by decide⟩,⟨487954, by decide⟩,⟨487991, by decide⟩,⟨487999, by decide⟩]) unmarked_context_12_71995_488000 node_context_12_71995_488000
  intro a
  fin_cases a
  · exact context_13_287980_487917
  · exact context_13_287981_487954
  · exact context_13_287982_487991
  · exact context_13_287983_487999

theorem unmarked_context_11_17998_488001 : frontier 10 ⟨488001, by decide⟩
    (prefixCache 11 17998) (prefixPartial 11 17998) = false := by
  decide +kernel

theorem node_context_11_17998_488001 : EJMOriginalGlobalDAGData.nodes 10 ⟨488001, by decide⟩ =
    .split (coordinate 11) (![⟨487755, by decide⟩,⟨487822, by decide⟩,⟨487908, by decide⟩,⟨488000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17998_488001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17998 ⟨488001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17998
    ⟨488001, by decide⟩ (by decide) (![⟨487755, by decide⟩,⟨487822, by decide⟩,⟨487908, by decide⟩,⟨488000, by decide⟩]) unmarked_context_11_17998_488001 node_context_11_17998_488001
  intro a
  fin_cases a
  · exact context_12_71992_487755
  · exact context_12_71993_487822
  · exact context_12_71994_487908
  · exact context_12_71995_488000

theorem selected_cut_19034 : selected 8 ⟨488008, by decide⟩
    (prefixPartial 13 287984) = some ⟨13, 2, 0, 488008, 287984, 369, 16384⟩ := by
  decide +kernel

theorem context_13_287984_488008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287984 ⟨488008, by decide⟩ :=
  accepted_of_selected 13 287984 ⟨488008, by decide⟩ ⟨13, 2, 0, 488008, 287984, 369, 16384⟩
    (by decide) selected_cut_19034

theorem selected_cut_19035 : selected 8 ⟨488062, by decide⟩
    (prefixPartial 13 287985) = some ⟨13, 2, 0, 488062, 287985, 3873, 16384⟩ := by
  decide +kernel

theorem context_13_287985_488062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287985 ⟨488062, by decide⟩ :=
  accepted_of_selected 13 287985 ⟨488062, by decide⟩ ⟨13, 2, 0, 488062, 287985, 3873, 16384⟩
    (by decide) selected_cut_19035

theorem selected_cut_19036 : selected 8 ⟨488121, by decide⟩
    (prefixPartial 13 287986) = some ⟨13, 2, 0, 488121, 287986, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_287986_488121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287986 ⟨488121, by decide⟩ :=
  accepted_of_selected 13 287986 ⟨488121, by decide⟩ ⟨13, 2, 0, 488121, 287986, 3109, 16384⟩
    (by decide) selected_cut_19036

theorem selected_cut_19037 : selected 8 ⟨488148, by decide⟩
    (prefixPartial 13 287987) = some ⟨13, 2, 0, 488148, 287987, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_287987_488148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287987 ⟨488148, by decide⟩ :=
  accepted_of_selected 13 287987 ⟨488148, by decide⟩ ⟨13, 2, 0, 488148, 287987, 1405, 16384⟩
    (by decide) selected_cut_19037

theorem unmarked_context_12_71996_488149 : frontier 9 ⟨488149, by decide⟩
    (prefixCache 12 71996) (prefixPartial 12 71996) = false := by
  decide +kernel

theorem node_context_12_71996_488149 : EJMOriginalGlobalDAGData.nodes 9 ⟨488149, by decide⟩ =
    .split (coordinate 12) (![⟨488008, by decide⟩,⟨488062, by decide⟩,⟨488121, by decide⟩,⟨488148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71996_488149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71996 ⟨488149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71996
    ⟨488149, by decide⟩ (by decide) (![⟨488008, by decide⟩,⟨488062, by decide⟩,⟨488121, by decide⟩,⟨488148, by decide⟩]) unmarked_context_12_71996_488149 node_context_12_71996_488149
  intro a
  fin_cases a
  · exact context_13_287984_488008
  · exact context_13_287985_488062
  · exact context_13_287986_488121
  · exact context_13_287987_488148

theorem selected_cut_19038 : selected 8 ⟨488153, by decide⟩
    (prefixPartial 13 287988) = some ⟨13, 2, 0, 488153, 287988, 149, 16384⟩ := by
  decide +kernel

theorem context_13_287988_488153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287988 ⟨488153, by decide⟩ :=
  accepted_of_selected 13 287988 ⟨488153, by decide⟩ ⟨13, 2, 0, 488153, 287988, 149, 16384⟩
    (by decide) selected_cut_19038

theorem selected_cut_19039 : selected 8 ⟨488182, by decide⟩
    (prefixPartial 13 287989) = some ⟨13, 2, 0, 488182, 287989, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_287989_488182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287989 ⟨488182, by decide⟩ :=
  accepted_of_selected 13 287989 ⟨488182, by decide⟩ ⟨13, 2, 0, 488182, 287989, 2469, 16384⟩
    (by decide) selected_cut_19039

theorem selected_cut_19040 : selected 8 ⟨488205, by decide⟩
    (prefixPartial 13 287990) = some ⟨13, 2, 0, 488205, 287990, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_287990_488205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287990 ⟨488205, by decide⟩ :=
  accepted_of_selected 13 287990 ⟨488205, by decide⟩ ⟨13, 2, 0, 488205, 287990, 2065, 16384⟩
    (by decide) selected_cut_19040

theorem selected_cut_19041 : selected 8 ⟨488214, by decide⟩
    (prefixPartial 13 287991) = some ⟨13, 2, 0, 488214, 287991, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_287991_488214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287991 ⟨488214, by decide⟩ :=
  accepted_of_selected 13 287991 ⟨488214, by decide⟩ ⟨13, 2, 0, 488214, 287991, 1113, 16384⟩
    (by decide) selected_cut_19041

theorem unmarked_context_12_71997_488215 : frontier 9 ⟨488215, by decide⟩
    (prefixCache 12 71997) (prefixPartial 12 71997) = false := by
  decide +kernel

theorem node_context_12_71997_488215 : EJMOriginalGlobalDAGData.nodes 9 ⟨488215, by decide⟩ =
    .split (coordinate 12) (![⟨488153, by decide⟩,⟨488182, by decide⟩,⟨488205, by decide⟩,⟨488214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71997_488215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71997 ⟨488215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71997
    ⟨488215, by decide⟩ (by decide) (![⟨488153, by decide⟩,⟨488182, by decide⟩,⟨488205, by decide⟩,⟨488214, by decide⟩]) unmarked_context_12_71997_488215 node_context_12_71997_488215
  intro a
  fin_cases a
  · exact context_13_287988_488153
  · exact context_13_287989_488182
  · exact context_13_287990_488205
  · exact context_13_287991_488214

theorem selected_cut_19042 : selected 8 ⟨488220, by decide⟩
    (prefixPartial 13 287992) = some ⟨13, 2, 0, 488220, 287992, 157, 16384⟩ := by
  decide +kernel

theorem context_13_287992_488220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287992 ⟨488220, by decide⟩ :=
  accepted_of_selected 13 287992 ⟨488220, by decide⟩ ⟨13, 2, 0, 488220, 287992, 157, 16384⟩
    (by decide) selected_cut_19042

theorem selected_cut_19043 : selected 8 ⟨488257, by decide⟩
    (prefixPartial 13 287993) = some ⟨13, 2, 0, 488257, 287993, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_287993_488257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287993 ⟨488257, by decide⟩ :=
  accepted_of_selected 13 287993 ⟨488257, by decide⟩ ⟨13, 2, 0, 488257, 287993, 3021, 16384⟩
    (by decide) selected_cut_19043

theorem selected_cut_19044 : selected 8 ⟨488297, by decide⟩
    (prefixPartial 13 287994) = some ⟨13, 2, 0, 488297, 287994, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_287994_488297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287994 ⟨488297, by decide⟩ :=
  accepted_of_selected 13 287994 ⟨488297, by decide⟩ ⟨13, 2, 0, 488297, 287994, 2433, 16384⟩
    (by decide) selected_cut_19044

theorem selected_cut_19045 : selected 8 ⟨488307, by decide⟩
    (prefixPartial 13 287995) = some ⟨13, 2, 0, 488307, 287995, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_287995_488307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287995 ⟨488307, by decide⟩ :=
  accepted_of_selected 13 287995 ⟨488307, by decide⟩ ⟨13, 2, 0, 488307, 287995, 1169, 16384⟩
    (by decide) selected_cut_19045

theorem unmarked_context_12_71998_488308 : frontier 9 ⟨488308, by decide⟩
    (prefixCache 12 71998) (prefixPartial 12 71998) = false := by
  decide +kernel

theorem node_context_12_71998_488308 : EJMOriginalGlobalDAGData.nodes 9 ⟨488308, by decide⟩ =
    .split (coordinate 12) (![⟨488220, by decide⟩,⟨488257, by decide⟩,⟨488297, by decide⟩,⟨488307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71998_488308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71998 ⟨488308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71998
    ⟨488308, by decide⟩ (by decide) (![⟨488220, by decide⟩,⟨488257, by decide⟩,⟨488297, by decide⟩,⟨488307, by decide⟩]) unmarked_context_12_71998_488308 node_context_12_71998_488308
  intro a
  fin_cases a
  · exact context_13_287992_488220
  · exact context_13_287993_488257
  · exact context_13_287994_488297
  · exact context_13_287995_488307

theorem selected_cut_19046 : selected 8 ⟨488312, by decide⟩
    (prefixPartial 13 287996) = some ⟨13, 2, 0, 488312, 287996, 93, 16384⟩ := by
  decide +kernel

theorem context_13_287996_488312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287996 ⟨488312, by decide⟩ :=
  accepted_of_selected 13 287996 ⟨488312, by decide⟩ ⟨13, 2, 0, 488312, 287996, 93, 16384⟩
    (by decide) selected_cut_19046

theorem selected_cut_19047 : selected 8 ⟨488351, by decide⟩
    (prefixPartial 13 287997) = some ⟨13, 2, 0, 488351, 287997, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_287997_488351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287997 ⟨488351, by decide⟩ :=
  accepted_of_selected 13 287997 ⟨488351, by decide⟩ ⟨13, 2, 0, 488351, 287997, 3157, 16384⟩
    (by decide) selected_cut_19047

theorem selected_cut_19048 : selected 8 ⟨488390, by decide⟩
    (prefixPartial 13 287998) = some ⟨13, 2, 0, 488390, 287998, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_287998_488390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287998 ⟨488390, by decide⟩ :=
  accepted_of_selected 13 287998 ⟨488390, by decide⟩ ⟨13, 2, 0, 488390, 287998, 2449, 16384⟩
    (by decide) selected_cut_19048

theorem selected_cut_19049 : selected 8 ⟨488397, by decide⟩
    (prefixPartial 13 287999) = some ⟨13, 2, 0, 488397, 287999, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_287999_488397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287999 ⟨488397, by decide⟩ :=
  accepted_of_selected 13 287999 ⟨488397, by decide⟩ ⟨13, 2, 0, 488397, 287999, 1041, 16384⟩
    (by decide) selected_cut_19049

theorem unmarked_context_12_71999_488398 : frontier 9 ⟨488398, by decide⟩
    (prefixCache 12 71999) (prefixPartial 12 71999) = false := by
  decide +kernel

theorem node_context_12_71999_488398 : EJMOriginalGlobalDAGData.nodes 9 ⟨488398, by decide⟩ =
    .split (coordinate 12) (![⟨488312, by decide⟩,⟨488351, by decide⟩,⟨488390, by decide⟩,⟨488397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71999_488398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71999 ⟨488398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71999
    ⟨488398, by decide⟩ (by decide) (![⟨488312, by decide⟩,⟨488351, by decide⟩,⟨488390, by decide⟩,⟨488397, by decide⟩]) unmarked_context_12_71999_488398 node_context_12_71999_488398
  intro a
  fin_cases a
  · exact context_13_287996_488312
  · exact context_13_287997_488351
  · exact context_13_287998_488390
  · exact context_13_287999_488397

theorem unmarked_context_11_17999_488399 : frontier 10 ⟨488399, by decide⟩
    (prefixCache 11 17999) (prefixPartial 11 17999) = false := by
  decide +kernel

theorem node_context_11_17999_488399 : EJMOriginalGlobalDAGData.nodes 10 ⟨488399, by decide⟩ =
    .split (coordinate 11) (![⟨488149, by decide⟩,⟨488215, by decide⟩,⟨488308, by decide⟩,⟨488398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17999_488399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17999 ⟨488399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17999
    ⟨488399, by decide⟩ (by decide) (![⟨488149, by decide⟩,⟨488215, by decide⟩,⟨488308, by decide⟩,⟨488398, by decide⟩]) unmarked_context_11_17999_488399 node_context_11_17999_488399
  intro a
  fin_cases a
  · exact context_12_71996_488149
  · exact context_12_71997_488215
  · exact context_12_71998_488308
  · exact context_12_71999_488398

theorem unmarked_context_10_4499_488400 : frontier 11 ⟨488400, by decide⟩
    (prefixCache 10 4499) (prefixPartial 10 4499) = false := by
  decide +kernel

theorem node_context_10_4499_488400 : EJMOriginalGlobalDAGData.nodes 11 ⟨488400, by decide⟩ =
    .split (coordinate 10) (![⟨487098, by decide⟩,⟨487597, by decide⟩,⟨488001, by decide⟩,⟨488399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4499_488400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4499 ⟨488400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4499
    ⟨488400, by decide⟩ (by decide) (![⟨487098, by decide⟩,⟨487597, by decide⟩,⟨488001, by decide⟩,⟨488399, by decide⟩]) unmarked_context_10_4499_488400 node_context_10_4499_488400
  intro a
  fin_cases a
  · exact context_11_17996_487098
  · exact context_11_17997_487597
  · exact context_11_17998_488001
  · exact context_11_17999_488399

theorem unmarked_context_9_1124_488401 : frontier 12 ⟨488401, by decide⟩
    (prefixCache 9 1124) (prefixPartial 9 1124) = false := by
  decide +kernel

theorem node_context_9_1124_488401 : EJMOriginalGlobalDAGData.nodes 12 ⟨488401, by decide⟩ =
    .split (coordinate 9) (![⟨483014, by decide⟩,⟨484892, by decide⟩,⟨486794, by decide⟩,⟨488400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1124_488401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1124 ⟨488401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1124
    ⟨488401, by decide⟩ (by decide) (![⟨483014, by decide⟩,⟨484892, by decide⟩,⟨486794, by decide⟩,⟨488400, by decide⟩]) unmarked_context_9_1124_488401 node_context_9_1124_488401
  intro a
  fin_cases a
  · exact context_10_4496_483014
  · exact context_10_4497_484892
  · exact context_10_4498_486794
  · exact context_10_4499_488400

theorem selected_cut_19050 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288000) = some ⟨13, 1, 0, 3444, 288000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288000, 1, 16384⟩
    (by decide) selected_cut_19050

theorem selected_cut_19051 : selected 8 ⟨488435, by decide⟩
    (prefixPartial 13 288001) = some ⟨13, 2, 0, 488435, 288001, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_288001_488435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288001 ⟨488435, by decide⟩ :=
  accepted_of_selected 13 288001 ⟨488435, by decide⟩ ⟨13, 2, 0, 488435, 288001, 2149, 16384⟩
    (by decide) selected_cut_19051

theorem selected_cut_19052 : selected 8 ⟨488456, by decide⟩
    (prefixPartial 13 288002) = some ⟨13, 2, 0, 488456, 288002, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_288002_488456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288002 ⟨488456, by decide⟩ :=
  accepted_of_selected 13 288002 ⟨488456, by decide⟩ ⟨13, 2, 0, 488456, 288002, 1657, 16384⟩
    (by decide) selected_cut_19052

theorem selected_cut_19053 : selected 8 ⟨488461, by decide⟩
    (prefixPartial 13 288003) = some ⟨13, 2, 0, 488461, 288003, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_288003_488461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288003 ⟨488461, by decide⟩ :=
  accepted_of_selected 13 288003 ⟨488461, by decide⟩ ⟨13, 2, 0, 488461, 288003, 1073, 16384⟩
    (by decide) selected_cut_19053

theorem unmarked_context_12_72000_488462 : frontier 9 ⟨488462, by decide⟩
    (prefixCache 12 72000) (prefixPartial 12 72000) = false := by
  decide +kernel

theorem node_context_12_72000_488462 : EJMOriginalGlobalDAGData.nodes 9 ⟨488462, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488435, by decide⟩,⟨488456, by decide⟩,⟨488461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72000_488462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72000 ⟨488462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72000
    ⟨488462, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488435, by decide⟩,⟨488456, by decide⟩,⟨488461, by decide⟩]) unmarked_context_12_72000_488462 node_context_12_72000_488462
  intro a
  fin_cases a
  · exact context_13_288000_3444
  · exact context_13_288001_488435
  · exact context_13_288002_488456
  · exact context_13_288003_488461

theorem selected_cut_19054 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288004) = some ⟨13, 1, 0, 3444, 288004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288004, 1, 16384⟩
    (by decide) selected_cut_19054

theorem selected_cut_19055 : selected 8 ⟨488498, by decide⟩
    (prefixPartial 13 288005) = some ⟨13, 2, 0, 488498, 288005, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_288005_488498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288005 ⟨488498, by decide⟩ :=
  accepted_of_selected 13 288005 ⟨488498, by decide⟩ ⟨13, 2, 0, 488498, 288005, 2237, 16384⟩
    (by decide) selected_cut_19055

theorem selected_cut_19056 : selected 8 ⟨488520, by decide⟩
    (prefixPartial 13 288006) = some ⟨13, 2, 0, 488520, 288006, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_288006_488520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288006 ⟨488520, by decide⟩ :=
  accepted_of_selected 13 288006 ⟨488520, by decide⟩ ⟨13, 2, 0, 488520, 288006, 1765, 16384⟩
    (by decide) selected_cut_19056

theorem selected_cut_19057 : selected 8 ⟨488530, by decide⟩
    (prefixPartial 13 288007) = some ⟨13, 2, 0, 488530, 288007, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_288007_488530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288007 ⟨488530, by decide⟩ :=
  accepted_of_selected 13 288007 ⟨488530, by decide⟩ ⟨13, 2, 0, 488530, 288007, 1141, 16384⟩
    (by decide) selected_cut_19057

theorem unmarked_context_12_72001_488531 : frontier 9 ⟨488531, by decide⟩
    (prefixCache 12 72001) (prefixPartial 12 72001) = false := by
  decide +kernel

theorem node_context_12_72001_488531 : EJMOriginalGlobalDAGData.nodes 9 ⟨488531, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488498, by decide⟩,⟨488520, by decide⟩,⟨488530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72001_488531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72001 ⟨488531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72001
    ⟨488531, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488498, by decide⟩,⟨488520, by decide⟩,⟨488530, by decide⟩]) unmarked_context_12_72001_488531 node_context_12_72001_488531
  intro a
  fin_cases a
  · exact context_13_288004_3444
  · exact context_13_288005_488498
  · exact context_13_288006_488520
  · exact context_13_288007_488530

theorem selected_cut_19058 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288008) = some ⟨13, 1, 0, 3444, 288008, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288008_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288008 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288008 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288008, 1, 16384⟩
    (by decide) selected_cut_19058

theorem selected_cut_19059 : selected 8 ⟨488571, by decide⟩
    (prefixPartial 13 288009) = some ⟨13, 2, 0, 488571, 288009, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_288009_488571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288009 ⟨488571, by decide⟩ :=
  accepted_of_selected 13 288009 ⟨488571, by decide⟩ ⟨13, 2, 0, 488571, 288009, 2841, 16384⟩
    (by decide) selected_cut_19059

theorem selected_cut_19060 : selected 8 ⟨488620, by decide⟩
    (prefixPartial 13 288010) = some ⟨13, 2, 0, 488620, 288010, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_288010_488620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288010 ⟨488620, by decide⟩ :=
  accepted_of_selected 13 288010 ⟨488620, by decide⟩ ⟨13, 2, 0, 488620, 288010, 2373, 16384⟩
    (by decide) selected_cut_19060

theorem selected_cut_19061 : selected 8 ⟨488632, by decide⟩
    (prefixPartial 13 288011) = some ⟨13, 2, 0, 488632, 288011, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_288011_488632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288011 ⟨488632, by decide⟩ :=
  accepted_of_selected 13 288011 ⟨488632, by decide⟩ ⟨13, 2, 0, 488632, 288011, 1213, 16384⟩
    (by decide) selected_cut_19061

theorem unmarked_context_12_72002_488633 : frontier 9 ⟨488633, by decide⟩
    (prefixCache 12 72002) (prefixPartial 12 72002) = false := by
  decide +kernel

theorem node_context_12_72002_488633 : EJMOriginalGlobalDAGData.nodes 9 ⟨488633, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488571, by decide⟩,⟨488620, by decide⟩,⟨488632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72002_488633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72002 ⟨488633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72002
    ⟨488633, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488571, by decide⟩,⟨488620, by decide⟩,⟨488632, by decide⟩]) unmarked_context_12_72002_488633 node_context_12_72002_488633
  intro a
  fin_cases a
  · exact context_13_288008_3444
  · exact context_13_288009_488571
  · exact context_13_288010_488620
  · exact context_13_288011_488632

theorem selected_cut_19062 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288012) = some ⟨13, 1, 0, 3444, 288012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288012, 1, 16384⟩
    (by decide) selected_cut_19062

theorem selected_cut_19063 : selected 8 ⟨488663, by decide⟩
    (prefixPartial 13 288013) = some ⟨13, 2, 0, 488663, 288013, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_288013_488663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288013 ⟨488663, by decide⟩ :=
  accepted_of_selected 13 288013 ⟨488663, by decide⟩ ⟨13, 2, 0, 488663, 288013, 2869, 16384⟩
    (by decide) selected_cut_19063

theorem selected_cut_19064 : selected 8 ⟨488687, by decide⟩
    (prefixPartial 13 288014) = some ⟨13, 2, 0, 488687, 288014, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_288014_488687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288014 ⟨488687, by decide⟩ :=
  accepted_of_selected 13 288014 ⟨488687, by decide⟩ ⟨13, 2, 0, 488687, 288014, 2381, 16384⟩
    (by decide) selected_cut_19064

theorem selected_cut_19065 : selected 8 ⟨488696, by decide⟩
    (prefixPartial 13 288015) = some ⟨13, 2, 0, 488696, 288015, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_288015_488696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288015 ⟨488696, by decide⟩ :=
  accepted_of_selected 13 288015 ⟨488696, by decide⟩ ⟨13, 2, 0, 488696, 288015, 1177, 16384⟩
    (by decide) selected_cut_19065

theorem unmarked_context_12_72003_488697 : frontier 9 ⟨488697, by decide⟩
    (prefixCache 12 72003) (prefixPartial 12 72003) = false := by
  decide +kernel

theorem node_context_12_72003_488697 : EJMOriginalGlobalDAGData.nodes 9 ⟨488697, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488663, by decide⟩,⟨488687, by decide⟩,⟨488696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72003_488697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72003 ⟨488697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72003
    ⟨488697, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488663, by decide⟩,⟨488687, by decide⟩,⟨488696, by decide⟩]) unmarked_context_12_72003_488697 node_context_12_72003_488697
  intro a
  fin_cases a
  · exact context_13_288012_3444
  · exact context_13_288013_488663
  · exact context_13_288014_488687
  · exact context_13_288015_488696

theorem unmarked_context_11_18000_488698 : frontier 10 ⟨488698, by decide⟩
    (prefixCache 11 18000) (prefixPartial 11 18000) = false := by
  decide +kernel

theorem node_context_11_18000_488698 : EJMOriginalGlobalDAGData.nodes 10 ⟨488698, by decide⟩ =
    .split (coordinate 11) (![⟨488462, by decide⟩,⟨488531, by decide⟩,⟨488633, by decide⟩,⟨488697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18000_488698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18000 ⟨488698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18000
    ⟨488698, by decide⟩ (by decide) (![⟨488462, by decide⟩,⟨488531, by decide⟩,⟨488633, by decide⟩,⟨488697, by decide⟩]) unmarked_context_11_18000_488698 node_context_11_18000_488698
  intro a
  fin_cases a
  · exact context_12_72000_488462
  · exact context_12_72001_488531
  · exact context_12_72002_488633
  · exact context_12_72003_488697

theorem selected_cut_19066 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288016) = some ⟨13, 1, 0, 3444, 288016, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288016_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288016 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288016 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288016, 1, 16384⟩
    (by decide) selected_cut_19066

theorem selected_cut_19067 : selected 8 ⟨488722, by decide⟩
    (prefixPartial 13 288017) = some ⟨13, 2, 0, 488722, 288017, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_288017_488722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288017 ⟨488722, by decide⟩ :=
  accepted_of_selected 13 288017 ⟨488722, by decide⟩ ⟨13, 2, 0, 488722, 288017, 2253, 16384⟩
    (by decide) selected_cut_19067

theorem selected_cut_19068 : selected 8 ⟨488744, by decide⟩
    (prefixPartial 13 288018) = some ⟨13, 2, 0, 488744, 288018, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_288018_488744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288018 ⟨488744, by decide⟩ :=
  accepted_of_selected 13 288018 ⟨488744, by decide⟩ ⟨13, 2, 0, 488744, 288018, 1849, 16384⟩
    (by decide) selected_cut_19068

theorem selected_cut_19069 : selected 8 ⟨488750, by decide⟩
    (prefixPartial 13 288019) = some ⟨13, 2, 0, 488750, 288019, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_288019_488750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288019 ⟨488750, by decide⟩ :=
  accepted_of_selected 13 288019 ⟨488750, by decide⟩ ⟨13, 2, 0, 488750, 288019, 1093, 16384⟩
    (by decide) selected_cut_19069

theorem unmarked_context_12_72004_488751 : frontier 9 ⟨488751, by decide⟩
    (prefixCache 12 72004) (prefixPartial 12 72004) = false := by
  decide +kernel

theorem node_context_12_72004_488751 : EJMOriginalGlobalDAGData.nodes 9 ⟨488751, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488722, by decide⟩,⟨488744, by decide⟩,⟨488750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72004_488751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72004 ⟨488751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72004
    ⟨488751, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488722, by decide⟩,⟨488744, by decide⟩,⟨488750, by decide⟩]) unmarked_context_12_72004_488751 node_context_12_72004_488751
  intro a
  fin_cases a
  · exact context_13_288016_3444
  · exact context_13_288017_488722
  · exact context_13_288018_488744
  · exact context_13_288019_488750

theorem selected_cut_19070 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 72005) = some ⟨12, 1, 0, 441672, 72005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72005_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72005 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 72005 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 72005, 1, 65536⟩
    (by decide) selected_cut_19070

theorem selected_cut_19071 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288024) = some ⟨13, 1, 0, 3444, 288024, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288024_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288024 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288024 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288024, 1, 16384⟩
    (by decide) selected_cut_19071

theorem selected_cut_19072 : selected 8 ⟨488790, by decide⟩
    (prefixPartial 13 288025) = some ⟨13, 2, 0, 488790, 288025, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_288025_488790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288025 ⟨488790, by decide⟩ :=
  accepted_of_selected 13 288025 ⟨488790, by decide⟩ ⟨13, 2, 0, 488790, 288025, 2549, 16384⟩
    (by decide) selected_cut_19072

theorem selected_cut_19073 : selected 8 ⟨488832, by decide⟩
    (prefixPartial 13 288026) = some ⟨13, 2, 0, 488832, 288026, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_288026_488832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288026 ⟨488832, by decide⟩ :=
  accepted_of_selected 13 288026 ⟨488832, by decide⟩ ⟨13, 2, 0, 488832, 288026, 2321, 16384⟩
    (by decide) selected_cut_19073

theorem selected_cut_19074 : selected 8 ⟨488845, by decide⟩
    (prefixPartial 13 288027) = some ⟨13, 2, 0, 488845, 288027, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_288027_488845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288027 ⟨488845, by decide⟩ :=
  accepted_of_selected 13 288027 ⟨488845, by decide⟩ ⟨13, 2, 0, 488845, 288027, 1189, 16384⟩
    (by decide) selected_cut_19074

theorem unmarked_context_12_72006_488846 : frontier 9 ⟨488846, by decide⟩
    (prefixCache 12 72006) (prefixPartial 12 72006) = false := by
  decide +kernel

theorem node_context_12_72006_488846 : EJMOriginalGlobalDAGData.nodes 9 ⟨488846, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488790, by decide⟩,⟨488832, by decide⟩,⟨488845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72006_488846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72006 ⟨488846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72006
    ⟨488846, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488790, by decide⟩,⟨488832, by decide⟩,⟨488845, by decide⟩]) unmarked_context_12_72006_488846 node_context_12_72006_488846
  intro a
  fin_cases a
  · exact context_13_288024_3444
  · exact context_13_288025_488790
  · exact context_13_288026_488832
  · exact context_13_288027_488845

theorem selected_cut_19075 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288028) = some ⟨13, 1, 0, 3444, 288028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288028, 1, 16384⟩
    (by decide) selected_cut_19075

theorem selected_cut_19076 : selected 8 ⟨488881, by decide⟩
    (prefixPartial 13 288029) = some ⟨13, 2, 0, 488881, 288029, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_288029_488881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288029 ⟨488881, by decide⟩ :=
  accepted_of_selected 13 288029 ⟨488881, by decide⟩ ⟨13, 2, 0, 488881, 288029, 2545, 16384⟩
    (by decide) selected_cut_19076

theorem selected_cut_19077 : selected 8 ⟨488921, by decide⟩
    (prefixPartial 13 288030) = some ⟨13, 2, 0, 488921, 288030, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_288030_488921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288030 ⟨488921, by decide⟩ :=
  accepted_of_selected 13 288030 ⟨488921, by decide⟩ ⟨13, 2, 0, 488921, 288030, 2453, 16384⟩
    (by decide) selected_cut_19077

theorem selected_cut_19078 : selected 8 ⟨488931, by decide⟩
    (prefixPartial 13 288031) = some ⟨13, 2, 0, 488931, 288031, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_288031_488931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288031 ⟨488931, by decide⟩ :=
  accepted_of_selected 13 288031 ⟨488931, by decide⟩ ⟨13, 2, 0, 488931, 288031, 1049, 16384⟩
    (by decide) selected_cut_19078

theorem unmarked_context_12_72007_488932 : frontier 9 ⟨488932, by decide⟩
    (prefixCache 12 72007) (prefixPartial 12 72007) = false := by
  decide +kernel

theorem node_context_12_72007_488932 : EJMOriginalGlobalDAGData.nodes 9 ⟨488932, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488881, by decide⟩,⟨488921, by decide⟩,⟨488931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72007_488932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72007 ⟨488932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72007
    ⟨488932, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488881, by decide⟩,⟨488921, by decide⟩,⟨488931, by decide⟩]) unmarked_context_12_72007_488932 node_context_12_72007_488932
  intro a
  fin_cases a
  · exact context_13_288028_3444
  · exact context_13_288029_488881
  · exact context_13_288030_488921
  · exact context_13_288031_488931

theorem unmarked_context_11_18001_488933 : frontier 10 ⟨488933, by decide⟩
    (prefixCache 11 18001) (prefixPartial 11 18001) = false := by
  decide +kernel

theorem node_context_11_18001_488933 : EJMOriginalGlobalDAGData.nodes 10 ⟨488933, by decide⟩ =
    .split (coordinate 11) (![⟨488751, by decide⟩,⟨441672, by decide⟩,⟨488846, by decide⟩,⟨488932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18001_488933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18001 ⟨488933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18001
    ⟨488933, by decide⟩ (by decide) (![⟨488751, by decide⟩,⟨441672, by decide⟩,⟨488846, by decide⟩,⟨488932, by decide⟩]) unmarked_context_11_18001_488933 node_context_11_18001_488933
  intro a
  fin_cases a
  · exact context_12_72004_488751
  · exact context_12_72005_441672
  · exact context_12_72006_488846
  · exact context_12_72007_488932

theorem selected_cut_19079 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288032) = some ⟨13, 1, 0, 3444, 288032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288032, 1, 16384⟩
    (by decide) selected_cut_19079

theorem selected_cut_19080 : selected 8 ⟨488954, by decide⟩
    (prefixPartial 13 288033) = some ⟨13, 2, 0, 488954, 288033, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_288033_488954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288033 ⟨488954, by decide⟩ :=
  accepted_of_selected 13 288033 ⟨488954, by decide⟩ ⟨13, 2, 0, 488954, 288033, 2245, 16384⟩
    (by decide) selected_cut_19080

theorem selected_cut_19081 : selected 8 ⟨488972, by decide⟩
    (prefixPartial 13 288034) = some ⟨13, 2, 0, 488972, 288034, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_288034_488972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288034 ⟨488972, by decide⟩ :=
  accepted_of_selected 13 288034 ⟨488972, by decide⟩ ⟨13, 2, 0, 488972, 288034, 1841, 16384⟩
    (by decide) selected_cut_19081

theorem selected_cut_19082 : selected 8 ⟨488977, by decide⟩
    (prefixPartial 13 288035) = some ⟨13, 2, 0, 488977, 288035, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_288035_488977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288035 ⟨488977, by decide⟩ :=
  accepted_of_selected 13 288035 ⟨488977, by decide⟩ ⟨13, 2, 0, 488977, 288035, 1121, 16384⟩
    (by decide) selected_cut_19082

theorem unmarked_context_12_72008_488978 : frontier 9 ⟨488978, by decide⟩
    (prefixCache 12 72008) (prefixPartial 12 72008) = false := by
  decide +kernel

theorem node_context_12_72008_488978 : EJMOriginalGlobalDAGData.nodes 9 ⟨488978, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨488954, by decide⟩,⟨488972, by decide⟩,⟨488977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72008_488978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72008 ⟨488978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72008
    ⟨488978, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨488954, by decide⟩,⟨488972, by decide⟩,⟨488977, by decide⟩]) unmarked_context_12_72008_488978 node_context_12_72008_488978
  intro a
  fin_cases a
  · exact context_13_288032_3444
  · exact context_13_288033_488954
  · exact context_13_288034_488972
  · exact context_13_288035_488977

theorem selected_cut_19083 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288036) = some ⟨13, 1, 0, 3444, 288036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288036, 1, 16384⟩
    (by decide) selected_cut_19083

theorem selected_cut_19084 : selected 8 ⟨489001, by decide⟩
    (prefixPartial 13 288037) = some ⟨13, 2, 0, 489001, 288037, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_288037_489001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288037 ⟨489001, by decide⟩ :=
  accepted_of_selected 13 288037 ⟨489001, by decide⟩ ⟨13, 2, 0, 489001, 288037, 2033, 16384⟩
    (by decide) selected_cut_19084

theorem selected_cut_19085 : selected 8 ⟨489020, by decide⟩
    (prefixPartial 13 288038) = some ⟨13, 2, 0, 489020, 288038, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_288038_489020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288038 ⟨489020, by decide⟩ :=
  accepted_of_selected 13 288038 ⟨489020, by decide⟩ ⟨13, 2, 0, 489020, 288038, 1785, 16384⟩
    (by decide) selected_cut_19085

theorem selected_cut_19086 : selected 8 ⟨489027, by decide⟩
    (prefixPartial 13 288039) = some ⟨13, 2, 0, 489027, 288039, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_288039_489027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288039 ⟨489027, by decide⟩ :=
  accepted_of_selected 13 288039 ⟨489027, by decide⟩ ⟨13, 2, 0, 489027, 288039, 1145, 16384⟩
    (by decide) selected_cut_19086

theorem unmarked_context_12_72009_489028 : frontier 9 ⟨489028, by decide⟩
    (prefixCache 12 72009) (prefixPartial 12 72009) = false := by
  decide +kernel

theorem node_context_12_72009_489028 : EJMOriginalGlobalDAGData.nodes 9 ⟨489028, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489001, by decide⟩,⟨489020, by decide⟩,⟨489027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72009_489028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72009 ⟨489028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72009
    ⟨489028, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489001, by decide⟩,⟨489020, by decide⟩,⟨489027, by decide⟩]) unmarked_context_12_72009_489028 node_context_12_72009_489028
  intro a
  fin_cases a
  · exact context_13_288036_3444
  · exact context_13_288037_489001
  · exact context_13_288038_489020
  · exact context_13_288039_489027

theorem selected_cut_19087 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288040) = some ⟨13, 1, 0, 3444, 288040, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288040_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288040 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288040 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288040, 1, 16384⟩
    (by decide) selected_cut_19087

theorem selected_cut_19088 : selected 8 ⟨489055, by decide⟩
    (prefixPartial 13 288041) = some ⟨13, 2, 0, 489055, 288041, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_288041_489055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288041 ⟨489055, by decide⟩ :=
  accepted_of_selected 13 288041 ⟨489055, by decide⟩ ⟨13, 2, 0, 489055, 288041, 2381, 16384⟩
    (by decide) selected_cut_19088

theorem selected_cut_19089 : selected 8 ⟨489087, by decide⟩
    (prefixPartial 13 288042) = some ⟨13, 2, 0, 489087, 288042, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_288042_489087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288042 ⟨489087, by decide⟩ :=
  accepted_of_selected 13 288042 ⟨489087, by decide⟩ ⟨13, 2, 0, 489087, 288042, 2205, 16384⟩
    (by decide) selected_cut_19089

theorem selected_cut_19090 : selected 8 ⟨489093, by decide⟩
    (prefixPartial 13 288043) = some ⟨13, 2, 0, 489093, 288043, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_288043_489093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288043 ⟨489093, by decide⟩ :=
  accepted_of_selected 13 288043 ⟨489093, by decide⟩ ⟨13, 2, 0, 489093, 288043, 1113, 16384⟩
    (by decide) selected_cut_19090

theorem unmarked_context_12_72010_489094 : frontier 9 ⟨489094, by decide⟩
    (prefixCache 12 72010) (prefixPartial 12 72010) = false := by
  decide +kernel

theorem node_context_12_72010_489094 : EJMOriginalGlobalDAGData.nodes 9 ⟨489094, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489055, by decide⟩,⟨489087, by decide⟩,⟨489093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72010_489094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72010 ⟨489094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72010
    ⟨489094, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489055, by decide⟩,⟨489087, by decide⟩,⟨489093, by decide⟩]) unmarked_context_12_72010_489094 node_context_12_72010_489094
  intro a
  fin_cases a
  · exact context_13_288040_3444
  · exact context_13_288041_489055
  · exact context_13_288042_489087
  · exact context_13_288043_489093

theorem selected_cut_19091 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288044) = some ⟨13, 1, 0, 3444, 288044, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288044_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288044 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288044 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288044, 1, 16384⟩
    (by decide) selected_cut_19091

theorem selected_cut_19092 : selected 8 ⟨489119, by decide⟩
    (prefixPartial 13 288045) = some ⟨13, 2, 0, 489119, 288045, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_288045_489119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288045 ⟨489119, by decide⟩ :=
  accepted_of_selected 13 288045 ⟨489119, by decide⟩ ⟨13, 2, 0, 489119, 288045, 2437, 16384⟩
    (by decide) selected_cut_19092

theorem selected_cut_19093 : selected 8 ⟨489142, by decide⟩
    (prefixPartial 13 288046) = some ⟨13, 2, 0, 489142, 288046, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_288046_489142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288046 ⟨489142, by decide⟩ :=
  accepted_of_selected 13 288046 ⟨489142, by decide⟩ ⟨13, 2, 0, 489142, 288046, 2233, 16384⟩
    (by decide) selected_cut_19093

theorem selected_cut_19094 : selected 8 ⟨489151, by decide⟩
    (prefixPartial 13 288047) = some ⟨13, 2, 0, 489151, 288047, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_288047_489151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288047 ⟨489151, by decide⟩ :=
  accepted_of_selected 13 288047 ⟨489151, by decide⟩ ⟨13, 2, 0, 489151, 288047, 1165, 16384⟩
    (by decide) selected_cut_19094

theorem unmarked_context_12_72011_489152 : frontier 9 ⟨489152, by decide⟩
    (prefixCache 12 72011) (prefixPartial 12 72011) = false := by
  decide +kernel

theorem node_context_12_72011_489152 : EJMOriginalGlobalDAGData.nodes 9 ⟨489152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489119, by decide⟩,⟨489142, by decide⟩,⟨489151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72011_489152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72011 ⟨489152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72011
    ⟨489152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489119, by decide⟩,⟨489142, by decide⟩,⟨489151, by decide⟩]) unmarked_context_12_72011_489152 node_context_12_72011_489152
  intro a
  fin_cases a
  · exact context_13_288044_3444
  · exact context_13_288045_489119
  · exact context_13_288046_489142
  · exact context_13_288047_489151

theorem unmarked_context_11_18002_489153 : frontier 10 ⟨489153, by decide⟩
    (prefixCache 11 18002) (prefixPartial 11 18002) = false := by
  decide +kernel

theorem node_context_11_18002_489153 : EJMOriginalGlobalDAGData.nodes 10 ⟨489153, by decide⟩ =
    .split (coordinate 11) (![⟨488978, by decide⟩,⟨489028, by decide⟩,⟨489094, by decide⟩,⟨489152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18002_489153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18002 ⟨489153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18002
    ⟨489153, by decide⟩ (by decide) (![⟨488978, by decide⟩,⟨489028, by decide⟩,⟨489094, by decide⟩,⟨489152, by decide⟩]) unmarked_context_11_18002_489153 node_context_11_18002_489153
  intro a
  fin_cases a
  · exact context_12_72008_488978
  · exact context_12_72009_489028
  · exact context_12_72010_489094
  · exact context_12_72011_489152

theorem selected_cut_19095 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288048) = some ⟨13, 1, 0, 3444, 288048, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288048_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288048 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288048 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288048, 1, 16384⟩
    (by decide) selected_cut_19095

theorem selected_cut_19096 : selected 8 ⟨489179, by decide⟩
    (prefixPartial 13 288049) = some ⟨13, 2, 0, 489179, 288049, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_288049_489179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288049 ⟨489179, by decide⟩ :=
  accepted_of_selected 13 288049 ⟨489179, by decide⟩ ⟨13, 2, 0, 489179, 288049, 2293, 16384⟩
    (by decide) selected_cut_19096

theorem selected_cut_19097 : selected 8 ⟨489196, by decide⟩
    (prefixPartial 13 288050) = some ⟨13, 2, 0, 489196, 288050, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_288050_489196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288050 ⟨489196, by decide⟩ :=
  accepted_of_selected 13 288050 ⟨489196, by decide⟩ ⟨13, 2, 0, 489196, 288050, 1997, 16384⟩
    (by decide) selected_cut_19097

theorem selected_cut_19098 : selected 8 ⟨489204, by decide⟩
    (prefixPartial 13 288051) = some ⟨13, 2, 0, 489204, 288051, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_288051_489204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288051 ⟨489204, by decide⟩ :=
  accepted_of_selected 13 288051 ⟨489204, by decide⟩ ⟨13, 2, 0, 489204, 288051, 1257, 16384⟩
    (by decide) selected_cut_19098

theorem unmarked_context_12_72012_489205 : frontier 9 ⟨489205, by decide⟩
    (prefixCache 12 72012) (prefixPartial 12 72012) = false := by
  decide +kernel

theorem node_context_12_72012_489205 : EJMOriginalGlobalDAGData.nodes 9 ⟨489205, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489179, by decide⟩,⟨489196, by decide⟩,⟨489204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72012_489205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72012 ⟨489205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72012
    ⟨489205, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489179, by decide⟩,⟨489196, by decide⟩,⟨489204, by decide⟩]) unmarked_context_12_72012_489205 node_context_12_72012_489205
  intro a
  fin_cases a
  · exact context_13_288048_3444
  · exact context_13_288049_489179
  · exact context_13_288050_489196
  · exact context_13_288051_489204

theorem selected_cut_19099 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288052) = some ⟨13, 1, 0, 3444, 288052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288052, 1, 16384⟩
    (by decide) selected_cut_19099

theorem selected_cut_19100 : selected 8 ⟨489228, by decide⟩
    (prefixPartial 13 288053) = some ⟨13, 2, 0, 489228, 288053, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_288053_489228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288053 ⟨489228, by decide⟩ :=
  accepted_of_selected 13 288053 ⟨489228, by decide⟩ ⟨13, 2, 0, 489228, 288053, 2017, 16384⟩
    (by decide) selected_cut_19100

theorem selected_cut_19101 : selected 8 ⟨489249, by decide⟩
    (prefixPartial 13 288054) = some ⟨13, 2, 0, 489249, 288054, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_288054_489249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288054 ⟨489249, by decide⟩ :=
  accepted_of_selected 13 288054 ⟨489249, by decide⟩ ⟨13, 2, 0, 489249, 288054, 1953, 16384⟩
    (by decide) selected_cut_19101

theorem selected_cut_19102 : selected 8 ⟨489264, by decide⟩
    (prefixPartial 13 288055) = some ⟨13, 2, 0, 489264, 288055, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_288055_489264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288055 ⟨489264, by decide⟩ :=
  accepted_of_selected 13 288055 ⟨489264, by decide⟩ ⟨13, 2, 0, 489264, 288055, 1225, 16384⟩
    (by decide) selected_cut_19102

theorem unmarked_context_12_72013_489265 : frontier 9 ⟨489265, by decide⟩
    (prefixCache 12 72013) (prefixPartial 12 72013) = false := by
  decide +kernel

theorem node_context_12_72013_489265 : EJMOriginalGlobalDAGData.nodes 9 ⟨489265, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489228, by decide⟩,⟨489249, by decide⟩,⟨489264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72013_489265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72013 ⟨489265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72013
    ⟨489265, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489228, by decide⟩,⟨489249, by decide⟩,⟨489264, by decide⟩]) unmarked_context_12_72013_489265 node_context_12_72013_489265
  intro a
  fin_cases a
  · exact context_13_288052_3444
  · exact context_13_288053_489228
  · exact context_13_288054_489249
  · exact context_13_288055_489264

theorem selected_cut_19103 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288056) = some ⟨13, 1, 0, 3444, 288056, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288056_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288056 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288056 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288056, 1, 16384⟩
    (by decide) selected_cut_19103

theorem selected_cut_19104 : selected 8 ⟨489299, by decide⟩
    (prefixPartial 13 288057) = some ⟨13, 2, 0, 489299, 288057, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_288057_489299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288057 ⟨489299, by decide⟩ :=
  accepted_of_selected 13 288057 ⟨489299, by decide⟩ ⟨13, 2, 0, 489299, 288057, 2501, 16384⟩
    (by decide) selected_cut_19104

theorem selected_cut_19105 : selected 8 ⟨489333, by decide⟩
    (prefixPartial 13 288058) = some ⟨13, 2, 0, 489333, 288058, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_288058_489333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288058 ⟨489333, by decide⟩ :=
  accepted_of_selected 13 288058 ⟨489333, by decide⟩ ⟨13, 2, 0, 489333, 288058, 2353, 16384⟩
    (by decide) selected_cut_19105

theorem selected_cut_19106 : selected 8 ⟨489344, by decide⟩
    (prefixPartial 13 288059) = some ⟨13, 2, 0, 489344, 288059, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_288059_489344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288059 ⟨489344, by decide⟩ :=
  accepted_of_selected 13 288059 ⟨489344, by decide⟩ ⟨13, 2, 0, 489344, 288059, 1209, 16384⟩
    (by decide) selected_cut_19106

theorem unmarked_context_12_72014_489345 : frontier 9 ⟨489345, by decide⟩
    (prefixCache 12 72014) (prefixPartial 12 72014) = false := by
  decide +kernel

theorem node_context_12_72014_489345 : EJMOriginalGlobalDAGData.nodes 9 ⟨489345, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489299, by decide⟩,⟨489333, by decide⟩,⟨489344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72014_489345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72014 ⟨489345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72014
    ⟨489345, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489299, by decide⟩,⟨489333, by decide⟩,⟨489344, by decide⟩]) unmarked_context_12_72014_489345 node_context_12_72014_489345
  intro a
  fin_cases a
  · exact context_13_288056_3444
  · exact context_13_288057_489299
  · exact context_13_288058_489333
  · exact context_13_288059_489344

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
