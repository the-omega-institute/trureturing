/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover374
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36003 : selected 9 ⟨949020, by decide⟩
    (prefixPartial 12 287640) = some ⟨12, 2, 0, 949020, 287640, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_287640_949020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287640 ⟨949020, by decide⟩ :=
  accepted_of_selected 12 287640 ⟨949020, by decide⟩ ⟨12, 2, 0, 949020, 287640, 1313, 65536⟩
    (by decide) selected_cut_36003

theorem selected_cut_36004 : selected 9 ⟨949040, by decide⟩
    (prefixPartial 12 287641) = some ⟨12, 2, 0, 949040, 287641, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_287641_949040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287641 ⟨949040, by decide⟩ :=
  accepted_of_selected 12 287641 ⟨949040, by decide⟩ ⟨12, 2, 0, 949040, 287641, 1297, 65536⟩
    (by decide) selected_cut_36004

theorem selected_cut_36005 : selected 9 ⟨949053, by decide⟩
    (prefixPartial 12 287642) = some ⟨12, 2, 0, 949053, 287642, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_287642_949053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287642 ⟨949053, by decide⟩ :=
  accepted_of_selected 12 287642 ⟨949053, by decide⟩ ⟨12, 2, 0, 949053, 287642, 1209, 65536⟩
    (by decide) selected_cut_36005

theorem selected_cut_36006 : selected 9 ⟨949068, by decide⟩
    (prefixPartial 12 287643) = some ⟨12, 2, 0, 949068, 287643, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_287643_949068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287643 ⟨949068, by decide⟩ :=
  accepted_of_selected 12 287643 ⟨949068, by decide⟩ ⟨12, 2, 0, 949068, 287643, 1257, 65536⟩
    (by decide) selected_cut_36006

theorem unmarked_context_11_71910_949069 : frontier 10 ⟨949069, by decide⟩
    (prefixCache 11 71910) (prefixPartial 11 71910) = false := by
  decide +kernel

theorem node_context_11_71910_949069 : EJMOriginalGlobalDAGData.nodes 10 ⟨949069, by decide⟩ =
    .split (coordinate 11) (![⟨949020, by decide⟩,⟨949040, by decide⟩,⟨949053, by decide⟩,⟨949068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71910_949069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71910 ⟨949069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71910
    ⟨949069, by decide⟩ (by decide) (![⟨949020, by decide⟩,⟨949040, by decide⟩,⟨949053, by decide⟩,⟨949068, by decide⟩]) unmarked_context_11_71910_949069 node_context_11_71910_949069
  intro a
  fin_cases a
  · exact context_12_287640_949020
  · exact context_12_287641_949040
  · exact context_12_287642_949053
  · exact context_12_287643_949068

theorem selected_cut_36007 : selected 10 ⟨949112, by decide⟩
    (prefixPartial 11 71911) = some ⟨11, 2, 0, 949112, 71911, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_71911_949112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71911 ⟨949112, by decide⟩ :=
  accepted_of_selected 11 71911 ⟨949112, by decide⟩ ⟨11, 2, 0, 949112, 71911, 3277, 262144⟩
    (by decide) selected_cut_36007

theorem unmarked_context_10_17977_949113 : frontier 11 ⟨949113, by decide⟩
    (prefixCache 10 17977) (prefixPartial 10 17977) = false := by
  decide +kernel

theorem node_context_10_17977_949113 : EJMOriginalGlobalDAGData.nodes 11 ⟨949113, by decide⟩ =
    .split (coordinate 10) (![⟨948942, by decide⟩,⟨949002, by decide⟩,⟨949069, by decide⟩,⟨949112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17977_949113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17977 ⟨949113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17977
    ⟨949113, by decide⟩ (by decide) (![⟨948942, by decide⟩,⟨949002, by decide⟩,⟨949069, by decide⟩,⟨949112, by decide⟩]) unmarked_context_10_17977_949113 node_context_10_17977_949113
  intro a
  fin_cases a
  · exact context_11_71908_948942
  · exact context_11_71909_949002
  · exact context_11_71910_949069
  · exact context_11_71911_949112

theorem selected_cut_36008 : selected 9 ⟨949125, by decide⟩
    (prefixPartial 12 287648) = some ⟨12, 2, 0, 949125, 287648, 981, 65536⟩ := by
  decide +kernel

theorem context_12_287648_949125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287648 ⟨949125, by decide⟩ :=
  accepted_of_selected 12 287648 ⟨949125, by decide⟩ ⟨12, 2, 0, 949125, 287648, 981, 65536⟩
    (by decide) selected_cut_36008

theorem selected_cut_36009 : selected 9 ⟨949135, by decide⟩
    (prefixPartial 12 287649) = some ⟨12, 2, 0, 949135, 287649, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_287649_949135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287649 ⟨949135, by decide⟩ :=
  accepted_of_selected 12 287649 ⟨949135, by decide⟩ ⟨12, 2, 0, 949135, 287649, 1057, 65536⟩
    (by decide) selected_cut_36009

theorem selected_cut_36010 : selected 9 ⟨949153, by decide⟩
    (prefixPartial 12 287650) = some ⟨12, 2, 0, 949153, 287650, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_287650_949153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287650 ⟨949153, by decide⟩ :=
  accepted_of_selected 12 287650 ⟨949153, by decide⟩ ⟨12, 2, 0, 949153, 287650, 1185, 65536⟩
    (by decide) selected_cut_36010

theorem selected_cut_36011 : selected 9 ⟨949165, by decide⟩
    (prefixPartial 12 287651) = some ⟨12, 2, 0, 949165, 287651, 977, 65536⟩ := by
  decide +kernel

theorem context_12_287651_949165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287651 ⟨949165, by decide⟩ :=
  accepted_of_selected 12 287651 ⟨949165, by decide⟩ ⟨12, 2, 0, 949165, 287651, 977, 65536⟩
    (by decide) selected_cut_36011

theorem unmarked_context_11_71912_949166 : frontier 10 ⟨949166, by decide⟩
    (prefixCache 11 71912) (prefixPartial 11 71912) = false := by
  decide +kernel

theorem node_context_11_71912_949166 : EJMOriginalGlobalDAGData.nodes 10 ⟨949166, by decide⟩ =
    .split (coordinate 11) (![⟨949125, by decide⟩,⟨949135, by decide⟩,⟨949153, by decide⟩,⟨949165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71912_949166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71912 ⟨949166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71912
    ⟨949166, by decide⟩ (by decide) (![⟨949125, by decide⟩,⟨949135, by decide⟩,⟨949153, by decide⟩,⟨949165, by decide⟩]) unmarked_context_11_71912_949166 node_context_11_71912_949166
  intro a
  fin_cases a
  · exact context_12_287648_949125
  · exact context_12_287649_949135
  · exact context_12_287650_949153
  · exact context_12_287651_949165

theorem selected_cut_36012 : selected 10 ⟨949202, by decide⟩
    (prefixPartial 11 71913) = some ⟨11, 2, 0, 949202, 71913, 2889, 262144⟩ := by
  decide +kernel

theorem context_11_71913_949202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71913 ⟨949202, by decide⟩ :=
  accepted_of_selected 11 71913 ⟨949202, by decide⟩ ⟨11, 2, 0, 949202, 71913, 2889, 262144⟩
    (by decide) selected_cut_36012

theorem selected_cut_36013 : selected 10 ⟨949240, by decide⟩
    (prefixPartial 11 71914) = some ⟨11, 2, 0, 949240, 71914, 2881, 262144⟩ := by
  decide +kernel

theorem context_11_71914_949240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71914 ⟨949240, by decide⟩ :=
  accepted_of_selected 11 71914 ⟨949240, by decide⟩ ⟨11, 2, 0, 949240, 71914, 2881, 262144⟩
    (by decide) selected_cut_36013

theorem selected_cut_36014 : selected 10 ⟨949287, by decide⟩
    (prefixPartial 11 71915) = some ⟨11, 2, 0, 949287, 71915, 3045, 262144⟩ := by
  decide +kernel

theorem context_11_71915_949287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71915 ⟨949287, by decide⟩ :=
  accepted_of_selected 11 71915 ⟨949287, by decide⟩ ⟨11, 2, 0, 949287, 71915, 3045, 262144⟩
    (by decide) selected_cut_36014

theorem unmarked_context_10_17978_949288 : frontier 11 ⟨949288, by decide⟩
    (prefixCache 10 17978) (prefixPartial 10 17978) = false := by
  decide +kernel

theorem node_context_10_17978_949288 : EJMOriginalGlobalDAGData.nodes 11 ⟨949288, by decide⟩ =
    .split (coordinate 10) (![⟨949166, by decide⟩,⟨949202, by decide⟩,⟨949240, by decide⟩,⟨949287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17978_949288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17978 ⟨949288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17978
    ⟨949288, by decide⟩ (by decide) (![⟨949166, by decide⟩,⟨949202, by decide⟩,⟨949240, by decide⟩,⟨949287, by decide⟩]) unmarked_context_10_17978_949288 node_context_10_17978_949288
  intro a
  fin_cases a
  · exact context_11_71912_949166
  · exact context_11_71913_949202
  · exact context_11_71914_949240
  · exact context_11_71915_949287

theorem selected_cut_36015 : selected 10 ⟨949344, by decide⟩
    (prefixPartial 11 71916) = some ⟨11, 2, 0, 949344, 71916, 3985, 262144⟩ := by
  decide +kernel

theorem context_11_71916_949344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71916 ⟨949344, by decide⟩ :=
  accepted_of_selected 11 71916 ⟨949344, by decide⟩ ⟨11, 2, 0, 949344, 71916, 3985, 262144⟩
    (by decide) selected_cut_36015

theorem selected_cut_36016 : selected 10 ⟨949397, by decide⟩
    (prefixPartial 11 71917) = some ⟨11, 2, 0, 949397, 71917, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_71917_949397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71917 ⟨949397, by decide⟩ :=
  accepted_of_selected 11 71917 ⟨949397, by decide⟩ ⟨11, 2, 0, 949397, 71917, 3537, 262144⟩
    (by decide) selected_cut_36016

theorem selected_cut_36017 : selected 10 ⟨949442, by decide⟩
    (prefixPartial 11 71918) = some ⟨11, 2, 0, 949442, 71918, 3601, 262144⟩ := by
  decide +kernel

theorem context_11_71918_949442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71918 ⟨949442, by decide⟩ :=
  accepted_of_selected 11 71918 ⟨949442, by decide⟩ ⟨11, 2, 0, 949442, 71918, 3601, 262144⟩
    (by decide) selected_cut_36017

theorem selected_cut_36018 : selected 10 ⟨949477, by decide⟩
    (prefixPartial 11 71919) = some ⟨11, 2, 0, 949477, 71919, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_71919_949477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71919 ⟨949477, by decide⟩ :=
  accepted_of_selected 11 71919 ⟨949477, by decide⟩ ⟨11, 2, 0, 949477, 71919, 2425, 262144⟩
    (by decide) selected_cut_36018

theorem unmarked_context_10_17979_949478 : frontier 11 ⟨949478, by decide⟩
    (prefixCache 10 17979) (prefixPartial 10 17979) = false := by
  decide +kernel

theorem node_context_10_17979_949478 : EJMOriginalGlobalDAGData.nodes 11 ⟨949478, by decide⟩ =
    .split (coordinate 10) (![⟨949344, by decide⟩,⟨949397, by decide⟩,⟨949442, by decide⟩,⟨949477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17979_949478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17979 ⟨949478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17979
    ⟨949478, by decide⟩ (by decide) (![⟨949344, by decide⟩,⟨949397, by decide⟩,⟨949442, by decide⟩,⟨949477, by decide⟩]) unmarked_context_10_17979_949478 node_context_10_17979_949478
  intro a
  fin_cases a
  · exact context_11_71916_949344
  · exact context_11_71917_949397
  · exact context_11_71918_949442
  · exact context_11_71919_949477

theorem unmarked_context_9_4494_949479 : frontier 12 ⟨949479, by decide⟩
    (prefixCache 9 4494) (prefixPartial 9 4494) = false := by
  decide +kernel

theorem node_context_9_4494_949479 : EJMOriginalGlobalDAGData.nodes 12 ⟨949479, by decide⟩ =
    .split (coordinate 9) (![⟨948871, by decide⟩,⟨949113, by decide⟩,⟨949288, by decide⟩,⟨949478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4494_949479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4494 ⟨949479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4494
    ⟨949479, by decide⟩ (by decide) (![⟨948871, by decide⟩,⟨949113, by decide⟩,⟨949288, by decide⟩,⟨949478, by decide⟩]) unmarked_context_9_4494_949479 node_context_9_4494_949479
  intro a
  fin_cases a
  · exact context_10_17976_948871
  · exact context_10_17977_949113
  · exact context_10_17978_949288
  · exact context_10_17979_949478

theorem selected_cut_36019 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71920) = some ⟨11, 1, 0, 907917, 71920, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71920_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71920 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71920 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71920, 1, 262144⟩
    (by decide) selected_cut_36019

theorem selected_cut_36020 : selected 10 ⟨949504, by decide⟩
    (prefixPartial 11 71921) = some ⟨11, 2, 0, 949504, 71921, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_71921_949504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71921 ⟨949504, by decide⟩ :=
  accepted_of_selected 11 71921 ⟨949504, by decide⟩ ⟨11, 2, 0, 949504, 71921, 2073, 262144⟩
    (by decide) selected_cut_36020

theorem selected_cut_36021 : selected 10 ⟨949533, by decide⟩
    (prefixPartial 11 71922) = some ⟨11, 2, 0, 949533, 71922, 2181, 262144⟩ := by
  decide +kernel

theorem context_11_71922_949533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71922 ⟨949533, by decide⟩ :=
  accepted_of_selected 11 71922 ⟨949533, by decide⟩ ⟨11, 2, 0, 949533, 71922, 2181, 262144⟩
    (by decide) selected_cut_36021

theorem selected_cut_36022 : selected 10 ⟨949558, by decide⟩
    (prefixPartial 11 71923) = some ⟨11, 2, 0, 949558, 71923, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_71923_949558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71923 ⟨949558, by decide⟩ :=
  accepted_of_selected 11 71923 ⟨949558, by decide⟩ ⟨11, 2, 0, 949558, 71923, 1537, 262144⟩
    (by decide) selected_cut_36022

theorem unmarked_context_10_17980_949559 : frontier 11 ⟨949559, by decide⟩
    (prefixCache 10 17980) (prefixPartial 10 17980) = false := by
  decide +kernel

theorem node_context_10_17980_949559 : EJMOriginalGlobalDAGData.nodes 11 ⟨949559, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨949504, by decide⟩,⟨949533, by decide⟩,⟨949558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17980_949559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17980 ⟨949559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17980
    ⟨949559, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨949504, by decide⟩,⟨949533, by decide⟩,⟨949558, by decide⟩]) unmarked_context_10_17980_949559 node_context_10_17980_949559
  intro a
  fin_cases a
  · exact context_11_71920_907917
  · exact context_11_71921_949504
  · exact context_11_71922_949533
  · exact context_11_71923_949558

theorem selected_cut_36023 : selected 10 ⟨949578, by decide⟩
    (prefixPartial 11 71924) = some ⟨11, 2, 0, 949578, 71924, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_71924_949578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71924 ⟨949578, by decide⟩ :=
  accepted_of_selected 11 71924 ⟨949578, by decide⟩ ⟨11, 2, 0, 949578, 71924, 1733, 262144⟩
    (by decide) selected_cut_36023

theorem selected_cut_36024 : selected 10 ⟨949596, by decide⟩
    (prefixPartial 11 71925) = some ⟨11, 2, 0, 949596, 71925, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_71925_949596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71925 ⟨949596, by decide⟩ :=
  accepted_of_selected 11 71925 ⟨949596, by decide⟩ ⟨11, 2, 0, 949596, 71925, 1541, 262144⟩
    (by decide) selected_cut_36024

theorem selected_cut_36025 : selected 10 ⟨949619, by decide⟩
    (prefixPartial 11 71926) = some ⟨11, 2, 0, 949619, 71926, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_71926_949619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71926 ⟨949619, by decide⟩ :=
  accepted_of_selected 11 71926 ⟨949619, by decide⟩ ⟨11, 2, 0, 949619, 71926, 1569, 262144⟩
    (by decide) selected_cut_36025

theorem selected_cut_36026 : selected 10 ⟨949639, by decide⟩
    (prefixPartial 11 71927) = some ⟨11, 2, 0, 949639, 71927, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_71927_949639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71927 ⟨949639, by decide⟩ :=
  accepted_of_selected 11 71927 ⟨949639, by decide⟩ ⟨11, 2, 0, 949639, 71927, 1057, 262144⟩
    (by decide) selected_cut_36026

theorem unmarked_context_10_17981_949640 : frontier 11 ⟨949640, by decide⟩
    (prefixCache 10 17981) (prefixPartial 10 17981) = false := by
  decide +kernel

theorem node_context_10_17981_949640 : EJMOriginalGlobalDAGData.nodes 11 ⟨949640, by decide⟩ =
    .split (coordinate 10) (![⟨949578, by decide⟩,⟨949596, by decide⟩,⟨949619, by decide⟩,⟨949639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17981_949640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17981 ⟨949640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17981
    ⟨949640, by decide⟩ (by decide) (![⟨949578, by decide⟩,⟨949596, by decide⟩,⟨949619, by decide⟩,⟨949639, by decide⟩]) unmarked_context_10_17981_949640 node_context_10_17981_949640
  intro a
  fin_cases a
  · exact context_11_71924_949578
  · exact context_11_71925_949596
  · exact context_11_71926_949619
  · exact context_11_71927_949639

theorem selected_cut_36027 : selected 11 ⟨949709, by decide⟩
    (prefixPartial 10 17982) = some ⟨10, 2, 0, 949709, 17982, 3713, 1048576⟩ := by
  decide +kernel

theorem context_10_17982_949709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17982 ⟨949709, by decide⟩ :=
  accepted_of_selected 10 17982 ⟨949709, by decide⟩ ⟨10, 2, 0, 949709, 17982, 3713, 1048576⟩
    (by decide) selected_cut_36027

theorem selected_cut_36028 : selected 11 ⟨949748, by decide⟩
    (prefixPartial 10 17983) = some ⟨10, 2, 0, 949748, 17983, 953, 1048576⟩ := by
  decide +kernel

theorem context_10_17983_949748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17983 ⟨949748, by decide⟩ :=
  accepted_of_selected 10 17983 ⟨949748, by decide⟩ ⟨10, 2, 0, 949748, 17983, 953, 1048576⟩
    (by decide) selected_cut_36028

theorem unmarked_context_9_4495_949749 : frontier 12 ⟨949749, by decide⟩
    (prefixCache 9 4495) (prefixPartial 9 4495) = false := by
  decide +kernel

theorem node_context_9_4495_949749 : EJMOriginalGlobalDAGData.nodes 12 ⟨949749, by decide⟩ =
    .split (coordinate 9) (![⟨949559, by decide⟩,⟨949640, by decide⟩,⟨949709, by decide⟩,⟨949748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4495_949749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4495 ⟨949749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4495
    ⟨949749, by decide⟩ (by decide) (![⟨949559, by decide⟩,⟨949640, by decide⟩,⟨949709, by decide⟩,⟨949748, by decide⟩]) unmarked_context_9_4495_949749 node_context_9_4495_949749
  intro a
  fin_cases a
  · exact context_10_17980_949559
  · exact context_10_17981_949640
  · exact context_10_17982_949709
  · exact context_10_17983_949748

theorem unmarked_context_8_1123_949750 : frontier 13 ⟨949750, by decide⟩
    (prefixCache 8 1123) (prefixPartial 8 1123) = false := by
  decide +kernel

theorem node_context_8_1123_949750 : EJMOriginalGlobalDAGData.nodes 13 ⟨949750, by decide⟩ =
    .split (coordinate 8) (![⟨947728, by decide⟩,⟨948622, by decide⟩,⟨949479, by decide⟩,⟨949749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1123_949750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1123 ⟨949750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1123
    ⟨949750, by decide⟩ (by decide) (![⟨947728, by decide⟩,⟨948622, by decide⟩,⟨949479, by decide⟩,⟨949749, by decide⟩]) unmarked_context_8_1123_949750 node_context_8_1123_949750
  intro a
  fin_cases a
  · exact context_9_4492_947728
  · exact context_9_4493_948622
  · exact context_9_4494_949479
  · exact context_9_4495_949749

theorem unmarked_context_7_280_949751 : frontier 14 ⟨949751, by decide⟩
    (prefixCache 7 280) (prefixPartial 7 280) = false := by
  decide +kernel

theorem node_context_7_280_949751 : EJMOriginalGlobalDAGData.nodes 14 ⟨949751, by decide⟩ =
    .split (coordinate 7) (![⟨934729, by decide⟩,⟨939549, by decide⟩,⟨944542, by decide⟩,⟨949750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_280_949751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 280 ⟨949751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 280
    ⟨949751, by decide⟩ (by decide) (![⟨934729, by decide⟩,⟨939549, by decide⟩,⟨944542, by decide⟩,⟨949750, by decide⟩]) unmarked_context_7_280_949751 node_context_7_280_949751
  intro a
  fin_cases a
  · exact context_8_1120_934729
  · exact context_8_1121_939549
  · exact context_8_1122_944542
  · exact context_8_1123_949750

theorem selected_cut_36029 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1124) = some ⟨8, 1, 0, 14300, 1124, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1124_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1124 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1124 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1124, 1, 16777216⟩
    (by decide) selected_cut_36029

theorem selected_cut_36030 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 288000) = some ⟨12, 1, 0, 34034, 288000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288000_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288000 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 288000 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 288000, 1, 65536⟩
    (by decide) selected_cut_36030

theorem selected_cut_36031 : selected 9 ⟨301653, by decide⟩
    (prefixPartial 12 288001) = some ⟨12, 1, 0, 301653, 288001, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288001_301653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288001 ⟨301653, by decide⟩ :=
  accepted_of_selected 12 288001 ⟨301653, by decide⟩ ⟨12, 1, 0, 301653, 288001, 1, 65536⟩
    (by decide) selected_cut_36031

theorem selected_cut_36032 : selected 9 ⟨949821, by decide⟩
    (prefixPartial 12 288002) = some ⟨12, 2, 0, 949821, 288002, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_288002_949821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288002 ⟨949821, by decide⟩ :=
  accepted_of_selected 12 288002 ⟨949821, by decide⟩ ⟨12, 2, 0, 949821, 288002, 2009, 65536⟩
    (by decide) selected_cut_36032

theorem selected_cut_36033 : selected 9 ⟨949918, by decide⟩
    (prefixPartial 12 288003) = some ⟨12, 2, 0, 949918, 288003, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_288003_949918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288003 ⟨949918, by decide⟩ :=
  accepted_of_selected 12 288003 ⟨949918, by decide⟩ ⟨12, 2, 0, 949918, 288003, 2265, 65536⟩
    (by decide) selected_cut_36033

theorem unmarked_context_11_72000_949919 : frontier 10 ⟨949919, by decide⟩
    (prefixCache 11 72000) (prefixPartial 11 72000) = false := by
  decide +kernel

theorem node_context_11_72000_949919 : EJMOriginalGlobalDAGData.nodes 10 ⟨949919, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨949821, by decide⟩,⟨949918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72000_949919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72000 ⟨949919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72000
    ⟨949919, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨301653, by decide⟩,⟨949821, by decide⟩,⟨949918, by decide⟩]) unmarked_context_11_72000_949919 node_context_11_72000_949919
  intro a
  fin_cases a
  · exact context_12_288000_34034
  · exact context_12_288001_301653
  · exact context_12_288002_949821
  · exact context_12_288003_949918

theorem selected_cut_36034 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 288004) = some ⟨12, 1, 0, 34034, 288004, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288004_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288004 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 288004 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 288004, 1, 65536⟩
    (by decide) selected_cut_36034

theorem selected_cut_36035 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 288005) = some ⟨12, 1, 0, 891951, 288005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288005_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288005 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 288005 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 288005, 1, 65536⟩
    (by decide) selected_cut_36035

theorem selected_cut_36036 : selected 9 ⟨949979, by decide⟩
    (prefixPartial 12 288006) = some ⟨12, 2, 0, 949979, 288006, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_288006_949979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288006 ⟨949979, by decide⟩ :=
  accepted_of_selected 12 288006 ⟨949979, by decide⟩ ⟨12, 2, 0, 949979, 288006, 3141, 65536⟩
    (by decide) selected_cut_36036

theorem selected_cut_36037 : selected 9 ⟨950036, by decide⟩
    (prefixPartial 12 288007) = some ⟨12, 2, 0, 950036, 288007, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_288007_950036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288007 ⟨950036, by decide⟩ :=
  accepted_of_selected 12 288007 ⟨950036, by decide⟩ ⟨12, 2, 0, 950036, 288007, 3225, 65536⟩
    (by decide) selected_cut_36037

theorem unmarked_context_11_72001_950037 : frontier 10 ⟨950037, by decide⟩
    (prefixCache 11 72001) (prefixPartial 11 72001) = false := by
  decide +kernel

theorem node_context_11_72001_950037 : EJMOriginalGlobalDAGData.nodes 10 ⟨950037, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨949979, by decide⟩,⟨950036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72001_950037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72001 ⟨950037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72001
    ⟨950037, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨949979, by decide⟩,⟨950036, by decide⟩]) unmarked_context_11_72001_950037 node_context_11_72001_950037
  intro a
  fin_cases a
  · exact context_12_288004_34034
  · exact context_12_288005_891951
  · exact context_12_288006_949979
  · exact context_12_288007_950036

theorem selected_cut_36038 : selected 9 ⟨950159, by decide⟩
    (prefixPartial 12 288008) = some ⟨12, 2, 0, 950159, 288008, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_288008_950159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288008 ⟨950159, by decide⟩ :=
  accepted_of_selected 12 288008 ⟨950159, by decide⟩ ⟨12, 2, 0, 950159, 288008, 3189, 65536⟩
    (by decide) selected_cut_36038

theorem selected_cut_36039 : selected 9 ⟨950221, by decide⟩
    (prefixPartial 12 288009) = some ⟨12, 2, 0, 950221, 288009, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_288009_950221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288009 ⟨950221, by decide⟩ :=
  accepted_of_selected 12 288009 ⟨950221, by decide⟩ ⟨12, 2, 0, 950221, 288009, 3129, 65536⟩
    (by decide) selected_cut_36039

theorem selected_cut_36040 : selected 9 ⟨950295, by decide⟩
    (prefixPartial 12 288010) = some ⟨12, 2, 0, 950295, 288010, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_288010_950295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288010 ⟨950295, by decide⟩ :=
  accepted_of_selected 12 288010 ⟨950295, by decide⟩ ⟨12, 2, 0, 950295, 288010, 3653, 65536⟩
    (by decide) selected_cut_36040

theorem selected_cut_36041 : selected 8 ⟨950338, by decide⟩
    (prefixPartial 13 1152044) = some ⟨13, 2, 0, 950338, 1152044, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_1152044_950338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1152044 ⟨950338, by decide⟩ :=
  accepted_of_selected 13 1152044 ⟨950338, by decide⟩ ⟨13, 2, 0, 950338, 1152044, 1433, 16384⟩
    (by decide) selected_cut_36041

theorem selected_cut_36042 : selected 8 ⟨950362, by decide⟩
    (prefixPartial 13 1152045) = some ⟨13, 2, 0, 950362, 1152045, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1152045_950362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1152045 ⟨950362, by decide⟩ :=
  accepted_of_selected 13 1152045 ⟨950362, by decide⟩ ⟨13, 2, 0, 950362, 1152045, 1101, 16384⟩
    (by decide) selected_cut_36042

theorem selected_cut_36043 : selected 8 ⟨950386, by decide⟩
    (prefixPartial 13 1152046) = some ⟨13, 2, 0, 950386, 1152046, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_1152046_950386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1152046 ⟨950386, by decide⟩ :=
  accepted_of_selected 13 1152046 ⟨950386, by decide⟩ ⟨13, 2, 0, 950386, 1152046, 1093, 16384⟩
    (by decide) selected_cut_36043

theorem selected_cut_36044 : selected 8 ⟨950395, by decide⟩
    (prefixPartial 13 1152047) = some ⟨13, 2, 0, 950395, 1152047, 661, 16384⟩ := by
  decide +kernel

theorem context_13_1152047_950395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1152047 ⟨950395, by decide⟩ :=
  accepted_of_selected 13 1152047 ⟨950395, by decide⟩ ⟨13, 2, 0, 950395, 1152047, 661, 16384⟩
    (by decide) selected_cut_36044

theorem unmarked_context_12_288011_950396 : frontier 9 ⟨950396, by decide⟩
    (prefixCache 12 288011) (prefixPartial 12 288011) = false := by
  decide +kernel

theorem node_context_12_288011_950396 : EJMOriginalGlobalDAGData.nodes 9 ⟨950396, by decide⟩ =
    .split (coordinate 12) (![⟨950338, by decide⟩,⟨950362, by decide⟩,⟨950386, by decide⟩,⟨950395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288011_950396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288011 ⟨950396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288011
    ⟨950396, by decide⟩ (by decide) (![⟨950338, by decide⟩,⟨950362, by decide⟩,⟨950386, by decide⟩,⟨950395, by decide⟩]) unmarked_context_12_288011_950396 node_context_12_288011_950396
  intro a
  fin_cases a
  · exact context_13_1152044_950338
  · exact context_13_1152045_950362
  · exact context_13_1152046_950386
  · exact context_13_1152047_950395

theorem unmarked_context_11_72002_950397 : frontier 10 ⟨950397, by decide⟩
    (prefixCache 11 72002) (prefixPartial 11 72002) = false := by
  decide +kernel

theorem node_context_11_72002_950397 : EJMOriginalGlobalDAGData.nodes 10 ⟨950397, by decide⟩ =
    .split (coordinate 11) (![⟨950159, by decide⟩,⟨950221, by decide⟩,⟨950295, by decide⟩,⟨950396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72002_950397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72002 ⟨950397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72002
    ⟨950397, by decide⟩ (by decide) (![⟨950159, by decide⟩,⟨950221, by decide⟩,⟨950295, by decide⟩,⟨950396, by decide⟩]) unmarked_context_11_72002_950397 node_context_11_72002_950397
  intro a
  fin_cases a
  · exact context_12_288008_950159
  · exact context_12_288009_950221
  · exact context_12_288010_950295
  · exact context_12_288011_950396

theorem selected_cut_36045 : selected 9 ⟨950464, by decide⟩
    (prefixPartial 12 288012) = some ⟨12, 2, 0, 950464, 288012, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_288012_950464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288012 ⟨950464, by decide⟩ :=
  accepted_of_selected 12 288012 ⟨950464, by decide⟩ ⟨12, 2, 0, 950464, 288012, 1461, 65536⟩
    (by decide) selected_cut_36045

theorem selected_cut_36046 : selected 9 ⟨950519, by decide⟩
    (prefixPartial 12 288013) = some ⟨12, 2, 0, 950519, 288013, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_288013_950519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288013 ⟨950519, by decide⟩ :=
  accepted_of_selected 12 288013 ⟨950519, by decide⟩ ⟨12, 2, 0, 950519, 288013, 2849, 65536⟩
    (by decide) selected_cut_36046

theorem selected_cut_36047 : selected 9 ⟨950594, by decide⟩
    (prefixPartial 12 288014) = some ⟨12, 2, 0, 950594, 288014, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_288014_950594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288014 ⟨950594, by decide⟩ :=
  accepted_of_selected 12 288014 ⟨950594, by decide⟩ ⟨12, 2, 0, 950594, 288014, 3493, 65536⟩
    (by decide) selected_cut_36047

theorem selected_cut_36048 : selected 9 ⟨950680, by decide⟩
    (prefixPartial 12 288015) = some ⟨12, 2, 0, 950680, 288015, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_288015_950680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288015 ⟨950680, by decide⟩ :=
  accepted_of_selected 12 288015 ⟨950680, by decide⟩ ⟨12, 2, 0, 950680, 288015, 3701, 65536⟩
    (by decide) selected_cut_36048

theorem unmarked_context_11_72003_950681 : frontier 10 ⟨950681, by decide⟩
    (prefixCache 11 72003) (prefixPartial 11 72003) = false := by
  decide +kernel

theorem node_context_11_72003_950681 : EJMOriginalGlobalDAGData.nodes 10 ⟨950681, by decide⟩ =
    .split (coordinate 11) (![⟨950464, by decide⟩,⟨950519, by decide⟩,⟨950594, by decide⟩,⟨950680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72003_950681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72003 ⟨950681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72003
    ⟨950681, by decide⟩ (by decide) (![⟨950464, by decide⟩,⟨950519, by decide⟩,⟨950594, by decide⟩,⟨950680, by decide⟩]) unmarked_context_11_72003_950681 node_context_11_72003_950681
  intro a
  fin_cases a
  · exact context_12_288012_950464
  · exact context_12_288013_950519
  · exact context_12_288014_950594
  · exact context_12_288015_950680

theorem unmarked_context_10_18000_950682 : frontier 11 ⟨950682, by decide⟩
    (prefixCache 10 18000) (prefixPartial 10 18000) = false := by
  decide +kernel

theorem node_context_10_18000_950682 : EJMOriginalGlobalDAGData.nodes 11 ⟨950682, by decide⟩ =
    .split (coordinate 10) (![⟨949919, by decide⟩,⟨950037, by decide⟩,⟨950397, by decide⟩,⟨950681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18000_950682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18000 ⟨950682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18000
    ⟨950682, by decide⟩ (by decide) (![⟨949919, by decide⟩,⟨950037, by decide⟩,⟨950397, by decide⟩,⟨950681, by decide⟩]) unmarked_context_10_18000_950682 node_context_10_18000_950682
  intro a
  fin_cases a
  · exact context_11_72000_949919
  · exact context_11_72001_950037
  · exact context_11_72002_950397
  · exact context_11_72003_950681

theorem selected_cut_36049 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288016) = some ⟨12, 1, 0, 1738, 288016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288016_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288016 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288016 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288016, 1, 65536⟩
    (by decide) selected_cut_36049

theorem selected_cut_36050 : selected 9 ⟨950743, by decide⟩
    (prefixPartial 12 288017) = some ⟨12, 2, 0, 950743, 288017, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_288017_950743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288017 ⟨950743, by decide⟩ :=
  accepted_of_selected 12 288017 ⟨950743, by decide⟩ ⟨12, 2, 0, 950743, 288017, 1501, 65536⟩
    (by decide) selected_cut_36050

theorem selected_cut_36051 : selected 9 ⟨950792, by decide⟩
    (prefixPartial 12 288018) = some ⟨12, 2, 0, 950792, 288018, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_288018_950792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288018 ⟨950792, by decide⟩ :=
  accepted_of_selected 12 288018 ⟨950792, by decide⟩ ⟨12, 2, 0, 950792, 288018, 2577, 65536⟩
    (by decide) selected_cut_36051

theorem selected_cut_36052 : selected 9 ⟨950841, by decide⟩
    (prefixPartial 12 288019) = some ⟨12, 2, 0, 950841, 288019, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_288019_950841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288019 ⟨950841, by decide⟩ :=
  accepted_of_selected 12 288019 ⟨950841, by decide⟩ ⟨12, 2, 0, 950841, 288019, 2725, 65536⟩
    (by decide) selected_cut_36052

theorem unmarked_context_11_72004_950842 : frontier 10 ⟨950842, by decide⟩
    (prefixCache 11 72004) (prefixPartial 11 72004) = false := by
  decide +kernel

theorem node_context_11_72004_950842 : EJMOriginalGlobalDAGData.nodes 10 ⟨950842, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨950743, by decide⟩,⟨950792, by decide⟩,⟨950841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72004_950842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72004 ⟨950842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72004
    ⟨950842, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨950743, by decide⟩,⟨950792, by decide⟩,⟨950841, by decide⟩]) unmarked_context_11_72004_950842 node_context_11_72004_950842
  intro a
  fin_cases a
  · exact context_12_288016_1738
  · exact context_12_288017_950743
  · exact context_12_288018_950792
  · exact context_12_288019_950841

theorem selected_cut_36053 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72005) = some ⟨11, 1, 0, 892405, 72005, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72005_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72005 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72005 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72005, 1, 262144⟩
    (by decide) selected_cut_36053

theorem selected_cut_36054 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288024) = some ⟨12, 1, 0, 1738, 288024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288024_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288024 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288024 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288024, 1, 65536⟩
    (by decide) selected_cut_36054

theorem selected_cut_36055 : selected 9 ⟨950878, by decide⟩
    (prefixPartial 12 288025) = some ⟨12, 2, 0, 950878, 288025, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_288025_950878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288025 ⟨950878, by decide⟩ :=
  accepted_of_selected 12 288025 ⟨950878, by decide⟩ ⟨12, 2, 0, 950878, 288025, 1509, 65536⟩
    (by decide) selected_cut_36055

theorem selected_cut_36056 : selected 9 ⟨950926, by decide⟩
    (prefixPartial 12 288026) = some ⟨12, 2, 0, 950926, 288026, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_288026_950926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288026 ⟨950926, by decide⟩ :=
  accepted_of_selected 12 288026 ⟨950926, by decide⟩ ⟨12, 2, 0, 950926, 288026, 2541, 65536⟩
    (by decide) selected_cut_36056

theorem selected_cut_36057 : selected 9 ⟨950987, by decide⟩
    (prefixPartial 12 288027) = some ⟨12, 2, 0, 950987, 288027, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_288027_950987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288027 ⟨950987, by decide⟩ :=
  accepted_of_selected 12 288027 ⟨950987, by decide⟩ ⟨12, 2, 0, 950987, 288027, 2837, 65536⟩
    (by decide) selected_cut_36057

theorem unmarked_context_11_72006_950988 : frontier 10 ⟨950988, by decide⟩
    (prefixCache 11 72006) (prefixPartial 11 72006) = false := by
  decide +kernel

theorem node_context_11_72006_950988 : EJMOriginalGlobalDAGData.nodes 10 ⟨950988, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨950878, by decide⟩,⟨950926, by decide⟩,⟨950987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72006_950988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72006 ⟨950988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72006
    ⟨950988, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨950878, by decide⟩,⟨950926, by decide⟩,⟨950987, by decide⟩]) unmarked_context_11_72006_950988 node_context_11_72006_950988
  intro a
  fin_cases a
  · exact context_12_288024_1738
  · exact context_12_288025_950878
  · exact context_12_288026_950926
  · exact context_12_288027_950987

theorem selected_cut_36058 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288028) = some ⟨12, 1, 0, 1738, 288028, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288028_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288028 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288028 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288028, 1, 65536⟩
    (by decide) selected_cut_36058

theorem selected_cut_36059 : selected 9 ⟨951017, by decide⟩
    (prefixPartial 12 288029) = some ⟨12, 2, 0, 951017, 288029, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_288029_951017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288029 ⟨951017, by decide⟩ :=
  accepted_of_selected 12 288029 ⟨951017, by decide⟩ ⟨12, 2, 0, 951017, 288029, 1441, 65536⟩
    (by decide) selected_cut_36059

theorem selected_cut_36060 : selected 9 ⟨951067, by decide⟩
    (prefixPartial 12 288030) = some ⟨12, 2, 0, 951067, 288030, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_288030_951067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288030 ⟨951067, by decide⟩ :=
  accepted_of_selected 12 288030 ⟨951067, by decide⟩ ⟨12, 2, 0, 951067, 288030, 2521, 65536⟩
    (by decide) selected_cut_36060

theorem selected_cut_36061 : selected 9 ⟨951122, by decide⟩
    (prefixPartial 12 288031) = some ⟨12, 2, 0, 951122, 288031, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_288031_951122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288031 ⟨951122, by decide⟩ :=
  accepted_of_selected 12 288031 ⟨951122, by decide⟩ ⟨12, 2, 0, 951122, 288031, 2645, 65536⟩
    (by decide) selected_cut_36061

theorem unmarked_context_11_72007_951123 : frontier 10 ⟨951123, by decide⟩
    (prefixCache 11 72007) (prefixPartial 11 72007) = false := by
  decide +kernel

theorem node_context_11_72007_951123 : EJMOriginalGlobalDAGData.nodes 10 ⟨951123, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨951017, by decide⟩,⟨951067, by decide⟩,⟨951122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72007_951123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72007 ⟨951123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72007
    ⟨951123, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨951017, by decide⟩,⟨951067, by decide⟩,⟨951122, by decide⟩]) unmarked_context_11_72007_951123 node_context_11_72007_951123
  intro a
  fin_cases a
  · exact context_12_288028_1738
  · exact context_12_288029_951017
  · exact context_12_288030_951067
  · exact context_12_288031_951122

theorem unmarked_context_10_18001_951124 : frontier 11 ⟨951124, by decide⟩
    (prefixCache 10 18001) (prefixPartial 10 18001) = false := by
  decide +kernel

theorem node_context_10_18001_951124 : EJMOriginalGlobalDAGData.nodes 11 ⟨951124, by decide⟩ =
    .split (coordinate 10) (![⟨950842, by decide⟩,⟨892405, by decide⟩,⟨950988, by decide⟩,⟨951123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18001_951124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18001 ⟨951124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18001
    ⟨951124, by decide⟩ (by decide) (![⟨950842, by decide⟩,⟨892405, by decide⟩,⟨950988, by decide⟩,⟨951123, by decide⟩]) unmarked_context_10_18001_951124 node_context_10_18001_951124
  intro a
  fin_cases a
  · exact context_11_72004_950842
  · exact context_11_72005_892405
  · exact context_11_72006_950988
  · exact context_11_72007_951123

theorem selected_cut_36062 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288032) = some ⟨12, 1, 0, 1738, 288032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288032_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288032 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288032 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288032, 1, 65536⟩
    (by decide) selected_cut_36062

theorem selected_cut_36063 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288033) = some ⟨12, 1, 0, 1738, 288033, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288033_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288033 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288033 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288033, 1, 65536⟩
    (by decide) selected_cut_36063

theorem selected_cut_36064 : selected 9 ⟨951204, by decide⟩
    (prefixPartial 12 288034) = some ⟨12, 2, 0, 951204, 288034, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_288034_951204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288034 ⟨951204, by decide⟩ :=
  accepted_of_selected 12 288034 ⟨951204, by decide⟩ ⟨12, 2, 0, 951204, 288034, 2273, 65536⟩
    (by decide) selected_cut_36064

theorem selected_cut_36065 : selected 9 ⟨951290, by decide⟩
    (prefixPartial 12 288035) = some ⟨12, 2, 0, 951290, 288035, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_288035_951290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288035 ⟨951290, by decide⟩ :=
  accepted_of_selected 12 288035 ⟨951290, by decide⟩ ⟨12, 2, 0, 951290, 288035, 3265, 65536⟩
    (by decide) selected_cut_36065

theorem unmarked_context_11_72008_951291 : frontier 10 ⟨951291, by decide⟩
    (prefixCache 11 72008) (prefixPartial 11 72008) = false := by
  decide +kernel

theorem node_context_11_72008_951291 : EJMOriginalGlobalDAGData.nodes 10 ⟨951291, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951204, by decide⟩,⟨951290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72008_951291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72008 ⟨951291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72008
    ⟨951291, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951204, by decide⟩,⟨951290, by decide⟩]) unmarked_context_11_72008_951291 node_context_11_72008_951291
  intro a
  fin_cases a
  · exact context_12_288032_1738
  · exact context_12_288033_1738
  · exact context_12_288034_951204
  · exact context_12_288035_951290

theorem selected_cut_36066 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288036) = some ⟨12, 1, 0, 1738, 288036, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288036_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288036 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288036 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288036, 1, 65536⟩
    (by decide) selected_cut_36066

theorem selected_cut_36067 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288037) = some ⟨12, 1, 0, 1738, 288037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288037_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288037 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288037 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288037, 1, 65536⟩
    (by decide) selected_cut_36067

theorem selected_cut_36068 : selected 9 ⟨951343, by decide⟩
    (prefixPartial 12 288038) = some ⟨12, 2, 0, 951343, 288038, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_288038_951343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288038 ⟨951343, by decide⟩ :=
  accepted_of_selected 12 288038 ⟨951343, by decide⟩ ⟨12, 2, 0, 951343, 288038, 1893, 65536⟩
    (by decide) selected_cut_36068

theorem selected_cut_36069 : selected 9 ⟨951399, by decide⟩
    (prefixPartial 12 288039) = some ⟨12, 2, 0, 951399, 288039, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_288039_951399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288039 ⟨951399, by decide⟩ :=
  accepted_of_selected 12 288039 ⟨951399, by decide⟩ ⟨12, 2, 0, 951399, 288039, 2697, 65536⟩
    (by decide) selected_cut_36069

theorem unmarked_context_11_72009_951400 : frontier 10 ⟨951400, by decide⟩
    (prefixCache 11 72009) (prefixPartial 11 72009) = false := by
  decide +kernel

theorem node_context_11_72009_951400 : EJMOriginalGlobalDAGData.nodes 10 ⟨951400, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951343, by decide⟩,⟨951399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72009_951400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72009 ⟨951400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72009
    ⟨951400, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951343, by decide⟩,⟨951399, by decide⟩]) unmarked_context_11_72009_951400 node_context_11_72009_951400
  intro a
  fin_cases a
  · exact context_12_288036_1738
  · exact context_12_288037_1738
  · exact context_12_288038_951343
  · exact context_12_288039_951399

theorem selected_cut_36070 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288040) = some ⟨12, 1, 0, 1738, 288040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288040_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288040 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288040 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288040, 1, 65536⟩
    (by decide) selected_cut_36070

theorem selected_cut_36071 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288041) = some ⟨12, 1, 0, 1738, 288041, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288041_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288041 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288041 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288041, 1, 65536⟩
    (by decide) selected_cut_36071

theorem selected_cut_36072 : selected 9 ⟨951508, by decide⟩
    (prefixPartial 12 288042) = some ⟨12, 2, 0, 951508, 288042, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_288042_951508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288042 ⟨951508, by decide⟩ :=
  accepted_of_selected 12 288042 ⟨951508, by decide⟩ ⟨12, 2, 0, 951508, 288042, 1189, 65536⟩
    (by decide) selected_cut_36072

theorem selected_cut_36073 : selected 9 ⟨951590, by decide⟩
    (prefixPartial 12 288043) = some ⟨12, 2, 0, 951590, 288043, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_288043_951590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288043 ⟨951590, by decide⟩ :=
  accepted_of_selected 12 288043 ⟨951590, by decide⟩ ⟨12, 2, 0, 951590, 288043, 3085, 65536⟩
    (by decide) selected_cut_36073

theorem unmarked_context_11_72010_951591 : frontier 10 ⟨951591, by decide⟩
    (prefixCache 11 72010) (prefixPartial 11 72010) = false := by
  decide +kernel

theorem node_context_11_72010_951591 : EJMOriginalGlobalDAGData.nodes 10 ⟨951591, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951508, by decide⟩,⟨951590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72010_951591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72010 ⟨951591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72010
    ⟨951591, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951508, by decide⟩,⟨951590, by decide⟩]) unmarked_context_11_72010_951591 node_context_11_72010_951591
  intro a
  fin_cases a
  · exact context_12_288040_1738
  · exact context_12_288041_1738
  · exact context_12_288042_951508
  · exact context_12_288043_951590

theorem selected_cut_36074 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288044) = some ⟨12, 1, 0, 1738, 288044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288044_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288044 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288044 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288044, 1, 65536⟩
    (by decide) selected_cut_36074

theorem selected_cut_36075 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 288045) = some ⟨12, 1, 0, 1738, 288045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288045_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288045 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 288045 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 288045, 1, 65536⟩
    (by decide) selected_cut_36075

theorem selected_cut_36076 : selected 9 ⟨951665, by decide⟩
    (prefixPartial 12 288046) = some ⟨12, 2, 0, 951665, 288046, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_288046_951665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288046 ⟨951665, by decide⟩ :=
  accepted_of_selected 12 288046 ⟨951665, by decide⟩ ⟨12, 2, 0, 951665, 288046, 2217, 65536⟩
    (by decide) selected_cut_36076

theorem selected_cut_36077 : selected 9 ⟨951738, by decide⟩
    (prefixPartial 12 288047) = some ⟨12, 2, 0, 951738, 288047, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_288047_951738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288047 ⟨951738, by decide⟩ :=
  accepted_of_selected 12 288047 ⟨951738, by decide⟩ ⟨12, 2, 0, 951738, 288047, 3005, 65536⟩
    (by decide) selected_cut_36077

theorem unmarked_context_11_72011_951739 : frontier 10 ⟨951739, by decide⟩
    (prefixCache 11 72011) (prefixPartial 11 72011) = false := by
  decide +kernel

theorem node_context_11_72011_951739 : EJMOriginalGlobalDAGData.nodes 10 ⟨951739, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951665, by decide⟩,⟨951738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72011_951739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72011 ⟨951739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72011
    ⟨951739, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨951665, by decide⟩,⟨951738, by decide⟩]) unmarked_context_11_72011_951739 node_context_11_72011_951739
  intro a
  fin_cases a
  · exact context_12_288044_1738
  · exact context_12_288045_1738
  · exact context_12_288046_951665
  · exact context_12_288047_951738

theorem unmarked_context_10_18002_951740 : frontier 11 ⟨951740, by decide⟩
    (prefixCache 10 18002) (prefixPartial 10 18002) = false := by
  decide +kernel

theorem node_context_10_18002_951740 : EJMOriginalGlobalDAGData.nodes 11 ⟨951740, by decide⟩ =
    .split (coordinate 10) (![⟨951291, by decide⟩,⟨951400, by decide⟩,⟨951591, by decide⟩,⟨951739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18002_951740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18002 ⟨951740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18002
    ⟨951740, by decide⟩ (by decide) (![⟨951291, by decide⟩,⟨951400, by decide⟩,⟨951591, by decide⟩,⟨951739, by decide⟩]) unmarked_context_10_18002_951740 node_context_10_18002_951740
  intro a
  fin_cases a
  · exact context_11_72008_951291
  · exact context_11_72009_951400
  · exact context_11_72010_951591
  · exact context_11_72011_951739

theorem selected_cut_36078 : selected 10 ⟨951833, by decide⟩
    (prefixPartial 11 72012) = some ⟨11, 2, 0, 951833, 72012, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_72012_951833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72012 ⟨951833, by decide⟩ :=
  accepted_of_selected 11 72012 ⟨951833, by decide⟩ ⟨11, 2, 0, 951833, 72012, 2393, 262144⟩
    (by decide) selected_cut_36078

theorem selected_cut_36079 : selected 10 ⟨951890, by decide⟩
    (prefixPartial 11 72013) = some ⟨11, 2, 0, 951890, 72013, 1817, 262144⟩ := by
  decide +kernel

theorem context_11_72013_951890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72013 ⟨951890, by decide⟩ :=
  accepted_of_selected 11 72013 ⟨951890, by decide⟩ ⟨11, 2, 0, 951890, 72013, 1817, 262144⟩
    (by decide) selected_cut_36079

theorem selected_cut_36080 : selected 10 ⟨951978, by decide⟩
    (prefixPartial 11 72014) = some ⟨11, 2, 0, 951978, 72014, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_72014_951978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72014 ⟨951978, by decide⟩ :=
  accepted_of_selected 11 72014 ⟨951978, by decide⟩ ⟨11, 2, 0, 951978, 72014, 2265, 262144⟩
    (by decide) selected_cut_36080

theorem selected_cut_36081 : selected 10 ⟨952127, by decide⟩
    (prefixPartial 11 72015) = some ⟨11, 2, 0, 952127, 72015, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_72015_952127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72015 ⟨952127, by decide⟩ :=
  accepted_of_selected 11 72015 ⟨952127, by decide⟩ ⟨11, 2, 0, 952127, 72015, 1521, 262144⟩
    (by decide) selected_cut_36081

theorem unmarked_context_10_18003_952128 : frontier 11 ⟨952128, by decide⟩
    (prefixCache 10 18003) (prefixPartial 10 18003) = false := by
  decide +kernel

theorem node_context_10_18003_952128 : EJMOriginalGlobalDAGData.nodes 11 ⟨952128, by decide⟩ =
    .split (coordinate 10) (![⟨951833, by decide⟩,⟨951890, by decide⟩,⟨951978, by decide⟩,⟨952127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18003_952128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18003 ⟨952128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18003
    ⟨952128, by decide⟩ (by decide) (![⟨951833, by decide⟩,⟨951890, by decide⟩,⟨951978, by decide⟩,⟨952127, by decide⟩]) unmarked_context_10_18003_952128 node_context_10_18003_952128
  intro a
  fin_cases a
  · exact context_11_72012_951833
  · exact context_11_72013_951890
  · exact context_11_72014_951978
  · exact context_11_72015_952127

theorem unmarked_context_9_4500_952129 : frontier 12 ⟨952129, by decide⟩
    (prefixCache 9 4500) (prefixPartial 9 4500) = false := by
  decide +kernel

theorem node_context_9_4500_952129 : EJMOriginalGlobalDAGData.nodes 12 ⟨952129, by decide⟩ =
    .split (coordinate 9) (![⟨950682, by decide⟩,⟨951124, by decide⟩,⟨951740, by decide⟩,⟨952128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4500_952129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4500 ⟨952129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4500
    ⟨952129, by decide⟩ (by decide) (![⟨950682, by decide⟩,⟨951124, by decide⟩,⟨951740, by decide⟩,⟨952128, by decide⟩]) unmarked_context_9_4500_952129 node_context_9_4500_952129
  intro a
  fin_cases a
  · exact context_10_18000_950682
  · exact context_10_18001_951124
  · exact context_10_18002_951740
  · exact context_10_18003_952128

theorem selected_cut_36082 : selected 9 ⟨277904, by decide⟩
    (prefixPartial 12 288064) = some ⟨12, 1, 0, 277904, 288064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288064_277904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288064 ⟨277904, by decide⟩ :=
  accepted_of_selected 12 288064 ⟨277904, by decide⟩ ⟨12, 1, 0, 277904, 288064, 1, 65536⟩
    (by decide) selected_cut_36082

theorem selected_cut_36083 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288065) = some ⟨12, 1, 0, 896706, 288065, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288065_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288065 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288065 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288065, 1, 65536⟩
    (by decide) selected_cut_36083

theorem selected_cut_36084 : selected 9 ⟨952199, by decide⟩
    (prefixPartial 12 288066) = some ⟨12, 2, 0, 952199, 288066, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_288066_952199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288066 ⟨952199, by decide⟩ :=
  accepted_of_selected 12 288066 ⟨952199, by decide⟩ ⟨12, 2, 0, 952199, 288066, 2437, 65536⟩
    (by decide) selected_cut_36084

theorem selected_cut_36085 : selected 9 ⟨952267, by decide⟩
    (prefixPartial 12 288067) = some ⟨12, 2, 0, 952267, 288067, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_288067_952267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288067 ⟨952267, by decide⟩ :=
  accepted_of_selected 12 288067 ⟨952267, by decide⟩ ⟨12, 2, 0, 952267, 288067, 2621, 65536⟩
    (by decide) selected_cut_36085

theorem unmarked_context_11_72016_952268 : frontier 10 ⟨952268, by decide⟩
    (prefixCache 11 72016) (prefixPartial 11 72016) = false := by
  decide +kernel

theorem node_context_11_72016_952268 : EJMOriginalGlobalDAGData.nodes 10 ⟨952268, by decide⟩ =
    .split (coordinate 11) (![⟨277904, by decide⟩,⟨896706, by decide⟩,⟨952199, by decide⟩,⟨952267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72016_952268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72016 ⟨952268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72016
    ⟨952268, by decide⟩ (by decide) (![⟨277904, by decide⟩,⟨896706, by decide⟩,⟨952199, by decide⟩,⟨952267, by decide⟩]) unmarked_context_11_72016_952268 node_context_11_72016_952268
  intro a
  fin_cases a
  · exact context_12_288064_277904
  · exact context_12_288065_896706
  · exact context_12_288066_952199
  · exact context_12_288067_952267

theorem selected_cut_36086 : selected 9 ⟨952332, by decide⟩
    (prefixPartial 12 288068) = some ⟨12, 2, 0, 952332, 288068, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_288068_952332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288068 ⟨952332, by decide⟩ :=
  accepted_of_selected 12 288068 ⟨952332, by decide⟩ ⟨12, 2, 0, 952332, 288068, 1713, 65536⟩
    (by decide) selected_cut_36086

theorem selected_cut_36087 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288069) = some ⟨12, 1, 0, 896706, 288069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288069_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288069 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288069 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288069, 1, 65536⟩
    (by decide) selected_cut_36087

theorem selected_cut_36088 : selected 9 ⟨952372, by decide⟩
    (prefixPartial 12 288070) = some ⟨12, 2, 0, 952372, 288070, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_288070_952372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288070 ⟨952372, by decide⟩ :=
  accepted_of_selected 12 288070 ⟨952372, by decide⟩ ⟨12, 2, 0, 952372, 288070, 1873, 65536⟩
    (by decide) selected_cut_36088

theorem selected_cut_36089 : selected 9 ⟨952413, by decide⟩
    (prefixPartial 12 288071) = some ⟨12, 2, 0, 952413, 288071, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_288071_952413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288071 ⟨952413, by decide⟩ :=
  accepted_of_selected 12 288071 ⟨952413, by decide⟩ ⟨12, 2, 0, 952413, 288071, 1789, 65536⟩
    (by decide) selected_cut_36089

theorem unmarked_context_11_72017_952414 : frontier 10 ⟨952414, by decide⟩
    (prefixCache 11 72017) (prefixPartial 11 72017) = false := by
  decide +kernel

theorem node_context_11_72017_952414 : EJMOriginalGlobalDAGData.nodes 10 ⟨952414, by decide⟩ =
    .split (coordinate 11) (![⟨952332, by decide⟩,⟨896706, by decide⟩,⟨952372, by decide⟩,⟨952413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72017_952414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72017 ⟨952414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72017
    ⟨952414, by decide⟩ (by decide) (![⟨952332, by decide⟩,⟨896706, by decide⟩,⟨952372, by decide⟩,⟨952413, by decide⟩]) unmarked_context_11_72017_952414 node_context_11_72017_952414
  intro a
  fin_cases a
  · exact context_12_288068_952332
  · exact context_12_288069_896706
  · exact context_12_288070_952372
  · exact context_12_288071_952413

theorem selected_cut_36090 : selected 9 ⟨952503, by decide⟩
    (prefixPartial 12 288072) = some ⟨12, 2, 0, 952503, 288072, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_288072_952503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288072 ⟨952503, by decide⟩ :=
  accepted_of_selected 12 288072 ⟨952503, by decide⟩ ⟨12, 2, 0, 952503, 288072, 2237, 65536⟩
    (by decide) selected_cut_36090

theorem selected_cut_36091 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288073) = some ⟨12, 1, 0, 896706, 288073, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288073_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288073 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288073 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288073, 1, 65536⟩
    (by decide) selected_cut_36091

theorem selected_cut_36092 : selected 9 ⟨952569, by decide⟩
    (prefixPartial 12 288074) = some ⟨12, 2, 0, 952569, 288074, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_288074_952569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288074 ⟨952569, by decide⟩ :=
  accepted_of_selected 12 288074 ⟨952569, by decide⟩ ⟨12, 2, 0, 952569, 288074, 2253, 65536⟩
    (by decide) selected_cut_36092

theorem selected_cut_36093 : selected 9 ⟨952631, by decide⟩
    (prefixPartial 12 288075) = some ⟨12, 2, 0, 952631, 288075, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_288075_952631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288075 ⟨952631, by decide⟩ :=
  accepted_of_selected 12 288075 ⟨952631, by decide⟩ ⟨12, 2, 0, 952631, 288075, 2481, 65536⟩
    (by decide) selected_cut_36093

theorem unmarked_context_11_72018_952632 : frontier 10 ⟨952632, by decide⟩
    (prefixCache 11 72018) (prefixPartial 11 72018) = false := by
  decide +kernel

theorem node_context_11_72018_952632 : EJMOriginalGlobalDAGData.nodes 10 ⟨952632, by decide⟩ =
    .split (coordinate 11) (![⟨952503, by decide⟩,⟨896706, by decide⟩,⟨952569, by decide⟩,⟨952631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72018_952632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72018 ⟨952632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72018
    ⟨952632, by decide⟩ (by decide) (![⟨952503, by decide⟩,⟨896706, by decide⟩,⟨952569, by decide⟩,⟨952631, by decide⟩]) unmarked_context_11_72018_952632 node_context_11_72018_952632
  intro a
  fin_cases a
  · exact context_12_288072_952503
  · exact context_12_288073_896706
  · exact context_12_288074_952569
  · exact context_12_288075_952631

theorem selected_cut_36094 : selected 9 ⟨952685, by decide⟩
    (prefixPartial 12 288076) = some ⟨12, 2, 0, 952685, 288076, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_288076_952685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288076 ⟨952685, by decide⟩ :=
  accepted_of_selected 12 288076 ⟨952685, by decide⟩ ⟨12, 2, 0, 952685, 288076, 1785, 65536⟩
    (by decide) selected_cut_36094

theorem selected_cut_36095 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288077) = some ⟨12, 1, 0, 896706, 288077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288077_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288077 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288077 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288077, 1, 65536⟩
    (by decide) selected_cut_36095

theorem selected_cut_36096 : selected 9 ⟨952730, by decide⟩
    (prefixPartial 12 288078) = some ⟨12, 2, 0, 952730, 288078, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_288078_952730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288078 ⟨952730, by decide⟩ :=
  accepted_of_selected 12 288078 ⟨952730, by decide⟩ ⟨12, 2, 0, 952730, 288078, 2085, 65536⟩
    (by decide) selected_cut_36096

theorem selected_cut_36097 : selected 9 ⟨952779, by decide⟩
    (prefixPartial 12 288079) = some ⟨12, 2, 0, 952779, 288079, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_288079_952779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288079 ⟨952779, by decide⟩ :=
  accepted_of_selected 12 288079 ⟨952779, by decide⟩ ⟨12, 2, 0, 952779, 288079, 1965, 65536⟩
    (by decide) selected_cut_36097

theorem unmarked_context_11_72019_952780 : frontier 10 ⟨952780, by decide⟩
    (prefixCache 11 72019) (prefixPartial 11 72019) = false := by
  decide +kernel

theorem node_context_11_72019_952780 : EJMOriginalGlobalDAGData.nodes 10 ⟨952780, by decide⟩ =
    .split (coordinate 11) (![⟨952685, by decide⟩,⟨896706, by decide⟩,⟨952730, by decide⟩,⟨952779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72019_952780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72019 ⟨952780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72019
    ⟨952780, by decide⟩ (by decide) (![⟨952685, by decide⟩,⟨896706, by decide⟩,⟨952730, by decide⟩,⟨952779, by decide⟩]) unmarked_context_11_72019_952780 node_context_11_72019_952780
  intro a
  fin_cases a
  · exact context_12_288076_952685
  · exact context_12_288077_896706
  · exact context_12_288078_952730
  · exact context_12_288079_952779

theorem unmarked_context_10_18004_952781 : frontier 11 ⟨952781, by decide⟩
    (prefixCache 10 18004) (prefixPartial 10 18004) = false := by
  decide +kernel

theorem node_context_10_18004_952781 : EJMOriginalGlobalDAGData.nodes 11 ⟨952781, by decide⟩ =
    .split (coordinate 10) (![⟨952268, by decide⟩,⟨952414, by decide⟩,⟨952632, by decide⟩,⟨952780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18004_952781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18004 ⟨952781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18004
    ⟨952781, by decide⟩ (by decide) (![⟨952268, by decide⟩,⟨952414, by decide⟩,⟨952632, by decide⟩,⟨952780, by decide⟩]) unmarked_context_10_18004_952781 node_context_10_18004_952781
  intro a
  fin_cases a
  · exact context_11_72016_952268
  · exact context_11_72017_952414
  · exact context_11_72018_952632
  · exact context_11_72019_952780

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
