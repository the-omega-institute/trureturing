import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows00
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows01
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows02
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows03
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows04
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows05
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows06
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows07
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows08
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows09
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows10
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows11
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows12
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows13
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows14
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows15
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows16
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows17
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows18
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows19
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows20
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows21
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows22
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows23
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows24
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows25
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows26
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows27
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows28
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows29
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows30
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows31

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

private def node4_0 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows00.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows16.table

private theorem node4_0Checked : node4_0.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows00.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows16.checked⟩

private def node4_8 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows08.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows24.table

private theorem node4_8Checked : node4_8.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows08.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows24.checked⟩

private def node3_0 : Table := .branch node4_0 node4_8

private theorem node3_0Checked : node3_0.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_0Checked, node4_8Checked⟩

private def node4_4 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows04.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows20.table

private theorem node4_4Checked : node4_4.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows04.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows20.checked⟩

private def node4_12 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows12.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows28.table

private theorem node4_12Checked : node4_12.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows12.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows28.checked⟩

private def node3_4 : Table := .branch node4_4 node4_12

private theorem node3_4Checked : node3_4.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_4Checked, node4_12Checked⟩

private def node2_0 : Table := .branch node3_0 node3_4

private theorem node2_0Checked : node2_0.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node3_0Checked, node3_4Checked⟩

private def node4_2 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows02.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows18.table

private theorem node4_2Checked : node4_2.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows02.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows18.checked⟩

private def node4_10 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows10.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows26.table

private theorem node4_10Checked : node4_10.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows10.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows26.checked⟩

private def node3_2 : Table := .branch node4_2 node4_10

private theorem node3_2Checked : node3_2.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_2Checked, node4_10Checked⟩

private def node4_6 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows06.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows22.table

private theorem node4_6Checked : node4_6.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows06.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows22.checked⟩

private def node4_14 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows14.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows30.table

private theorem node4_14Checked : node4_14.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows14.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows30.checked⟩

private def node3_6 : Table := .branch node4_6 node4_14

private theorem node3_6Checked : node3_6.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_6Checked, node4_14Checked⟩

private def node2_2 : Table := .branch node3_2 node3_6

private theorem node2_2Checked : node2_2.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node3_2Checked, node3_6Checked⟩

private def node1_0 : Table := .branch node2_0 node2_2

private theorem node1_0Checked : node1_0.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node2_0Checked, node2_2Checked⟩

private def node4_1 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows01.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows17.table

private theorem node4_1Checked : node4_1.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows01.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows17.checked⟩

private def node4_9 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows09.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows25.table

private theorem node4_9Checked : node4_9.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows09.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows25.checked⟩

private def node3_1 : Table := .branch node4_1 node4_9

private theorem node3_1Checked : node3_1.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_1Checked, node4_9Checked⟩

private def node4_5 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows05.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows21.table

private theorem node4_5Checked : node4_5.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows05.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows21.checked⟩

private def node4_13 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows13.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows29.table

private theorem node4_13Checked : node4_13.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows13.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows29.checked⟩

private def node3_5 : Table := .branch node4_5 node4_13

private theorem node3_5Checked : node3_5.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_5Checked, node4_13Checked⟩

private def node2_1 : Table := .branch node3_1 node3_5

private theorem node2_1Checked : node2_1.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node3_1Checked, node3_5Checked⟩

private def node4_3 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows03.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows19.table

private theorem node4_3Checked : node4_3.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows03.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows19.checked⟩

private def node4_11 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows11.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows27.table

private theorem node4_11Checked : node4_11.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows11.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows27.checked⟩

private def node3_3 : Table := .branch node4_3 node4_11

private theorem node3_3Checked : node3_3.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_3Checked, node4_11Checked⟩

private def node4_7 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows07.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows23.table

private theorem node4_7Checked : node4_7.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows07.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows23.checked⟩

private def node4_15 : Table := .branch D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows15.table D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows31.table

private theorem node4_15Checked : node4_15.check = true :=
  Bool.and_eq_true_iff.mpr ⟨D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows15.checked, D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows31.checked⟩

private def node3_7 : Table := .branch node4_7 node4_15

private theorem node3_7Checked : node3_7.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node4_7Checked, node4_15Checked⟩

private def node2_3 : Table := .branch node3_3 node3_7

private theorem node2_3Checked : node2_3.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node3_3Checked, node3_7Checked⟩

private def node1_1 : Table := .branch node2_1 node2_3

private theorem node1_1Checked : node1_1.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node2_1Checked, node2_3Checked⟩

def table : Table := .branch node1_0 node1_1

theorem tableChecked : table.check = true :=
  Bool.and_eq_true_iff.mpr ⟨node1_0Checked, node1_1Checked⟩

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows
