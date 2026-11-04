import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Polygons.PolygonCatalanSupplier

/-!
Exact source telescope witnesses for the public targets below. The available
DependentFamily enrollment does not supply their original-source reconstruction,
lawful readout, full-domain variation/sensitivity or actual observational
dependence proofs. No Contract.Registration is asserted. These exact unfinished
targets and missing evidence are disclosed for issue #24755.
-/
namespace Reg.D5.S3.Geometry.Polygons.PolygonCatalanSupplier

abbrev target_1_scope := type_of% (@_root_.ClusterAlgebras.catalanNumber_zero)
def target_1_source : target_1_scope := @_root_.ClusterAlgebras.catalanNumber_zero

abbrev target_2_scope := type_of% (@_root_.ClusterAlgebras.catalanNumber_succ)
def target_2_source : target_2_scope := @_root_.ClusterAlgebras.catalanNumber_succ

abbrev target_3_scope := type_of% (@_root_.ClusterAlgebras.TypeA.Interleave.symm)
def target_3_source : target_3_scope := @_root_.ClusterAlgebras.TypeA.Interleave.symm

abbrev target_4_scope := type_of% (@_root_.ClusterAlgebras.TypeA.mem_intervalTriangulations)
def target_4_source : target_4_scope := @_root_.ClusterAlgebras.TypeA.mem_intervalTriangulations

abbrev target_5_scope := type_of% (@_root_.ClusterAlgebras.TypeA.mk_mem_intervalDiagonals_iff)
def target_5_source : target_5_scope := @_root_.ClusterAlgebras.TypeA.mk_mem_intervalDiagonals_iff

abbrev target_6_scope := type_of% (@_root_.ClusterAlgebras.TypeA.mk_mem_intervalSides_iff)
def target_6_source : target_6_scope := @_root_.ClusterAlgebras.TypeA.mk_mem_intervalSides_iff

abbrev target_7_scope := type_of% (@_root_.ClusterAlgebras.TypeA.not_interleave_of_mem_intervalSides)
def target_7_source : target_7_scope := @_root_.ClusterAlgebras.TypeA.not_interleave_of_mem_intervalSides

abbrev target_8_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.bounds_of_mem_intervalSegments)
def target_8_source : target_8_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.bounds_of_mem_intervalSegments

abbrev target_9_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.not_interleave)
def target_9_source : target_9_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.not_interleave

abbrev target_10_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.exists_interleave)
def target_10_source : target_10_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.exists_interleave

abbrev target_11_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.existsUnique_apex)
def target_11_source : target_11_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.existsUnique_apex

abbrev target_12_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.le_or_le_of_apex)
def target_12_source : target_12_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.le_or_le_of_apex

abbrev target_13_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.eq_union_of_apex)
def target_13_source : target_13_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.eq_union_of_apex

abbrev target_14_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_left_of_apex)
def target_14_source : target_14_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_left_of_apex

abbrev target_15_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_right_of_apex)
def target_15_source : target_15_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.inter_right_of_apex

abbrev target_16_scope := type_of% (@_root_.ClusterAlgebras.TypeA.mk_mem_union_intervalDiagonals_iff)
def target_16_source : target_16_scope := @_root_.ClusterAlgebras.TypeA.mk_mem_union_intervalDiagonals_iff

abbrev target_17_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.union)
def target_17_source : target_17_scope := @_root_.ClusterAlgebras.TypeA.IsIntervalTriangulation.union

abbrev target_18_scope := type_of% (@_root_.ClusterAlgebras.TypeA.union_inter_intervalDiagonals_left)
def target_18_source : target_18_scope := @_root_.ClusterAlgebras.TypeA.union_inter_intervalDiagonals_left

abbrev target_19_scope := type_of% (@_root_.ClusterAlgebras.TypeA.union_inter_intervalDiagonals_right)
def target_19_source : target_19_scope := @_root_.ClusterAlgebras.TypeA.union_inter_intervalDiagonals_right

abbrev target_20_scope := type_of% (@_root_.ClusterAlgebras.TypeA.union_apex_mem_intervalSegments)
def target_20_source : target_20_scope := @_root_.ClusterAlgebras.TypeA.union_apex_mem_intervalSegments

abbrev target_21_scope := type_of% (@_root_.ClusterAlgebras.TypeA.exists_equiv_intervalTriangulation)
def target_21_source : target_21_scope := @_root_.ClusterAlgebras.TypeA.exists_equiv_intervalTriangulation

abbrev target_22_scope := type_of% (@_root_.ClusterAlgebras.TypeA.card_subtype_isIntervalTriangulation)
def target_22_source : target_22_scope := @_root_.ClusterAlgebras.TypeA.card_subtype_isIntervalTriangulation

abbrev target_23_scope := type_of% (@_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_eq_sum)
def target_23_source : target_23_scope := @_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_eq_sum

abbrev target_24_scope := type_of% (@_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_self_add_one)
def target_24_source : target_24_scope := @_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_self_add_one

abbrev target_25_scope := type_of% (@_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_eq_catalanNumber)
def target_25_source : target_25_scope := @_root_.ClusterAlgebras.TypeA.intervalTriangulationCount_eq_catalanNumber

abbrev target_26_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePosSeg_mk)
def target_26_source : target_26_scope := @_root_.ClusterAlgebras.TypeA.basePosSeg_mk

abbrev target_27_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePos_nonneg)
def target_27_source : target_27_scope := @_root_.ClusterAlgebras.TypeA.basePos_nonneg

abbrev target_28_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePos_lt)
def target_28_source : target_28_scope := @_root_.ClusterAlgebras.TypeA.basePos_lt

abbrev target_29_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePos_eq_ite)
def target_29_source : target_29_scope := @_root_.ClusterAlgebras.TypeA.basePos_eq_ite

abbrev target_30_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePos_injective)
def target_30_source : target_30_scope := @_root_.ClusterAlgebras.TypeA.basePos_injective

abbrev target_31_scope := type_of% (@_root_.ClusterAlgebras.TypeA.exists_basePos_eq)
def target_31_source : target_31_scope := @_root_.ClusterAlgebras.TypeA.exists_basePos_eq

abbrev target_32_scope := type_of% (@_root_.ClusterAlgebras.TypeA.sbtw_iff_val)
def target_32_source : target_32_scope := @_root_.ClusterAlgebras.TypeA.sbtw_iff_val

abbrev target_33_scope := type_of% (@_root_.ClusterAlgebras.TypeA.sbtw_iff_sbtw_basePos)
def target_33_source : target_33_scope := @_root_.ClusterAlgebras.TypeA.sbtw_iff_sbtw_basePos

abbrev target_34_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePos_add_one)
def target_34_source : target_34_scope := @_root_.ClusterAlgebras.TypeA.basePos_add_one

abbrev target_35_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePosSeg_injective)
def target_35_source : target_35_scope := @_root_.ClusterAlgebras.TypeA.basePosSeg_injective

abbrev target_36_scope := type_of% (@_root_.ClusterAlgebras.TypeA.IsSegment.exists_basePos_lt)
def target_36_source : target_36_scope := @_root_.ClusterAlgebras.TypeA.IsSegment.exists_basePos_lt

abbrev target_37_scope := type_of% (@_root_.ClusterAlgebras.TypeA.basePosSeg_mk_of_lt)
def target_37_source : target_37_scope := @_root_.ClusterAlgebras.TypeA.basePosSeg_mk_of_lt

abbrev target_38_scope := type_of% (@_root_.ClusterAlgebras.TypeA.isSide_mk_iff)
def target_38_source : target_38_scope := @_root_.ClusterAlgebras.TypeA.isSide_mk_iff

abbrev target_39_scope := type_of% (@_root_.ClusterAlgebras.TypeA.cross_mk_iff)
def target_39_source : target_39_scope := @_root_.ClusterAlgebras.TypeA.cross_mk_iff

abbrev target_40_scope := type_of% (@_root_.ClusterAlgebras.TypeA.cross_mk_iff_basePos)
def target_40_source : target_40_scope := @_root_.ClusterAlgebras.TypeA.cross_mk_iff_basePos

abbrev target_41_scope := type_of% (@_root_.ClusterAlgebras.TypeA.isSide_mk_iff_basePos)
def target_41_source : target_41_scope := @_root_.ClusterAlgebras.TypeA.isSide_mk_iff_basePos

abbrev target_42_scope := type_of% (@_root_.ClusterAlgebras.TypeA.bijOn_basePosSeg_isDiagonal)
def target_42_source : target_42_scope := @_root_.ClusterAlgebras.TypeA.bijOn_basePosSeg_isDiagonal

abbrev target_43_scope := type_of% (@_root_.ClusterAlgebras.TypeA.cross_iff_interleave)
def target_43_source : target_43_scope := @_root_.ClusterAlgebras.TypeA.cross_iff_interleave

abbrev target_44_scope := type_of% (@_root_.ClusterAlgebras.TypeA.bijOn_basePosTri)
def target_44_source : target_44_scope := @_root_.ClusterAlgebras.TypeA.bijOn_basePosTri

abbrev target_45_scope := type_of% (@_root_.ClusterAlgebras.TypeA.encard_setOf_isTriangulation)
def target_45_source : target_45_scope := @_root_.ClusterAlgebras.TypeA.encard_setOf_isTriangulation

end Reg.D5.S3.Geometry.Polygons.PolygonCatalanSupplier
