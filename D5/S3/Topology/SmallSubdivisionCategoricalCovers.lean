/- GID: D5/S3/Topology/SmallSubdivisionCategoricalCovers
   generality: I
   mirror-B: D5/B/S3/Topology/SmallSubdivisionCategoricalCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Topology/SmallSubdivisionCategoricalCovers.cover_of_census_table; instance=D5/S3/Topology/SmallSubdivisionCategoricalCovers.census; result=D5/S3/Topology/SmallSubdivisionCategoricalCovers.cover_of_census_table
   digest: Checked partitions give categorical lower two-covers for the exceptional acyclic thirteen- and fourteen-point orders. -/

module

public import D5.S3.Topology.ThirteenPointStructuralCategoricalCovers
public import Mathlib.Data.Fin.VecNotation
import OmegaBuild.Commands

/-! Explicit partitions for the exceptional acyclic thirteen- and fourteen-point orders. -/

compile_only_with_mathlib

public section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Topology.SmallSubdivisionCategoricalCovers

open D5.S3.Topology.ConnectedCategoryGraft
open D5.S3.Topology.FiniteCategoricalCoverCertificate
open D5.S3.Topology.SubdivisionCategoricalCover
open PartialOrder (NonemptyFiniteChains)

open D5.S3.Topology.ThirteenPointStructuralCategoricalCovers

private def partition1 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 8, 19, 37, 74, 140, 495, 735, 1215, 2175, 4351]
    ![255, 7936] ![12, 0]
    ![[(16, 12), (32, 12), (1, 12), (64, 12), (2, 12), (128, 12), (4, 12), (8, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition2 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 8, 23, 41, 127, 143, 431, 671, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(64, 10), (256, 10), (32, 10), (512, 10), (16, 10), (128, 10), (1, 10), (2,
      10), (4, 10), (8, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition3 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 8, 23, 43, 76, 255, 367, 607, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (32, 10), (512, 10), (16, 10), (1, 10), (2, 10), (64,
      10), (4, 10), (8, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition4 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 8, 23, 43, 77, 239, 351, 575, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (64, 10), (512, 10), (16, 10), (4, 10), (32, 10), (1,
      10), (2, 10), (8, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition5 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 35, 69, 133, 261, 807, 1175, 2127, 4607]
    ![511, 7680] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (2, 12), (64, 12), (128, 12), (256, 12), (1,
      12), (4, 12)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition6 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 839, 1175, 2095, 4607]
    ![511, 7680] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (64, 12), (1, 12), (128, 12), (256, 12), (2,
      12), (4, 12)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition7 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 135, 423, 663, 1143, 2127, 4159]
    ![255, 7936] ![0, 0]
    ![[(8, 12), (64, 10), (128, 8), (4, 5), (4, 0), (32, 0), (64, 0), (128, 7),
      (128, 9), (2, 4), (2, 0), (8, 0), (16, 0), (128, 0)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition8 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 135, 455, 663, 1111, 2095, 4223]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (64, 12), (128, 8), (4, 6), (4, 0), (128, 7),
      (128, 9), (128, 4), (128, 12), (1, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition9 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 247, 351, 559, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (16, 10), (64, 10), (512, 10), (8, 10), (2, 10), (32,
      10), (1, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition10 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 255, 343, 559, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (16, 10), (64, 10), (512, 10), (8, 10), (2, 10), (32,
      10), (1, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition11 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 262, 807, 1175, 2127, 4607]
    ![511, 7680] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 12), (256, 12), (2,
      12), (4, 12)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition12 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 359, 663, 1103, 2079, 4351]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition13 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 591, 1263, 2079, 4191]
    ![255, 7936] ![10, 0]
    ![[(8, 10), (16, 12), (32, 10), (1, 3), (1, 1), (16, 6), (16, 10), (1, 10), (64,
      10), (128, 10), (2, 10), (4, 10)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition14 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1071, 2287, 4191]
    ![255, 7936] ![11, 0]
    ![[(8, 11), (16, 12), (32, 11), (1, 3), (1, 1), (16, 6), (16, 11), (1, 11), (64,
      11), (128, 11), (2, 11), (4, 11)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition15 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1103, 2079, 4351]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition16 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1103, 2287, 4191]
    ![255, 7936] ![11, 0]
    ![[(8, 11), (16, 12), (32, 11), (1, 3), (1, 1), (16, 6), (16, 11), (1, 11), (64,
      11), (128, 11), (2, 11), (4, 11)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition17 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1135, 2079, 4319]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 10), (1, 3), (1, 1), (32, 6), (32, 12), (1, 12), (64,
      12), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition18 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1135, 2207, 4191]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 10), (1, 3), (1, 1), (32, 6), (32, 12), (1, 12), (64,
      12), (128, 11), (2, 3), (2, 0), (128, 4), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition19 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1167, 2127, 4351]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition20 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1199, 2079, 4223]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 10), (2, 3), (2, 0),
      (128, 5), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition21 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1199, 2207, 4191]
    ![255, 7936] ![11, 0]
    ![[(8, 11), (16, 11), (32, 10), (1, 3), (1, 1), (32, 7), (32, 11), (1, 11), (64,
      12), (128, 11), (2, 3), (2, 0), (64, 4), (64, 11), (2, 11), (4, 11)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition22 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1231, 2079, 4223]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 10), (128, 6), (128,
      12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition23 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1231, 2143, 4159]
    ![255, 7936] ![11, 0]
    ![[(8, 11), (16, 11), (32, 12), (32, 4), (32, 11), (1, 11), (64, 11), (128, 10),
      (128, 6), (128, 11), (2, 11), (4, 11)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition24 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1231, 2159, 4191]
    ![255, 7936] ![1, 0]
    ![[(16, 12), (32, 11), (1, 3), (1, 1), (8, 1), (128, 10), (4, 6), (4, 1), (16,
      1), (32, 1), (64, 1), (128, 1)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition25 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1231, 2223, 4191]
    ![255, 7936] ![10, 0]
    ![[(8, 10), (16, 12), (32, 11), (1, 3), (1, 1), (16, 6), (16, 10), (32, 7), (32,
      10), (1, 10), (64, 10), (128, 10), (2, 10), (4, 10)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition26 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1263, 2079, 4191]
    ![255, 7936] ![10, 0]
    ![[(8, 10), (16, 12), (32, 10), (1, 3), (1, 1), (16, 6), (16, 10), (1, 10), (64,
      10), (128, 10), (2, 10), (4, 10)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition27 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 599, 1271, 2127, 4191]
    ![255, 7936] ![10, 0]
    ![[(8, 12), (16, 10), (32, 10), (1, 4), (1, 2), (8, 6), (8, 10), (1, 10), (64,
      10), (128, 10), (2, 10), (4, 10)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition28 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 719, 1135, 2079, 4191]
    ![255, 7936] ![1, 0]
    ![[(16, 12), (32, 10), (1, 3), (1, 1), (8, 1), (128, 9), (4, 6), (4, 1), (16,
      1), (32, 1), (64, 1), (128, 1)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition29 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 727, 1103, 2079, 4223]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (1, 12), (64, 12), (128, 9), (128, 6), (128,
      12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition30 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 727, 1103, 2143, 4159]
    ![255, 7936] ![11, 0]
    ![[(8, 11), (16, 11), (32, 12), (32, 4), (32, 11), (1, 11), (64, 11), (128, 9),
      (128, 6), (128, 11), (2, 11), (4, 11)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition31 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 727, 1143, 2127, 4191]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 10), (32, 4), (32, 12), (1, 12), (64, 12), (128, 9),
      (128, 6), (128, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition32 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 423, 759, 1103, 2079, 4191]
    ![255, 7936] ![9, 0]
    ![[(8, 12), (16, 9), (32, 9), (1, 4), (1, 2), (8, 6), (8, 9), (1, 9), (64, 9),
      (128, 9), (2, 9), (4, 9)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition33 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 37, 70, 134, 487, 663, 1071, 2159, 4191]
    ![255, 7936] ![1, 0]
    ![[(16, 12), (32, 11), (1, 3), (1, 1), (8, 1), (128, 8), (4, 6), (4, 1), (16,
      1), (32, 1), (64, 1), (128, 1)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition34 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 135, 423, 663, 1143, 2127, 4159]
    ![255, 7936] ![2, 0]
    ![[(8, 12), (64, 10), (128, 8), (2, 5), (2, 2), (32, 2), (64, 2), (128, 7),
      (128, 9), (1, 4), (1, 2), (8, 2), (16, 2), (128, 2)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition35 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 135, 455, 663, 1111, 2095, 4223]
    ![255, 7936] ![12, 0]
    ![[(8, 12), (16, 12), (32, 12), (64, 12), (128, 8), (2, 6), (2, 2), (128, 7),
      (128, 9), (128, 4), (128, 12), (1, 12), (2, 12), (4, 12)],
      [(256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition36 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 247, 351, 559, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (16, 10), (64, 10), (512, 10), (8, 10), (1, 10), (32,
      10), (2, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition37 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 255, 343, 559, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(128, 10), (256, 10), (16, 10), (64, 10), (512, 10), (8, 10), (1, 10), (32,
      10), (2, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition38 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 71, 231, 343, 567, 1103, 2095, 4127]
    ![127, 8064] ![6, 0]
    ![[(8, 10), (8, 6), (16, 8), (1, 6), (16, 6), (32, 7), (2, 6), (4, 6), (32, 6)],
      [(128, 0), (256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition39 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 119, 175, 319, 575, 1791, 2559, 5119]
    ![1023, 7168] ![12, 0]
    ![[(64, 12), (128, 12), (256, 12), (512, 12), (8, 12), (16, 12), (1, 12), (32,
      12), (2, 12), (4, 12)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition40 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 119, 183, 303, 559, 1055, 2079, 4159]
    ![63, 8128] ![12, 0]
    ![[(8, 12), (16, 12), (1, 12), (32, 12), (2, 12), (4, 12)],
      [(64, 0), (128, 0), (256, 0), (512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition41 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 543, 1535, 2559, 4607]
    ![511, 7680] ![10, 0]
    ![[(64, 10), (128, 10), (16, 10), (256, 10), (8, 10), (1, 10), (32, 10), (2,
      10), (4, 10)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition42 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 543, 1535, 3071, 5119]
    ![1023, 7168] ![11, 0]
    ![[(64, 11), (128, 11), (256, 11), (32, 11), (512, 11), (8, 11), (2, 11), (16,
      11), (1, 11), (4, 11)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition43 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 543, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(64, 10), (128, 10), (256, 10), (32, 10), (512, 10), (8, 10), (2, 10), (16,
      10), (1, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition44 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 567, 1535, 2559, 4607]
    ![511, 7680] ![10, 0]
    ![[(64, 10), (128, 10), (16, 10), (256, 10), (8, 10), (1, 10), (32, 10), (2,
      10), (4, 10)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition45 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 567, 1535, 3071, 5119]
    ![1023, 7168] ![11, 0]
    ![[(64, 11), (128, 11), (256, 11), (8, 11), (512, 11), (16, 11), (1, 11), (32,
      11), (2, 11), (4, 11)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition46 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 767, 1535, 2559, 4607]
    ![511, 7680] ![10, 0]
    ![[(64, 10), (128, 10), (16, 10), (256, 10), (8, 10), (1, 10), (32, 10), (2,
      10), (4, 10)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition47 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 303, 1023, 1535, 2559, 4607]
    ![511, 7680] ![9, 0]
    ![[(64, 9), (128, 9), (16, 9), (256, 9), (8, 9), (1, 9), (32, 9), (2, 9), (4,
      9)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition48 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 38, 127, 183, 311, 559, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(64, 10), (128, 10), (256, 10), (16, 10), (512, 10), (8, 10), (1, 10), (32,
      10), (2, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition49 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 39, 119, 175, 287, 767, 1535, 2559, 4607]
    ![511, 7680] ![10, 0]
    ![[(64, 10), (128, 10), (32, 10), (256, 10), (8, 10), (2, 10), (16, 10), (1,
      10), (4, 10)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition50 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 63, 71, 215, 335, 543, 1535, 2559, 4607]
    ![511, 7680] ![10, 0]
    ![[(32, 10), (128, 10), (16, 10), (256, 10), (8, 10), (64, 10), (1, 10), (2,
      10), (4, 10)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition51 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 63, 71, 215, 335, 543, 1535, 3071, 5119]
    ![1023, 7168] ![11, 0]
    ![[(32, 11), (128, 11), (256, 11), (64, 11), (512, 11), (8, 11), (2, 11), (16,
      11), (1, 11), (4, 11)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition52 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 63, 71, 215, 335, 1023, 1535, 2559, 4607]
    ![511, 7680] ![9, 0]
    ![[(32, 9), (128, 9), (16, 9), (256, 9), (8, 9), (64, 9), (1, 9), (2, 9), (4,
      9)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def partition53 : CertifiedOrder 13 :=
  certify ![1, 2, 4, 11, 21, 63, 95, 135, 407, 655, 2047, 3071, 5119]
    ![1023, 7168] ![10, 0]
    ![[(32, 10), (64, 10), (256, 10), (16, 10), (512, 10), (8, 10), (128, 10), (1,
      10), (2, 10), (4, 10)],
      [(1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def partitionCensus : List (CertifiedOrder 13) :=
  [partition1, partition2, partition3, partition4, partition5, partition6,
   partition7, partition8, partition9, partition10, partition11, partition12,
   partition13, partition14, partition15, partition16, partition17, partition18,
   partition19, partition20, partition21, partition22, partition23, partition24,
   partition25, partition26, partition27, partition28, partition29, partition30,
   partition31, partition32, partition33, partition34, partition35, partition36,
   partition37, partition38, partition39, partition40, partition41, partition42,
   partition43, partition44, partition45, partition46, partition47, partition48,
   partition49, partition50, partition51, partition52, partition53]

private def fourteen1 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 599, 1335, 2255, 4399, 8367]
    ![487, 15896] ![0, 0]
    ![[(256, 10), (32, 10), (128, 11), (64, 11), (32, 5), (256, 8), (256, 12), (32,
      12), (2, 3), (2, 0), (32, 5), (256, 5), (256, 13), (32, 13), (4, 7), (4,
      1), (4, 3), (4, 0), (32, 0), (256, 0), (64, 0), (128, 0)],
      [(512, 4), (528, 10), (2048, 3), (4096, 3), (6152, 13), (1552, 0), (14344, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen2 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 855, 1079, 2255, 4399, 8367]
    ![487, 15896] ![13, 0]
    ![[(256, 9), (64, 9), (128, 13), (32, 13), (256, 8), (256, 12), (2, 3), (2, 0),
      (256, 5), (256, 13), (64, 6), (64, 11), (4, 7), (4, 1), (64, 3), (64,
      13), (4, 13), (2, 13), (1, 13)],
      [(512, 4), (528, 10), (2048, 3), (4096, 3), (6152, 13), (1552, 0), (14344, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen3 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 599, 1367, 2255, 4399, 8367]
    ![487, 15896] ![13, 0]
    ![[(256, 10), (64, 10), (128, 13), (32, 13), (256, 8), (256, 12), (2, 3), (2,
      0), (256, 5), (256, 13), (64, 6), (64, 11), (4, 7), (4, 1), (64, 3),
      (64, 13), (4, 13), (2, 13), (1, 13)],
      [(512, 4), (528, 10), (2048, 3), (4096, 3), (6152, 13), (1552, 0), (14344, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen4 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 525, 1375, 2911, 4287, 8895]
    ![911, 15472] ![9, 0]
    ![[(1, 9), (4, 9), (517, 3), (256, 11), (128, 13), (2, 4), (2, 0), (128, 9),
      (256, 9), (525, 9), (2, 9)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen5 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 543, 1375, 2911, 4287, 8895]
    ![911, 15472] ![11, 0]
    ![[(1, 9), (4, 9), (517, 11), (256, 11), (128, 13), (128, 9), (128, 11), (8,
      11), (2, 11)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen6 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 524, 1375, 2783, 4927, 8895]
    ![911, 15472] ![4, 0]
    ![[(4, 9), (516, 3), (256, 10), (1, 10), (1, 1), (256, 8), (256, 12), (128, 13),
      (524, 9), (524, 2), (524, 5), (524, 0), (128, 4), (256, 4), (524, 4),
      (2, 4), (1, 4)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen7 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 525, 1887, 2271, 4415, 8895]
    ![911, 15472] ![9, 0]
    ![[(1, 9), (4, 9), (517, 3), (256, 10), (128, 13), (2, 4), (2, 0), (128, 9),
      (256, 9), (525, 9), (2, 9)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen8 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 543, 1887, 2271, 4415, 8895]
    ![911, 15472] ![10, 0]
    ![[(1, 9), (4, 9), (517, 10), (256, 10), (128, 13), (128, 9), (128, 10), (8,
      10), (2, 10)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen9 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 525, 1247, 2783, 4415, 9023]
    ![911, 15472] ![7, 0]
    ![[(2, 8), (4, 9), (258, 3), (516, 11), (516, 7), (266, 7), (1, 7)],
      [(16, 0), (32, 0), (4096, 0), (8192, 0), (64, 1), (1024, 4), (2048, 4), (64,
      4), (64, 0), (1024, 0), (2048, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen10 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 543, 1247, 2783, 4415, 9023]
    ![911, 15472] ![11, 0]
    ![[(4, 9), (516, 11), (128, 11), (1, 11), (256, 13), (256, 9), (256, 11), (8,
      11), (2, 11)],
      [(16, 0), (32, 0), (4096, 0), (8192, 0), (64, 1), (1024, 4), (2048, 4), (64,
      4), (64, 0), (1024, 0), (2048, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen11 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 265, 522, 1835, 2463, 4311, 8831]
    ![911, 15472] ![9, 0]
    ![[(1, 8), (4, 7), (132, 1), (134, 9), (257, 3), (265, 9)],
      [(1024, 5), (1056, 13), (2048, 4), (2064, 0), (64, 0), (4096, 0), (9248, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen12 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 265, 526, 1839, 2463, 4311, 8831]
    ![911, 15472] ![6, 0]
    ![[(1, 8), (257, 3), (265, 9), (777, 13), (128, 12), (2, 4), (2, 0), (128, 6),
      (777, 6), (4, 6), (2, 6)],
      [(1024, 5), (1056, 13), (2048, 4), (2064, 0), (64, 0), (4096, 0), (9248, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen13 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 265, 522, 1455, 2843, 4311, 8831]
    ![911, 15472] ![9, 0]
    ![[(1, 8), (4, 7), (132, 1), (134, 9), (257, 3), (265, 9)],
      [(1024, 5), (1056, 13), (2048, 4), (2064, 0), (64, 0), (4096, 0), (9248, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen14 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 265, 526, 1455, 2847, 4311, 8831]
    ![911, 15472] ![6, 0]
    ![[(1, 8), (257, 3), (265, 9), (777, 13), (128, 12), (2, 4), (2, 0), (128, 6),
      (777, 6), (4, 6), (2, 6)],
      [(1024, 5), (1056, 13), (2048, 4), (2064, 0), (64, 0), (4096, 0), (9248, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen15 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 265, 526, 1255, 2847, 4511, 8831]
    ![911, 15472] ![6, 0]
    ![[(1, 8), (257, 3), (265, 9), (777, 13), (128, 10), (2, 5), (2, 0), (128, 6),
      (777, 6), (4, 6), (2, 6)],
      [(2048, 4), (4096, 4), (6160, 13), (32, 0), (64, 0), (1024, 0), (14352, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen16 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1391, 2271, 4831, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen17 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1263, 2399, 4831, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen18 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1775, 2399, 4319, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen19 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1195, 2399, 4831, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(1024, 5), (1056, 13), (9248, 4), (9264, 0), (64, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen20 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 526, 1455, 2135, 4831, 9023]
    ![911, 15472] ![12, 0]
    ![[(512, 12), (128, 12), (2, 12), (1, 12), (256, 13), (256, 9), (256, 12), (8,
      12), (4, 12)],
      [(1024, 5), (1056, 13), (9248, 4), (9264, 0), (64, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen21 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 269, 526, 1455, 2655, 4319, 9023]
    ![911, 15472] ![13, 0]
    ![[(1, 8), (512, 13), (257, 13), (4, 13), (128, 10), (2, 5), (2, 0), (128, 8),
      (128, 13), (8, 13), (2, 13)],
      [(1024, 5), (1056, 13), (9248, 4), (9264, 0), (64, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen22 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1775, 2203, 4447, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(2048, 4), (2064, 0), (32, 0), (64, 0), (1024, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen23 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 269, 526, 1263, 2463, 4703, 9023]
    ![911, 15472] ![13, 0]
    ![[(1, 8), (512, 13), (257, 13), (4, 13), (128, 11), (2, 4), (2, 0), (128, 8),
      (128, 13), (8, 13), (2, 13)],
      [(2048, 4), (2064, 0), (32, 0), (64, 0), (1024, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen24 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 525, 1263, 2783, 4415, 9023]
    ![911, 15472] ![7, 0]
    ![[(2, 8), (4, 9), (258, 3), (516, 11), (516, 7), (266, 7), (1, 7)],
      [(16, 0), (32, 0), (4096, 0), (8192, 0), (64, 2), (1024, 5), (2048, 9), (2048,
      13), (2048, 5), (64, 5), (64, 0), (1024, 0), (2048, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen25 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 71, 137, 266, 524, 1519, 2783, 4671, 8511]
    ![911, 15472] ![9, 0]
    ![[(1, 7), (2, 8), (4, 9), (129, 3), (258, 3), (395, 9)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen26 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 134, 266, 523, 1871, 2263, 4415, 8895]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (4, 7), (132, 1), (513, 10), (513, 8), (8, 8), (134, 8)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen27 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 134, 266, 523, 1871, 2783, 4415, 8375]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (4, 7), (132, 1), (513, 10), (513, 8), (8, 8), (134, 8)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen28 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 527, 1871, 2399, 4287, 8895]
    ![911, 15472] ![10, 0]
    ![[(1, 9), (4, 9), (517, 10), (256, 10), (128, 13), (128, 9), (128, 10), (8,
      10), (2, 10)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen29 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 527, 1871, 2271, 4415, 8895]
    ![911, 15472] ![10, 0]
    ![[(1, 9), (4, 9), (517, 10), (256, 10), (128, 13), (128, 9), (128, 10), (8,
      10), (2, 10)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen30 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 267, 526, 1487, 2655, 4927, 8383]
    ![911, 15472] ![8, 0]
    ![[(1, 8), (4, 9), (516, 12), (516, 8), (128, 10), (128, 8), (8, 8), (2, 8)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen31 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 267, 526, 1487, 2911, 4671, 8383]
    ![911, 15472] ![8, 0]
    ![[(1, 8), (4, 9), (516, 11), (516, 8), (128, 10), (128, 8), (8, 8), (2, 8)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen32 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 135, 265, 522, 1935, 2399, 4799, 8311]
    ![911, 15472] ![10, 0]
    ![[(4, 7), (512, 10), (256, 10), (132, 10), (8, 10), (2, 10), (1, 10)],
      [(16, 0), (32, 0), (1024, 0), (4096, 0), (64, 1), (2048, 4), (8192, 4), (64,
      4), (64, 0), (2048, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen33 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 527, 1743, 2271, 4415, 9023]
    ![911, 15472] ![10, 0]
    ![[(4, 9), (516, 10), (128, 10), (1, 10), (256, 13), (256, 9), (256, 10), (8,
      10), (2, 10)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen34 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 526, 1487, 2783, 4151, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 7), (4, 9), (129, 3), (516, 13), (516, 8), (137, 8), (2, 8)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen35 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 71, 137, 266, 526, 1487, 2783, 4671, 8511]
    ![911, 15472] ![7, 0]
    ![[(1, 7), (4, 9), (129, 3), (516, 11), (256, 10), (2, 6), (2, 0), (256, 7),
      (516, 7), (137, 7), (2, 7)],
      [(1024, 6), (1088, 11), (3136, 4), (3152, 0), (32, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen36 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 69, 138, 267, 524, 1519, 2203, 4703, 9023]
    ![911, 15472] ![7, 0]
    ![[(1, 8), (4, 9), (516, 3), (257, 10), (257, 7), (524, 7), (2, 7)],
      [(2048, 4), (2064, 0), (32, 0), (64, 0), (1024, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen37 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 267, 524, 1519, 2719, 4183, 9023]
    ![911, 15472] ![7, 0]
    ![[(2, 8), (4, 9), (516, 3), (258, 10), (258, 7), (524, 7), (1, 7)],
      [(2048, 4), (2064, 0), (32, 0), (8192, 0), (64, 1), (1024, 8), (1024, 13),
      (1024, 4), (4096, 4), (64, 4), (64, 0), (1024, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen38 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1679, 2415, 4831, 9023]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(16, 0), (32, 0), (64, 0), (1024, 0), (2048, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen39 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 526, 1422, 2151, 4831, 9023]
    ![911, 15472] ![12, 0]
    ![[(512, 12), (128, 12), (2, 12), (1, 12), (256, 13), (256, 9), (256, 12), (8,
      12), (4, 12)],
      [(16, 0), (32, 0), (64, 0), (2048, 0), (4096, 0), (8192, 0), (1024, 1), (1024,
      4), (1024, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen40 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1743, 2735, 4447, 9023]
    ![911, 15472] ![8, 13]
    ![[(1, 9), (2, 7), (130, 3), (513, 13), (513, 8), (138, 8), (4, 8)],
      [(1024, 6), (1088, 12), (2048, 5), (2080, 13), (5184, 4), (5200, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen41 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 268, 525, 1839, 2735, 4447, 8927]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 2), (513, 10), (513, 8), (8, 8), (134, 8)],
      [(1024, 5), (1056, 11), (16, 0), (64, 0), (3104, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen42 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1839, 2735, 4447, 8927]
    ![911, 15472] ![8, 0]
    ![[(1, 9), (2, 7), (130, 3), (513, 10), (513, 8), (138, 8), (4, 8)],
      [(1024, 5), (1056, 11), (16, 0), (64, 0), (3104, 0), (4096, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen43 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 134, 268, 525, 1711, 2415, 4895, 8927]
    ![911, 15472] ![8, 13]
    ![[(1, 9), (2, 7), (130, 2), (513, 12), (513, 8), (8, 8), (134, 8)],
      [(1024, 5), (1056, 11), (3104, 6), (3168, 13), (4096, 4), (4112, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen44 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 35, 69, 138, 268, 525, 1711, 2415, 4895, 8927]
    ![911, 15472] ![8, 13]
    ![[(1, 9), (2, 7), (130, 3), (513, 12), (513, 8), (138, 8), (4, 8)],
      [(1024, 5), (1056, 11), (3104, 6), (3168, 13), (4096, 4), (4112, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen45 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 525, 1807, 2287, 4831, 9023]
    ![911, 15472] ![7, 0]
    ![[(2, 8), (4, 9), (258, 3), (516, 12), (516, 7), (266, 7), (1, 7)],
      [(16, 0), (32, 0), (1024, 0), (8192, 0), (64, 2), (2048, 5), (4096, 9), (4096,
      13), (4096, 5), (64, 5), (64, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen46 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 525, 1419, 2151, 4831, 9023]
    ![911, 15472] ![7, 0]
    ![[(2, 8), (4, 9), (258, 3), (516, 12), (516, 7), (266, 7), (1, 7)],
      [(16, 0), (32, 0), (1024, 0), (8192, 0), (64, 2), (2048, 5), (4096, 9), (4096,
      13), (4096, 5), (64, 5), (64, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen47 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 526, 1935, 2415, 4831, 8767]
    ![911, 15472] ![8, 0]
    ![[(1, 7), (4, 9), (129, 3), (516, 10), (516, 8), (137, 8), (2, 8)],
      [(16, 0), (32, 0), (1024, 0), (8192, 0), (64, 2), (2048, 5), (2048, 13), (64,
      9), (64, 1), (2048, 4), (4096, 4), (64, 4), (64, 0), (2048, 0), (4096,
      0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen48 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 70, 137, 266, 526, 1487, 2863, 4831, 8767]
    ![911, 15472] ![8, 13]
    ![[(1, 7), (4, 9), (129, 3), (516, 11), (516, 8), (137, 8), (2, 8)],
      [(1024, 6), (1088, 12), (2048, 5), (2080, 13), (5184, 4), (5200, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen49 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 19, 37, 71, 138, 268, 527, 1711, 2287, 4895, 8543]
    ![911, 15472] ![10, 13]
    ![[(1, 9), (513, 10), (128, 10), (2, 10), (256, 12), (256, 9), (256, 10), (8,
      10), (4, 10)],
      [(1024, 5), (1056, 11), (3104, 6), (3168, 13), (4096, 4), (4112, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen50 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 16, 35, 69, 135, 266, 536, 1052, 3039, 5823, 9599]
    ![1567, 14816] ![9, 0]
    ![[(4, 10), (1028, 12), (1028, 9), (16, 9), (8, 9), (2, 11), (1, 11), (1, 9),
      (2, 9)],
      [(32, 0), (64, 0), (128, 0), (4096, 0), (256, 1), (2048, 7), (2048, 12),
      (2048, 5), (8192, 5), (256, 5), (256, 0), (2048, 0), (8192, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen51 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 16, 35, 69, 137, 274, 534, 1052, 3039, 5823, 9599]
    ![1183, 15200] ![1, 13]
    ![[(1, 7), (4, 10), (16, 10), (129, 3), (137, 10), (1181, 12), (1181, 1)],
      [(32, 0), (64, 0), (256, 1), (512, 1), (4096, 5), (4096, 13), (32, 13), (64,
      6), (64, 2), (2048, 9), (2048, 12), (64, 10), (64, 4), (2048, 9), (2048,
      11), (2048, 8), (2048, 13), (64, 13), (512, 13), (256, 13)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def fourteen52 : CertifiedOrder 14 :=
  certify ![1, 2, 4, 8, 16, 35, 69, 138, 276, 538, 1052, 3039, 5567, 9855]
    ![1311, 15072] ![8, 3]
    ![[(8, 10), (1032, 12), (1032, 8), (16, 8), (4, 8), (2, 11), (1, 11), (1, 8),
      (2, 8)],
      [(32, 0), (64, 0), (128, 1), (512, 1), (4096, 5), (4096, 13), (512, 9), (128,
      9), (128, 3), (512, 3), (32, 13), (32, 3), (64, 6), (64, 2), (4096, 3),
      (8192, 10), (8192, 12), (64, 8), (64, 4), (2048, 9), (8192, 10), (8192,
      13), (8192, 9), (64, 9), (64, 3), (2048, 3), (8192, 3)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def fourteenCensus : List (CertifiedOrder 14) :=
  [fourteen1, fourteen2, fourteen3, fourteen4, fourteen5, fourteen6,
   fourteen7, fourteen8, fourteen9, fourteen10, fourteen11, fourteen12,
   fourteen13, fourteen14, fourteen15, fourteen16, fourteen17, fourteen18,
   fourteen19, fourteen20, fourteen21, fourteen22, fourteen23, fourteen24,
   fourteen25, fourteen26, fourteen27, fourteen28, fourteen29, fourteen30,
   fourteen31, fourteen32, fourteen33, fourteen34, fourteen35, fourteen36,
   fourteen37, fourteen38, fourteen39, fourteen40, fourteen41, fourteen42,
   fourteen43, fourteen44, fourteen45, fourteen46, fourteen47, fourteen48,
   fourteen49, fourteen50, fourteen51, fourteen52]


/-- The displayed exceptional order tables at each census size. -/
def census : (n : ℕ) → List (CertifiedOrder n)
  | 13 => partitionCensus
  | 14 => fourteenCensus
  | _ => []

/-- A displayed table has a categorical lower two-cover of its second ordinary
subdivision. Census completeness and classification are external. -/
theorem cover_of_census_table {n : ℕ} (le : Fin n → Fin n → Bool)
    (hm : le ∈ (census n).map CertifiedOrder.le) :
    ∃ hv : ValidOrder le,
      letI : PartialOrder (Fin n) := tableOrder le hv
      HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains (Fin n))) 2 := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
  exact ⟨w.valid, w.doubleSubdivisionCover⟩

end D5.S3.Topology.SmallSubdivisionCategoricalCovers
