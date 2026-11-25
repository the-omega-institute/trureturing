/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SixteenFourReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cyclic coefficient checks for the (16,4) shifted comparison. -/

import D5.S3.Quantum.Analysis.RefinedBMV67
import D5.S3.Quantum.Analysis.RefinedBMV84
import D5.S3.Quantum.Analysis.RefinedBMV.SixteenFourCertificate
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

/-! # Four-copy refined BMV at degree sixteen

Two rational Gram blocks compare the ordered word mean with the fourth
trace of the Hermitian part of the shifted product.
-/

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder CStarAlgebra

namespace RefinedBMV
namespace Algebra164

open Algebra44 (realTrace)
open private Word Terms shift aGap aRun gramTerms scaleTerms
  coefficientsVanish coefficients_sound Algebra84.representative weightedSum weightedSum_eq_map
  weightedSum_append weightedSum_scale traceWord traceWord_representative
  eval_gramTerms eval_aRun weightedGram weightedGram_nonneg
  realTrace_smul from D5.S3.Quantum.Analysis.RefinedBMV84
open private Algebra44.realTrace_mul_comm Algebra44.realTrace_add_four
  from D5.S3.Quantum.Analysis.RefinedBMV44
open private evalWord_append43 from D5.S3.Quantum.Analysis.RefinedBMV43

private def shiftedWord (i j k l : Bool) : Word :=
  [false] ++ aGap (4 + shift j - shift i) ++ aGap (4 + shift k - shift j) ++
    aGap (4 + shift l - shift k) ++ aRun (4 + shift i - shift l)

private def shiftedTerms : Terms :=
  [(1, shiftedWord false false false false), (1, shiftedWord true true true true),
    (4, shiftedWord false false false true), (4, shiftedWord true true true false),
    (4, shiftedWord true true false false), (2, shiftedWord true false true false)]

open private words0 words1 G0 G1 ldl0 ldl1
  from D5.S3.Quantum.Analysis.RefinedBMV.SixteenFourCertificate

open private gapTrace word_count from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

private def gapList : List FourCopyGap.Gap :=
  (List.range 17).flatMap fun a =>
    (List.range (17 - a)).flatMap fun b =>
      (List.range (17 - a - b)).map fun c => (a, b, c, 16 - a - b - c)

set_option maxRecDepth 12000 in
-- Check that the exact list of four-gap compositions has no duplicates.
set_option maxHeartbeats 6000000 in
private theorem gapList_nodup : gapList.Nodup := by decide +kernel

private theorem gapList_toFinset : gapList.toFinset = FourCopyGap.gaps 16 := by
  ext g
  rcases g with ⟨a, b, c, d⟩
  simp only [List.mem_toFinset, gapList, List.mem_flatMap, List.mem_range,
    List.mem_map, FourCopyGap.mem_gaps]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, he⟩
    simp only [Prod.mk.injEq] at he
    omega
  · intro h
    refine ⟨a, by omega, b, by omega, c, by omega, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    omega

private def gapWord (g : FourCopyGap.Gap) : Word :=
  aGap g.1 ++ aGap g.2.1 ++ aGap g.2.2.1 ++ aGap g.2.2.2

private def orderedTerms : Terms := gapList.map fun g => (1, gapWord g)

private def certificateTerms : Terms := gramTerms G0 [] words0 ++ gramTerms G1 [true] words1

private def gapTerms : Terms :=
  scaleTerms 80 orderedTerms ++ scaleTerms (-4845) shiftedTerms

private def allTerms : Terms := gapTerms ++ scaleTerms (-1) certificateTerms

private def chunk (i : ℕ) : Terms := (allTerms.drop (192 * i)).take 192

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary0 : Terms :=
  []

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary1 : Terms :=
  [(-240, gapWord (16, 0, 0, 0)), (-400, gapWord (15, 1, 0, 0)), (-240,
    gapWord (15, 0, 1, 0)), (-320, gapWord (14, 2, 0, 0)), (-400, gapWord (14, 1, 1, 0)), (-160, gapWord (14, 1, 0, 1)), (-160, gapWord (14, 0, 2, 0)), (-320, gapWord (13, 3, 0, 0)), (-240, gapWord (13, 2, 1, 0)), (-240, gapWord (13, 2, 0, 1)), (-240, gapWord (13, 1, 2, 0)), (-160, gapWord (13, 1, 1, 1)), (-160, gapWord (13, 0, 3, 0)),
    (-320, gapWord (12, 4, 0, 0)), (-240, gapWord (12, 3, 1, 0)), (-240,
    gapWord (12, 3, 0, 1)), (-160, gapWord (12, 2, 2, 0)), (-160, gapWord (12, 2, 1, 1)), (-80, gapWord (12, 2, 0, 2)), (-160, gapWord (12, 1, 3, 0)), (-80, gapWord (12, 1, 2, 1)), (-160, gapWord (12, 0, 4, 0)), (-320, gapWord (11, 5, 0, 0)), (-240, gapWord (11, 4, 1, 0)), (-240, gapWord (11, 4, 0, 1)), (-160, gapWord (11, 3, 2, 0)), (-160, gapWord (11, 3, 1, 1)), (-160, gapWord (11, 3, 0, 2)), (-160, gapWord (11, 2, 3, 0)), (-80, gapWord (11, 2, 2, 1)), (-160, gapWord (11, 1, 4, 0)), (-160, gapWord (11, 0, 5, 0)), (-320, gapWord (10, 6, 0, 0)), (-240, gapWord (10, 5, 1, 0)), (-240, gapWord (10, 5, 0, 1)), (-160, gapWord (10, 4, 2, 0)), (-160, gapWord (10, 4, 1, 1)), (-160, gapWord (10, 4, 0, 2)), (-160, gapWord (10, 3, 3, 0)), (-80, gapWord (10, 3, 2, 1)), (-80, gapWord (10, 3, 0, 3)), (-160, gapWord (10, 2, 4, 0)),
    (-160, gapWord (10, 1, 5, 0)), (-160, gapWord (10, 0, 6, 0)), (-320,
    gapWord (9, 7, 0, 0)), (-240, gapWord (9, 6, 1, 0)), (-240, gapWord (9, 6, 0, 1)), (-160, gapWord (9, 5, 2, 0)), (-160, gapWord (9, 5, 1, 1)), (-160, gapWord (9, 5, 0, 2)), (-160, gapWord (9, 4, 3, 0)), (-80, gapWord (9, 4, 2, 1)), (-160, gapWord (9, 4, 0, 3)), (-160, gapWord (9, 3, 4, 0)), (-160, gapWord (9, 2, 5, 0)), (-160, gapWord (9, 1, 6, 0)), (-160, gapWord (9, 0, 7, 0)), (-160, gapWord (8, 8, 0, 0)), (-240, gapWord (8, 7, 1, 0)), (-240, gapWord (8, 7, 0, 1)), (-160, gapWord (8, 6, 2, 0)), (-160, gapWord (8, 6, 1, 1)), (-160, gapWord (8, 6, 0, 2)), (-160, gapWord (8, 5, 3, 0)), (-80, gapWord (8, 5, 2, 1)), (-160, gapWord (8, 5, 0, 3)), (-160, gapWord (8, 4, 4, 0)), (-80, gapWord (8, 4, 0, 4)), (-160, gapWord (8, 3, 5, 0)),
    (-160, gapWord (8, 2, 6, 0)), (-160, gapWord (8, 1, 7, 0)), (-80,
    gapWord (8, 0, 8, 0)), (-160, gapWord (7, 7, 2, 0)), (-80, gapWord (7, 7, 1, 1)), (-160, gapWord (7, 6, 3, 0)), (-80, gapWord (7, 6, 2, 1)), (-80, gapWord (7, 6, 1, 2)), (-160, gapWord (7, 6, 0, 3)), (-160, gapWord (7, 5, 4, 0)), (-160, gapWord (7, 5, 0, 4)), (-160, gapWord (7, 4, 5, 0)), (-160, gapWord (7, 3, 6, 0)), (-80, gapWord (7, 2, 7, 0)), (-160, gapWord (6, 6, 4, 0)), (-160, gapWord (6, 5, 5, 0)), (-80, gapWord (6, 5, 0, 5)), (-80, gapWord (6, 4, 6, 0))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary2 : Terms :=
  [(-240, gapWord (16, 0, 0, 0)), (-480, gapWord (15, 1, 0, 0)), (-240,
    gapWord (15, 0, 1, 0)), (-400, gapWord (14, 2, 0, 0)), (-480, gapWord (14, 1, 1, 0)), (-240, gapWord (14, 1, 0, 1)), (-240, gapWord (14, 0, 2, 0)), (-320, gapWord (13, 3, 0, 0)), (-400, gapWord (13, 2, 1, 0)), (-400, gapWord (13, 2, 0, 1)), (-480, gapWord (13, 1, 2, 0)), (-240, gapWord (13, 1, 1, 1)), (-160, gapWord (13, 0, 3, 0)),
    (-320, gapWord (12, 4, 0, 0)), (-320, gapWord (12, 3, 1, 0)), (-320,
    gapWord (12, 3, 0, 1)), (-400, gapWord (12, 2, 2, 0)), (-400, gapWord (12, 2, 1, 1)), (-160, gapWord (12, 2, 0, 2)), (-320, gapWord (12, 1, 3, 0)), (-240, gapWord (12, 1, 2, 1)), (-160, gapWord (12, 0, 4, 0)), (-320, gapWord (11, 5, 0, 0)), (-320, gapWord (11, 4, 1, 0)), (-320, gapWord (11, 4, 0, 1)), (-320, gapWord (11, 3, 2, 0)), (-320, gapWord (11, 3, 1, 1)), (-240, gapWord (11, 3, 0, 2)), (-240, gapWord (11, 2, 3, 0)), (-400, gapWord (11, 2, 2, 1)), (-160, gapWord (11, 2, 1, 2)), (-320, gapWord (11, 1, 4, 0)), (-160, gapWord (11, 1, 3, 1)), (-160, gapWord (11, 0, 5, 0)), (-320, gapWord (10, 6, 0, 0)), (-320, gapWord (10, 5, 1, 0)), (-320, gapWord (10, 5, 0, 1)), (-320, gapWord (10, 4, 2, 0)), (-320, gapWord (10, 4, 1, 1)), (-240, gapWord (10, 4, 0, 2)), (-160, gapWord (10, 3, 3, 0)), (-320, gapWord (10, 3, 2, 1)), (-240, gapWord (10, 3, 1, 2)), (-80, gapWord (10, 3, 0, 3)), (-240, gapWord (10, 2, 4, 0)), (-240, gapWord (10, 2, 3, 1)), (-160, gapWord (10, 2, 2, 2)), (-320, gapWord (10, 1, 5, 0)), (-160, gapWord (10, 1, 4, 1)), (-160, gapWord (10, 0, 6, 0)), (-320, gapWord (9, 7, 0, 0)), (-320, gapWord (9, 6, 1, 0)), (-320, gapWord (9, 6, 0, 1)), (-320, gapWord (9, 5, 2, 0)), (-320, gapWord (9, 5, 1, 1)), (-240, gapWord (9, 5, 0, 2)), (-160, gapWord (9, 4, 3, 0)), (-320, gapWord (9, 4, 2, 1)), (-240, gapWord (9, 4, 1, 2)), (-160, gapWord (9, 4, 0, 3)), (-160, gapWord (9, 3, 4, 0)), (-160, gapWord (9, 3, 3, 1)), (-240, gapWord (9, 3, 2, 2)), (-80, gapWord (9, 3, 1, 3)), (-240, gapWord (9, 2, 5, 0)), (-240, gapWord (9, 2, 4, 1)), (-80, gapWord (9, 2, 3, 2)), (-320, gapWord (9, 1, 6, 0)), (-160, gapWord (9, 1, 5, 1)), (-160, gapWord (9, 0, 7, 0)), (-160, gapWord (8, 8, 0, 0)), (-320, gapWord (8, 7, 1, 0)), (-320, gapWord (8, 7, 0, 1)), (-320, gapWord (8, 6, 2, 0)), (-320, gapWord (8, 6, 1, 1)), (-240, gapWord (8, 6, 0, 2)), (-160, gapWord (8, 5, 3, 0)), (-320, gapWord (8, 5, 2, 1)), (-240, gapWord (8, 5, 1, 2)), (-160, gapWord (8, 5, 0, 3)), (-160, gapWord (8, 4, 4, 0)), (-160, gapWord (8, 4, 3, 1)), (-240, gapWord (8, 4, 2, 2)), (-160, gapWord (8, 4, 1, 3)), (-80, gapWord (8, 4, 0, 4)), (-160, gapWord (8, 3, 5, 0)),
    (-160, gapWord (8, 3, 4, 1)), (-80, gapWord (8, 3, 3, 2)), (-80, gapWord (8, 3, 2, 3)), (-320, gapWord (8, 2, 6, 0)), (-320, gapWord (8, 2, 5, 1)), (-160, gapWord (8, 2, 4, 2)), (-320, gapWord (8, 1, 7, 0)), (-160, gapWord (8, 1, 6, 1)), (-80, gapWord (8, 0, 8, 0)), (-320, gapWord (7, 7, 2, 0)), (-160, gapWord (7, 7, 1, 1)), (-160, gapWord (7, 6, 3, 0)), (-320, gapWord (7, 6, 2, 1)), (-320, gapWord (7, 6, 1, 2)), (-160, gapWord (7, 6, 0, 3)), (-160, gapWord (7, 5, 4, 0)), (-160, gapWord (7, 5, 3, 1)), (-320, gapWord (7, 5, 2, 2)), (-160, gapWord (7, 5, 1, 3)), (-160, gapWord (7, 5, 0, 4)), (-160, gapWord (7, 4, 5, 0)), (-160, gapWord (7, 4, 4, 1)), (-160, gapWord (7, 4, 3, 2)), (-160, gapWord (7, 4, 2, 3)), (-80, gapWord (7, 4, 1, 4)), (-160, gapWord (7, 3, 6, 0)), (-160, gapWord (7, 3, 5, 1)), (-160, gapWord (7, 3, 4, 2)), (-160, gapWord (7, 2, 7, 0)), (-320, gapWord (7, 2, 6, 1)), (-160, gapWord (7, 2, 5, 2)), (-80, gapWord (7, 1, 7, 1)), (-160, gapWord (6, 6, 4, 0)), (-160, gapWord (6, 6, 3, 1)), (-160, gapWord (6, 6, 2, 2)), (-160, gapWord (6, 5, 5, 0)), (-160, gapWord (6, 5, 4, 1)), (-160, gapWord (6, 5, 3, 2)), (-160, gapWord (6, 5, 2, 3)), (-160, gapWord (6, 5, 1, 4)), (-80, gapWord (6, 5, 0, 5)), (-80, gapWord (6, 4, 6, 0)), (-160, gapWord (6, 4, 5, 1)), (-160, gapWord (6, 4, 4, 2)), (-80, gapWord (6, 4, 2, 4)),
    (-80, gapWord (6, 3, 6, 1)), (-160, gapWord (6, 3, 5, 2)), (-80,
    gapWord (6, 2, 6, 2)), (-80, gapWord (5, 5, 5, 1)), (-160, gapWord (5, 5, 4, 2)), (-80, gapWord (5, 4, 5, 2))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary3 : Terms :=
  [(-240, gapWord (16, 0, 0, 0)), (-480, gapWord (15, 1, 0, 0)), (-240,
    gapWord (15, 0, 1, 0)), (-480, gapWord (14, 2, 0, 0)), (-480, gapWord (14, 1, 1, 0)), (-240, gapWord (14, 1, 0, 1)), (-240, gapWord (14, 0, 2, 0)), (-480, gapWord (13, 3, 0, 0)), (-480, gapWord (13, 2, 1, 0)), (-480, gapWord (13, 2, 0, 1)), (-480, gapWord (13, 1, 2, 0)), (-240, gapWord (13, 1, 1, 1)), (-240, gapWord (13, 0, 3, 0)),
    (-400, gapWord (12, 4, 0, 0)), (-480, gapWord (12, 3, 1, 0)), (-480,
    gapWord (12, 3, 0, 1)), (-480, gapWord (12, 2, 2, 0)), (-480, gapWord (12, 2, 1, 1)), (-240, gapWord (12, 2, 0, 2)), (-480, gapWord (12, 1, 3, 0)), (-240, gapWord (12, 1, 2, 1)), (-240, gapWord (12, 0, 4, 0)), (-320, gapWord (11, 5, 0, 0)), (-400, gapWord (11, 4, 1, 0)), (-400, gapWord (11, 4, 0, 1)), (-480, gapWord (11, 3, 2, 0)), (-480, gapWord (11, 3, 1, 1)), (-480, gapWord (11, 3, 0, 2)), (-480, gapWord (11, 2, 3, 0)), (-480, gapWord (11, 2, 2, 1)), (-240, gapWord (11, 2, 1, 2)), (-480, gapWord (11, 1, 4, 0)), (-240, gapWord (11, 1, 3, 1)), (-160, gapWord (11, 0, 5, 0)), (-320, gapWord (10, 6, 0, 0)), (-320, gapWord (10, 5, 1, 0)), (-320, gapWord (10, 5, 0, 1)), (-400, gapWord (10, 4, 2, 0)), (-400, gapWord (10, 4, 1, 1)), (-400, gapWord (10, 4, 0, 2)), (-480, gapWord (10, 3, 3, 0)), (-480, gapWord (10, 3, 2, 1)), (-480, gapWord (10, 3, 1, 2)), (-240, gapWord (10, 3, 0, 3)), (-480, gapWord (10, 2, 4, 0)), (-480, gapWord (10, 2, 3, 1)), (-240, gapWord (10, 2, 2, 2)), (-320, gapWord (10, 1, 5, 0)), (-240, gapWord (10, 1, 4, 1)), (-160, gapWord (10, 0, 6, 0)), (-320, gapWord (9, 7, 0, 0)), (-320, gapWord (9, 6, 1, 0)), (-320, gapWord (9, 6, 0, 1)), (-320, gapWord (9, 5, 2, 0)), (-320, gapWord (9, 5, 1, 1)), (-320, gapWord (9, 5, 0, 2)), (-400, gapWord (9, 4, 3, 0)), (-400, gapWord (9, 4, 2, 1)), (-400, gapWord (9, 4, 1, 2)), (-400, gapWord (9, 4, 0, 3)), (-480, gapWord (9, 3, 4, 0)), (-480, gapWord (9, 3, 3, 1)), (-480, gapWord (9, 3, 2, 2)), (-240, gapWord (9, 3, 1, 3)), (-320, gapWord (9, 2, 5, 0)), (-480, gapWord (9, 2, 4, 1)), (-240, gapWord (9, 2, 3, 2)), (-320, gapWord (9, 1, 6, 0)), (-160, gapWord (9, 1, 5, 1)), (-160, gapWord (9, 0, 7, 0)), (-160, gapWord (8, 8, 0, 0)), (-320, gapWord (8, 7, 1, 0)), (-320, gapWord (8, 7, 0, 1)), (-320, gapWord (8, 6, 2, 0)), (-320, gapWord (8, 6, 1, 1)), (-320, gapWord (8, 6, 0, 2)), (-320, gapWord (8, 5, 3, 0)), (-320, gapWord (8, 5, 2, 1)), (-320, gapWord (8, 5, 1, 2)), (-320, gapWord (8, 5, 0, 3)), (-400, gapWord (8, 4, 4, 0)), (-400, gapWord (8, 4, 3, 1)), (-400, gapWord (8, 4, 2, 2)), (-400, gapWord (8, 4, 1, 3)), (-160, gapWord (8, 4, 0, 4)), (-320, gapWord (8, 3, 5, 0)), (-480, gapWord (8, 3, 4, 1)), (-480, gapWord (8, 3, 3, 2)), (-240, gapWord (8, 3, 2, 3)), (-320, gapWord (8, 2, 6, 0)), (-320, gapWord (8, 2, 5, 1)), (-240, gapWord (8, 2, 4, 2)), (-320, gapWord (8, 1, 7, 0)), (-160, gapWord (8, 1, 6, 1)), (-80, gapWord (8, 0, 8, 0)), (-320, gapWord (7, 7, 2, 0)), (-160, gapWord (7, 7, 1, 1)), (-320, gapWord (7, 6, 3, 0)), (-320, gapWord (7, 6, 2, 1)), (-320, gapWord (7, 6, 1, 2)), (-320, gapWord (7, 6, 0, 3)), (-240, gapWord (7, 5, 4, 0)), (-320, gapWord (7, 5, 3, 1)), (-320, gapWord (7, 5, 2, 2)), (-320, gapWord (7, 5, 1, 3)), (-240, gapWord (7, 5, 0, 4)), (-240, gapWord (7, 4, 5, 0)), (-400, gapWord (7, 4, 4, 1)), (-400, gapWord (7, 4, 3, 2)), (-400, gapWord (7, 4, 2, 3)), (-160, gapWord (7, 4, 1, 4)), (-320, gapWord (7, 3, 6, 0)), (-320, gapWord (7, 3, 5, 1)), (-480, gapWord (7, 3, 4, 2)), (-240, gapWord (7, 3, 3, 3)), (-160, gapWord (7, 2, 7, 0)), (-320, gapWord (7, 2, 6, 1)), (-160, gapWord (7, 2, 5, 2)), (-80, gapWord (7, 1, 7, 1)), (-240, gapWord (6, 6, 4, 0)), (-320, gapWord (6, 6, 3, 1)), (-160, gapWord (6, 6, 2, 2)), (-160, gapWord (6, 5, 5, 0)), (-320, gapWord (6, 5, 4, 1)), (-320, gapWord (6, 5, 3, 2)), (-320, gapWord (6, 5, 2, 3)), (-240, gapWord (6, 5, 1, 4)), (-80, gapWord (6, 5, 0, 5)), (-80, gapWord (6, 4, 6, 0)), (-240, gapWord (6, 4, 5, 1)), (-400, gapWord (6, 4, 4, 2)), (-400, gapWord (6, 4, 3, 3)), (-160, gapWord (6, 4, 2, 4)), (-160, gapWord (6, 3, 6, 1)), (-320, gapWord (6, 3, 5, 2)), (-240, gapWord (6, 3, 4, 3)), (-80, gapWord (6, 2, 6, 2)), (-80, gapWord (5, 5, 5, 1)), (-320, gapWord (5, 5, 4, 2)), (-160, gapWord (5, 5, 3, 3)), (-160, gapWord (5, 4, 5, 2)), (-480, gapWord (5, 4, 4, 3)), (-240, gapWord (5, 4, 3, 4)), (-80, gapWord (5, 3, 5, 3)), (-80, gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary4 : Terms :=
  [(-240, gapWord (16, 0, 0, 0)), (-480, gapWord (15, 1, 0, 0)), (-240,
    gapWord (15, 0, 1, 0)), (-480, gapWord (14, 2, 0, 0)), (-480, gapWord (14, 1, 1, 0)), (-240, gapWord (14, 1, 0, 1)), (-240, gapWord (14, 0, 2, 0)), (-480, gapWord (13, 3, 0, 0)), (-480, gapWord (13, 2, 1, 0)), (-480, gapWord (13, 2, 0, 1)), (-480, gapWord (13, 1, 2, 0)), (-240, gapWord (13, 1, 1, 1)), (-240, gapWord (13, 0, 3, 0)),
    (-480, gapWord (12, 4, 0, 0)), (-480, gapWord (12, 3, 1, 0)), (-480,
    gapWord (12, 3, 0, 1)), (-480, gapWord (12, 2, 2, 0)), (-480, gapWord (12, 2, 1, 1)), (-240, gapWord (12, 2, 0, 2)), (-480, gapWord (12, 1, 3, 0)), (-240, gapWord (12, 1, 2, 1)), (-240, gapWord (12, 0, 4, 0)), (-480, gapWord (11, 5, 0, 0)), (-480, gapWord (11, 4, 1, 0)), (-480, gapWord (11, 4, 0, 1)), (-480, gapWord (11, 3, 2, 0)), (-480, gapWord (11, 3, 1, 1)), (-480, gapWord (11, 3, 0, 2)), (-480, gapWord (11, 2, 3, 0)), (-480, gapWord (11, 2, 2, 1)), (-240, gapWord (11, 2, 1, 2)), (-480, gapWord (11, 1, 4, 0)), (-240, gapWord (11, 1, 3, 1)), (-240, gapWord (11, 0, 5, 0)), (-480, gapWord (10, 6, 0, 0)), (-480, gapWord (10, 5, 1, 0)), (-480, gapWord (10, 5, 0, 1)), (-480, gapWord (10, 4, 2, 0)), (-480, gapWord (10, 4, 1, 1)), (-480, gapWord (10, 4, 0, 2)), (-480, gapWord (10, 3, 3, 0)), (-480, gapWord (10, 3, 2, 1)), (-480, gapWord (10, 3, 1, 2)), (-240, gapWord (10, 3, 0, 3)), (-480, gapWord (10, 2, 4, 0)), (-480, gapWord (10, 2, 3, 1)), (-240, gapWord (10, 2, 2, 2)), (-480, gapWord (10, 1, 5, 0)), (-240, gapWord (10, 1, 4, 1)), (-240, gapWord (10, 0, 6, 0)), (-400, gapWord (9, 7, 0, 0)), (-480, gapWord (9, 6, 1, 0)), (-480, gapWord (9, 6, 0, 1)), (-480, gapWord (9, 5, 2, 0)), (-480, gapWord (9, 5, 1, 1)), (-480, gapWord (9, 5, 0, 2)), (-480, gapWord (9, 4, 3, 0)), (-480, gapWord (9, 4, 2, 1)), (-480, gapWord (9, 4, 1, 2)), (-480, gapWord (9, 4, 0, 3)), (-480, gapWord (9, 3, 4, 0)), (-480, gapWord (9, 3, 3, 1)), (-480, gapWord (9, 3, 2, 2)), (-240, gapWord (9, 3, 1, 3)), (-480, gapWord (9, 2, 5, 0)), (-480, gapWord (9, 2, 4, 1)), (-240, gapWord (9, 2, 3, 2)), (-480, gapWord (9, 1, 6, 0)), (-240, gapWord (9, 1, 5, 1)), (-240, gapWord (9, 0, 7, 0)), (-160, gapWord (8, 8, 0, 0)), (-400, gapWord (8, 7, 1, 0)), (-400, gapWord (8, 7, 0, 1)), (-480, gapWord (8, 6, 2, 0)), (-480, gapWord (8, 6, 1, 1)), (-480, gapWord (8, 6, 0, 2)), (-480, gapWord (8, 5, 3, 0)), (-480, gapWord (8, 5, 2, 1)), (-480, gapWord (8, 5, 1, 2)), (-480, gapWord (8, 5, 0, 3)), (-480, gapWord (8, 4, 4, 0)), (-480, gapWord (8, 4, 3, 1)), (-480, gapWord (8, 4, 2, 2)), (-480, gapWord (8, 4, 1, 3)), (-240, gapWord (8, 4, 0, 4)), (-480, gapWord (8, 3, 5, 0)), (-480, gapWord (8, 3, 4, 1)), (-480, gapWord (8, 3, 3, 2)), (-240, gapWord (8, 3, 2, 3)), (-480, gapWord (8, 2, 6, 0)), (-480, gapWord (8, 2, 5, 1)), (-240, gapWord (8, 2, 4, 2)), (-480, gapWord (8, 1, 7, 0)), (-240, gapWord (8, 1, 6, 1)), (-80, gapWord (8, 0, 8, 0)), (-400, gapWord (7, 7, 2, 0)), (-240, gapWord (7, 7, 1, 1)), (-560, gapWord (7, 6, 3, 0)), (-560, gapWord (7, 6, 2, 1)), (-480, gapWord (7, 6, 1, 2)), (-480, gapWord (7, 6, 0, 3)), (-560, gapWord (7, 5, 4, 0)), (-560, gapWord (7, 5, 3, 1)), (-480, gapWord (7, 5, 2, 2)), (-480, gapWord (7, 5, 1, 3)), (-480, gapWord (7, 5, 0, 4)), (-560, gapWord (7, 4, 5, 0)), (-560, gapWord (7, 4, 4, 1)), (-480, gapWord (7, 4, 3, 2)), (-480, gapWord (7, 4, 2, 3)), (-240, gapWord (7, 4, 1, 4)), (-560, gapWord (7, 3, 6, 0)), (-560, gapWord (7, 3, 5, 1)), (-480, gapWord (7, 3, 4, 2)), (-240, gapWord (7, 3, 3, 3)), (-240, gapWord (7, 2, 7, 0)), (-560, gapWord (7, 2, 6, 1)), (-240, gapWord (7, 2, 5, 2)), (-160, gapWord (7, 1, 7, 1)), (-640, gapWord (6, 6, 4, 0)), (-640, gapWord (6, 6, 3, 1)), (-320, gapWord (6, 6, 2, 2)), (-640, gapWord (6, 5, 5, 0)), (-640, gapWord (6, 5, 4, 1)), (-640, gapWord (6, 5, 3, 2)), (-640, gapWord (6, 5, 2, 3)), (-640, gapWord (6, 5, 1, 4)), (-320, gapWord (6, 5, 0, 5)), (-320, gapWord (6, 4, 6, 0)), (-640, gapWord (6, 4, 5, 1)), (-640, gapWord (6, 4, 4, 2)), (-640, gapWord (6, 4, 3, 3)), (-320, gapWord (6, 4, 2, 4)), (-320, gapWord (6, 3, 6, 1)), (-640, gapWord (6, 3, 5, 2)), (-320, gapWord (6, 3, 4, 3)), (-160, gapWord (6, 2, 6, 2)), (-320, gapWord (5, 5, 5, 1)), (-640, gapWord (5, 5, 4, 2)), (-320, gapWord (5, 5, 3, 3)), (-320, gapWord (5, 4, 5, 2)), (-640, gapWord (5, 4, 4, 3)), (-320, gapWord (5, 4, 3, 4)), (-160, gapWord (5, 3, 5, 3)), (-80, gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary5 : Terms :=
  [(-240, gapWord (16, 0, 0, 0)), (-480, gapWord (15, 1, 0, 0)), (-240,
    gapWord (15, 0, 1, 0)), (-560, gapWord (14, 2, 0, 0)), (-480, gapWord (14, 1, 1, 0)), (-240, gapWord (14, 1, 0, 1)), (-240, gapWord (14, 0, 2, 0)), (-640, gapWord (13, 3, 0, 0)), (-640, gapWord (13, 2, 1, 0)), (-640, gapWord (13, 2, 0, 1)), (-640, gapWord (13, 1, 2, 0)), (-320, gapWord (13, 1, 1, 1)), (-320, gapWord (13, 0, 3, 0)),
    (-640, gapWord (12, 4, 0, 0)), (-640, gapWord (12, 3, 1, 0)), (-640,
    gapWord (12, 3, 0, 1)), (-640, gapWord (12, 2, 2, 0)), (-640, gapWord (12, 2, 1, 1)), (-320, gapWord (12, 2, 0, 2)), (-640, gapWord (12, 1, 3, 0)), (-320, gapWord (12, 1, 2, 1)), (-320, gapWord (12, 0, 4, 0)), (-640, gapWord (11, 5, 0, 0)), (-640, gapWord (11, 4, 1, 0)), (-640, gapWord (11, 4, 0, 1)), (-640, gapWord (11, 3, 2, 0)), (-640, gapWord (11, 3, 1, 1)), (-640, gapWord (11, 3, 0, 2)), (-640, gapWord (11, 2, 3, 0)), (-640, gapWord (11, 2, 2, 1)), (-320, gapWord (11, 2, 1, 2)), (-640, gapWord (11, 1, 4, 0)), (-320, gapWord (11, 1, 3, 1)), (-320, gapWord (11, 0, 5, 0)), (-640, gapWord (10, 6, 0, 0)), (-640, gapWord (10, 5, 1, 0)), (-640, gapWord (10, 5, 0, 1)), (-640, gapWord (10, 4, 2, 0)), (-640, gapWord (10, 4, 1, 1)), (-640, gapWord (10, 4, 0, 2)), (-640, gapWord (10, 3, 3, 0)), (-640, gapWord (10, 3, 2, 1)), (-640, gapWord (10, 3, 1, 2)), (-320, gapWord (10, 3, 0, 3)), (-640, gapWord (10, 2, 4, 0)), (-640, gapWord (10, 2, 3, 1)), (-320, gapWord (10, 2, 2, 2)), (-640, gapWord (10, 1, 5, 0)), (-320, gapWord (10, 1, 4, 1)), (-320, gapWord (10, 0, 6, 0)), (-640, gapWord (9, 7, 0, 0)), (-640, gapWord (9, 6, 1, 0)), (-640, gapWord (9, 6, 0, 1)), (-640, gapWord (9, 5, 2, 0)), (-640, gapWord (9, 5, 1, 1)), (-640, gapWord (9, 5, 0, 2)), (-640, gapWord (9, 4, 3, 0)), (-640, gapWord (9, 4, 2, 1)), (-640, gapWord (9, 4, 1, 2)), (-640, gapWord (9, 4, 0, 3)), (-640, gapWord (9, 3, 4, 0)), (-640, gapWord (9, 3, 3, 1)), (-640, gapWord (9, 3, 2, 2)), (-320, gapWord (9, 3, 1, 3)), (-640, gapWord (9, 2, 5, 0)), (-640, gapWord (9, 2, 4, 1)), (-320, gapWord (9, 2, 3, 2)), (-640, gapWord (9, 1, 6, 0)), (-320, gapWord (9, 1, 5, 1)), (-320, gapWord (9, 0, 7, 0)), (-320, gapWord (8, 8, 0, 0)), (-640, gapWord (8, 7, 1, 0)), (-640, gapWord (8, 7, 0, 1)), (-640, gapWord (8, 6, 2, 0)), (-640, gapWord (8, 6, 1, 1)), (-640, gapWord (8, 6, 0, 2)), (-640, gapWord (8, 5, 3, 0)), (-640, gapWord (8, 5, 2, 1)), (-640, gapWord (8, 5, 1, 2)), (-640, gapWord (8, 5, 0, 3)), (-640, gapWord (8, 4, 4, 0)), (-640, gapWord (8, 4, 3, 1)), (-640, gapWord (8, 4, 2, 2)), (-640, gapWord (8, 4, 1, 3)), (-320, gapWord (8, 4, 0, 4)), (-640, gapWord (8, 3, 5, 0)), (-640, gapWord (8, 3, 4, 1)), (-640, gapWord (8, 3, 3, 2)), (-320, gapWord (8, 3, 2, 3)), (-640, gapWord (8, 2, 6, 0)), (-640, gapWord (8, 2, 5, 1)), (-320, gapWord (8, 2, 4, 2)), (-640, gapWord (8, 1, 7, 0)), (-320, gapWord (8, 1, 6, 1)), (-160, gapWord (8, 0, 8, 0)), (-640, gapWord (7, 7, 2, 0)), (-320, gapWord (7, 7, 1, 1)), (-640, gapWord (7, 6, 3, 0)), (-640, gapWord (7, 6, 2, 1)), (-640, gapWord (7, 6, 1, 2)), (-640, gapWord (7, 6, 0, 3)), (-640, gapWord (7, 5, 4, 0)), (-640, gapWord (7, 5, 3, 1)), (-640, gapWord (7, 5, 2, 2)), (-640, gapWord (7, 5, 1, 3)), (-640, gapWord (7, 5, 0, 4)), (-640, gapWord (7, 4, 5, 0)), (-640, gapWord (7, 4, 4, 1)), (-640, gapWord (7, 4, 3, 2)), (-640, gapWord (7, 4, 2, 3)), (-320, gapWord (7, 4, 1, 4)), (-640, gapWord (7, 3, 6, 0)), (-640, gapWord (7, 3, 5, 1)), (-640, gapWord (7, 3, 4, 2)), (-320, gapWord (7, 3, 3, 3)), (-320, gapWord (7, 2, 7, 0)), (-640, gapWord (7, 2, 6, 1)), (-320, gapWord (7, 2, 5, 2)), (-160, gapWord (7, 1, 7, 1)), (-640, gapWord (6, 6, 4, 0)), (-640, gapWord (6, 6, 3, 1)), (-320, gapWord (6, 6, 2, 2)), (-640, gapWord (6, 5, 5, 0)), (-640, gapWord (6, 5, 4, 1)), (-640, gapWord (6, 5, 3, 2)), (-640, gapWord (6, 5, 2, 3)), (-640, gapWord (6, 5, 1, 4)), (-320, gapWord (6, 5, 0, 5)), (-320, gapWord (6, 4, 6, 0)), (-640, gapWord (6, 4, 5, 1)), (-640, gapWord (6, 4, 4, 2)), (-640, gapWord (6, 4, 3, 3)), (-320, gapWord (6, 4, 2, 4)), (-320, gapWord (6, 3, 6, 1)), (-640, gapWord (6, 3, 5, 2)), (-320, gapWord (6, 3, 4, 3)), (-160, gapWord (6, 2, 6, 2)), (-320, gapWord (5, 5, 5, 1)), (-640, gapWord (5, 5, 4, 2)), (-320, gapWord (5, 5, 3, 3)), (-320, gapWord (5, 4, 5, 2)), (-640, gapWord (5, 4, 4, 3)), (-320, gapWord (5, 4, 3, 4)), (-160, gapWord (5, 3, 5, 3)), (-80, gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary6 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-8791332717107903 / 18408219104000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-8791332717107903 / 9204109552000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((-353851 / 1000), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-8791332717107903 / 9204109552000), gapWord (13, 2, 1, 0)),
    ((-68417 / 500), gapWord (13, 2, 0, 1)), ((-353851 / 500), gapWord (13, 1, 2, 0)), ((-8791332717107903 / 18408219104000), gapWord (13, 1, 1, 1)),
    ((-3074028966406839 / 9204109552000), gapWord (13, 0, 3, 0)), ((-199259 / 500),
    gapWord (12, 4, 0, 0)), ((-8827780990933823 / 9204109552000), gapWord (12, 3, 1, 0)), ((-68417 / 500), gapWord (12, 3, 0, 1)), ((-704149 / 1000), gapWord (12, 2, 2, 0)), ((-8791332717107903 / 9204109552000), gapWord (12, 2, 1, 1)), ((-68417 / 1000), gapWord (12, 2, 0, 2)), ((-3109869769002327 /
    4602054776000), gapWord (12, 1, 3, 0)), ((-353851 / 1000), gapWord (12, 1, 2, 1)), ((-313186853753743 / 1150513694000), gapWord (12, 0, 4, 0)), ((-98111 /
    250), gapWord (11, 5, 0, 0)), ((-253481319369931 / 418368616000), gapWord (11, 4, 1, 0)), ((-199259 / 500), gapWord (11, 4, 0, 1)), ((-3015918642904153 /
    4602054776000), gapWord (11, 3, 2, 0)), ((-8827780990933823 / 9204109552000),
    gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)),
    ((-7850184001674409 / 9204109552000), gapWord (11, 2, 3, 0)), ((-704149 / 1000),
    gapWord (11, 2, 2, 1)), ((-8791332717107903 / 18408219104000), gapWord (11, 2, 1, 2)), ((-140817788340797 / 209184308000), gapWord (11, 1, 4, 0)),
    ((-629142114319563 / 1840821910400), gapWord (11, 1, 3, 1)), ((-328019327365327 /
    920410955200), gapWord (11, 0, 5, 0)), ((-193707 / 500), gapWord (10, 6, 0, 0)), ((-1265209464754467 / 2301027388000), gapWord (10, 5, 1, 0)),
    ((-98111 / 250), gapWord (10, 5, 0, 1)), ((-305478262809491 / 418368616000),
    gapWord (10, 4, 2, 0)), ((-253481319369931 / 418368616000), gapWord (10, 4, 1, 1)), ((-199259 / 500), gapWord (10, 4, 0, 2)), ((-7623288970016567 /
    9204109552000), gapWord (10, 3, 3, 0)), ((-3015918642904153 / 4602054776000),
    gapWord (10, 3, 2, 1)), ((-8827780990933823 / 9204109552000), gapWord (10, 3, 1, 2)), ((-68417 / 1000), gapWord (10, 3, 0, 3)), ((-3309118560407959 /
    4602054776000), gapWord (10, 2, 4, 0)), ((-1584373121373077 / 1840821910400),
    gapWord (10, 2, 3, 1)), ((-175149 / 500), gapWord (10, 2, 2, 2)),
    ((-3322902394437899 / 4602054776000), gapWord (10, 1, 5, 0)), ((-922621964241281 /
    2301027388000), gapWord (10, 1, 4, 1)), ((-45708 / 125), gapWord (10, 0, 6, 0)), ((-195413 / 500), gapWord (9, 7, 0, 0)), ((-5582754156456487 /
    9204109552000), gapWord (9, 6, 1, 0)), ((-193707 / 500), gapWord (9, 6, 0, 1)), ((-26483103298222151 / 36816438208000), gapWord (9, 5, 2, 0)),
    ((-1265209464754467 / 2301027388000), gapWord (9, 5, 1, 1)), ((-98111 / 250),
    gapWord (9, 5, 0, 2)), ((-1732726901115461 / 2301027388000), gapWord (9, 4, 3, 0)), ((-305478262809491 / 418368616000), gapWord (9, 4, 2, 1)),
    ((-253481319369931 / 418368616000), gapWord (9, 4, 1, 2)), ((-199259 / 500),
    gapWord (9, 4, 0, 3)), ((-806796345945339 / 1150513694000), gapWord (9, 3, 4, 0)), ((-7694970575207543 / 9204109552000), gapWord (9, 3, 3, 1)),
    ((-119982701691401 / 184082191040), gapWord (9, 3, 2, 2)), ((-8864229264759743 /
    18408219104000), gapWord (9, 3, 1, 3)), ((-80647432930781113 / 110449314624000),
    gapWord (9, 2, 5, 0)), ((-3901615073875549 / 4602054776000), gapWord (9, 2, 4, 1)), ((-477615503526757 / 920410955200), gapWord (9, 2, 3, 2)),
    ((-2816291442400421 / 3808597056000), gapWord (9, 1, 6, 0)), ((-45708 / 125),
    gapWord (9, 1, 5, 1)), ((-1423624608515237 / 3808597056000), gapWord (9, 0, 7, 0)), ((-97379 / 500), gapWord (8, 8, 0, 0)), ((-523344291292731 /
    920410955200), gapWord (8, 7, 1, 0)), ((-195413 / 500), gapWord (8, 7, 0, 1)), ((-2553389530301201 / 4602054776000), gapWord (8, 6, 2, 0)),
    ((-5582754156456487 / 9204109552000), gapWord (8, 6, 1, 1)), ((-193707 / 500),
    gapWord (8, 6, 0, 2)), ((-5525132978716827 / 9204109552000), gapWord (8, 5, 3, 0)), ((-26483103298222151 / 36816438208000), gapWord (8, 5, 2, 1)),
    ((-1265209464754467 / 2301027388000), gapWord (8, 5, 1, 2)), ((-98111 / 250), gapWord (8, 5, 0, 3)), ((-1628089981673549 / 2301027388000), gapWord (8, 4, 4, 0)), ((-1732726901115461 / 2301027388000), gapWord (8, 4, 3, 1)),
    ((-305478262809491 / 418368616000), gapWord (8, 4, 2, 2)), ((-253481319369931 /
    418368616000), gapWord (8, 4, 1, 3)), (-320, gapWord (8, 4, 0, 4)),
    ((-638600499060627 / 920410955200), gapWord (8, 3, 5, 0)), ((-1909840948624473 /
    2301027388000), gapWord (8, 3, 4, 1)), ((-4662707519438649 / 4602054776000),
    gapWord (8, 3, 3, 2)), ((-1387476958361777 / 4602054776000), gapWord (8, 3, 2, 3)), ((-720539 / 1000), gapWord (8, 2, 6, 0)), ((-2816291442400421 /
    3808597056000), gapWord (8, 2, 5, 1)), ((-2056371145392987 / 4602054776000),
    gapWord (8, 2, 4, 2)), ((-2775200488763237 / 3808597056000), gapWord (8, 1, 7, 0)), ((-1423624608515237 / 3808597056000), gapWord (8, 1, 6, 1)),
    ((-2839 / 16), gapWord (8, 0, 8, 0)), ((-195413 / 500), gapWord (7, 7, 2, 0)), ((-1720434472399447 / 4602054776000), gapWord (7, 7, 1, 1)), ((-195413
    / 500), gapWord (7, 6, 3, 0)), ((-7676220496901 / 10459215400), gapWord (7, 6, 2, 1)), ((-5582754156456487 / 9204109552000), gapWord (7, 6, 1, 2)),
    ((-193707 / 500), gapWord (7, 6, 0, 3)), (-640, gapWord (7, 5, 4, 0)), ((-1434685591077461 / 1840821910400), gapWord (7, 5, 3, 1)),
    ((-26483103298222151 / 36816438208000), gapWord (7, 5, 2, 2)),
    ((-1265209464754467 / 2301027388000), gapWord (7, 5, 1, 3)), (-640, gapWord (7, 5, 0, 4)), (-640, gapWord (7, 4, 5, 0)), ((-1628089981673549 /
    2301027388000), gapWord (7, 4, 4, 1)), ((-1732726901115461 / 2301027388000),
    gapWord (7, 4, 3, 2)), ((-305478262809491 / 418368616000), gapWord (7, 4, 2, 3)), (-320, gapWord (7, 4, 1, 4)), ((-85708 / 125), gapWord (7, 3, 6, 0)), ((-1406203 / 2000), gapWord (7, 3, 5, 1)), ((-4030809114159371 /
    4602054776000), gapWord (7, 3, 4, 2)), ((-61783 / 125), gapWord (7, 3, 3, 3)), ((-1423624608515237 / 3808597056000), gapWord (7, 2, 7, 0)),
    ((-2775200488763237 / 3808597056000), gapWord (7, 2, 6, 1)), ((-1423624608515237 /
    3808597056000), gapWord (7, 2, 5, 2)), ((-2839 / 16), gapWord (7, 1, 7, 1)), (-640, gapWord (6, 6, 4, 0)), ((-5582754156456487 / 9204109552000),
    gapWord (6, 6, 3, 1)), ((-1657102546236993 / 4602054776000), gapWord (6, 6, 2, 2)), (-640, gapWord (6, 5, 5, 0)), (-640, gapWord (6, 5, 4, 1)), ((-7046764103062397 / 9204109552000), gapWord (6, 5, 3, 2)),
    ((-26483103298222151 / 36816438208000), gapWord (6, 5, 2, 3)), (-640, gapWord (6, 5, 1, 4)), (-320, gapWord (6, 5, 0, 5)), (-320, gapWord (6, 4, 6, 0)), (-640, gapWord (6, 4, 5, 1)), ((-1628089981673549 /
    2301027388000), gapWord (6, 4, 4, 2)), ((-1732726901115461 / 2301027388000),
    gapWord (6, 4, 3, 3)), (-320, gapWord (6, 4, 2, 4)),
    ((-1423624608515237 / 3808597056000), gapWord (6, 3, 6, 1)), ((-2775200488763237 /
    3808597056000), gapWord (6, 3, 5, 2)), ((-214517 / 500), gapWord (6, 3, 4, 3)), ((-2839 / 16), gapWord (6, 2, 6, 2)), (-320, gapWord (5, 5, 5, 1)), (-640, gapWord (5, 5, 4, 2)), ((-3732559010588411 / 9204109552000),
    gapWord (5, 5, 3, 3)), (-320, gapWord (5, 4, 5, 2)),
    ((87559731577206451 / 2301027388000), gapWord (5, 4, 4, 3)), (19060, gapWord (5, 4, 3, 4)), ((152201 / 16), gapWord (5, 3, 5, 3)), (9610, gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary7 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-8791332717107903 / 18408219104000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-8791332717107903 / 9204109552000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((-353851 / 1000), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-8791332717107903 / 9204109552000), gapWord (13, 2, 1, 0)),
    ((-68417 / 500), gapWord (13, 2, 0, 1)), ((-353851 / 500), gapWord (13, 1, 2, 0)), ((-8791332717107903 / 18408219104000), gapWord (13, 1, 1, 1)),
    ((-3074028966406839 / 9204109552000), gapWord (13, 0, 3, 0)), ((-39259 / 250),
    gapWord (12, 4, 0, 0)), ((-8827780990933823 / 9204109552000), gapWord (12, 3, 1, 0)), ((-68417 / 500), gapWord (12, 3, 0, 1)), ((-704149 / 1000), gapWord (12, 2, 2, 0)), ((-8791332717107903 / 9204109552000), gapWord (12, 2, 1, 1)), ((-68417 / 1000), gapWord (12, 2, 0, 2)), ((-3109869769002327 /
    4602054776000), gapWord (12, 1, 3, 0)), ((-353851 / 1000), gapWord (12, 1, 2, 1)), ((-313186853753743 / 1150513694000), gapWord (12, 0, 4, 0)), ((-18111 /
    125), gapWord (11, 5, 0, 0)), ((-294946669638923 / 418368616000), gapWord (11, 4, 1, 0)), ((-39259 / 250), gapWord (11, 4, 0, 1)), ((-3015918642904153 /
    4602054776000), gapWord (11, 3, 2, 0)), ((-8827780990933823 / 9204109552000),
    gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)),
    ((-7850184001674409 / 9204109552000), gapWord (11, 2, 3, 0)), ((-704149 / 1000),
    gapWord (11, 2, 2, 1)), ((-8791332717107903 / 18408219104000), gapWord (11, 2, 1, 2)), ((-140817788340797 / 209184308000), gapWord (11, 1, 4, 0)),
    ((-629142114319563 / 1840821910400), gapWord (11, 1, 3, 1)), ((-328019327365327 /
    920410955200), gapWord (11, 0, 5, 0)), ((-33707 / 250), gapWord (10, 6, 0, 0)), ((-75889754603061 / 143814211750), gapWord (10, 5, 1, 0)), ((-18111 / 125),
    gapWord (10, 5, 0, 1)), ((-307524922078963 / 418368616000), gapWord (10, 4, 2, 0)), ((-294946669638923 / 418368616000), gapWord (10, 4, 1, 1)), ((-39259 /
    250), gapWord (10, 4, 0, 2)), ((-7623288970016567 / 9204109552000), gapWord (10, 3, 3, 0)), ((-3015918642904153 / 4602054776000), gapWord (10, 3, 2, 1)), ((-8827780990933823 / 9204109552000), gapWord (10, 3, 1, 2)), ((-68417 /
    1000), gapWord (10, 3, 0, 3)), ((-3309118560407959 / 4602054776000), gapWord (10, 2, 4, 0)), ((-1584373121373077 / 1840821910400), gapWord (10, 2, 3, 1)), ((-175149 / 500), gapWord (10, 2, 2, 2)), ((-3322902394437899 /
    4602054776000), gapWord (10, 1, 5, 0)), ((-922621964241281 / 2301027388000),
    gapWord (10, 1, 4, 1)), ((-45708 / 125), gapWord (10, 0, 6, 0)), ((-35413 /
    250), gapWord (9, 7, 0, 0)), ((-5030433950460071 / 9204109552000), gapWord (9, 6, 1, 0)), ((-33707 / 250), gapWord (9, 6, 0, 1)), ((-25631612715347527 /
    36816438208000), gapWord (9, 5, 2, 0)), ((-75889754603061 / 143814211750), gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-334528494792001 / 460205477600), gapWord (9, 4, 3, 0)), ((-307524922078963 /
    418368616000), gapWord (9, 4, 2, 1)), ((-294946669638923 / 418368616000), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)),
    ((-806796345945339 / 1150513694000), gapWord (9, 3, 4, 0)), ((-7694970575207543 /
    9204109552000), gapWord (9, 3, 3, 1)), ((-119982701691401 / 184082191040),
    gapWord (9, 3, 2, 2)), ((-8864229264759743 / 18408219104000), gapWord (9, 3, 1, 3)), ((-80647432930781113 / 110449314624000), gapWord (9, 2, 5, 0)),
    ((-3901615073875549 / 4602054776000), gapWord (9, 2, 4, 1)), ((-477615503526757 /
    920410955200), gapWord (9, 2, 3, 2)), ((-2816291442400421 / 3808597056000),
    gapWord (9, 1, 6, 0)), ((-45708 / 125), gapWord (9, 1, 5, 1)),
    ((-1423624608515237 / 3808597056000), gapWord (9, 0, 7, 0)), ((-17379 / 250),
    gapWord (8, 8, 0, 0)), ((-217287 / 500), gapWord (8, 7, 1, 0)),
    ((-35413 / 250), gapWord (8, 7, 0, 1)), ((-1628450153201617 / 4602054776000),
    gapWord (8, 6, 2, 0)), ((-5030433950460071 / 9204109552000), gapWord (8, 6, 1, 1)), ((-33707 / 250), gapWord (8, 6, 0, 2)), ((-3279532738438971 /
    9204109552000), gapWord (8, 5, 3, 0)), ((-25631612715347527 / 36816438208000),
    gapWord (8, 5, 2, 1)), ((-75889754603061 / 143814211750), gapWord (8, 5, 1, 2)), ((-18111 / 125), gapWord (8, 5, 0, 3)), ((-579070003703453 /
    2301027388000), gapWord (8, 4, 4, 0)), ((-1464979354247781 / 2301027388000),
    gapWord (8, 4, 3, 1)), ((-300725595331731 / 418368616000), gapWord (8, 4, 2, 2)), ((-4515693472816871 / 9204109552000), gapWord (8, 4, 1, 3)), ((52239 /
    125), gapWord (8, 4, 0, 4)), ((-1998371203193011 / 4602054776000), gapWord (8, 3, 5, 0)), ((-1909840948624473 / 2301027388000), gapWord (8, 3, 4, 1)), ((-4662707519438649 / 4602054776000), gapWord (8, 3, 3, 2)),
    ((-1387476958361777 / 4602054776000), gapWord (8, 3, 2, 3)), ((90677 / 1000), gapWord (8, 2, 6, 0)), ((-2816291442400421 / 3808597056000), gapWord (8, 2, 5, 1)), ((-2056371145392987 / 4602054776000), gapWord (8, 2, 4, 2)),
    ((2801499664514203 / 3808597056000), gapWord (8, 1, 7, 0)), ((-1423624608515237 /
    3808597056000), gapWord (8, 1, 6, 1)), ((1264994114837369 / 1150513694000),
    gapWord (8, 0, 8, 0)), ((-9759 / 50), gapWord (7, 7, 2, 0)), ((-182529
    / 500), gapWord (7, 7, 1, 1)), ((-138978323503739 / 920410955200), gapWord (7, 6, 3, 0)), ((-2988550625810209 / 4602054776000), gapWord (7, 6, 2, 1)), ((-5523111526559527 / 9204109552000), gapWord (7, 6, 1, 2)), ((-2812 /
    125), gapWord (7, 6, 0, 3)), ((-388984934629911 / 1150513694000), gapWord (7, 5, 4, 0)), ((-6408252733973803 / 9204109552000), gapWord (7, 5, 3, 1)), ((-26434211068281927 / 36816438208000), gapWord (7, 5, 2, 2)),
    ((-525302344265453 / 1150513694000), gapWord (7, 5, 1, 3)), ((28118 / 125), gapWord (7, 5, 0, 4)), ((-18099171564628783 / 27612328656000), gapWord (7, 4, 5, 0)), ((-1712869034757021 / 2301027388000), gapWord (7, 4, 4, 1)),
    ((-1477128778856421 / 2301027388000), gapWord (7, 4, 3, 2)), ((-812380371852947 /
    418368616000), gapWord (7, 4, 2, 3)), ((-23693 / 25), gapWord (7, 4, 1, 4)), ((1331485231225823 / 761719411200), gapWord (7, 3, 6, 0)), ((-328203 /
    1000), gapWord (7, 3, 5, 1)), ((-6898220587551243 / 4602054776000), gapWord (7, 3, 4, 2)), ((-196497 / 125), gapWord (7, 3, 3, 3)), ((5879893449952603 /
    3808597056000), gapWord (7, 2, 7, 0)), ((-6023019714237797 / 3808597056000),
    gapWord (7, 2, 6, 1)), ((-4436042067152549 / 3808597056000), gapWord (7, 2, 5, 2)), ((-747340888982051 / 1150513694000), gapWord (7, 1, 7, 1)), ((-8113 /
    125), gapWord (6, 6, 4, 0)), ((-5447240909698389 / 9204109552000), gapWord (6, 6, 3, 1)), ((-246431602466141 / 920410955200), gapWord (6, 6, 2, 2)),
    ((335613 / 250), gapWord (6, 5, 5, 0)), ((-67433 / 125), gapWord (6, 5, 4, 1)), ((-262215740420773 / 368164382080), gapWord (6, 5, 3, 2)),
    ((-56605019897374463 / 36816438208000), gapWord (6, 5, 2, 3)), ((-85648 / 125),
    gapWord (6, 5, 1, 4)), ((124486 / 125), gapWord (6, 5, 0, 5)), ((39959 /
    25), gapWord (6, 4, 6, 0)), ((-8655976062906031 / 27612328656000), gapWord (6, 4, 5, 1)), ((-3436025608644253 / 2301027388000), gapWord (6, 4, 4, 2)), ((-6116957220457829 / 2301027388000), gapWord (6, 4, 3, 3)), ((-134182 /
    125), gapWord (6, 4, 2, 4)), ((-61572607483227793 / 110449314624000), gapWord (6, 3, 6, 1)), ((-8645223552905573 / 3808597056000), gapWord (6, 3, 5, 2)), ((-616757 / 500), gapWord (6, 3, 4, 3)), ((-126646376389127 /
    158691544000), gapWord (6, 2, 6, 2)), ((-597 / 2), gapWord (5, 5, 5, 1)), ((-212634 / 125), gapWord (5, 5, 4, 2)), ((-7906438610229371 /
    9204109552000), gapWord (5, 5, 3, 3)), ((-19519107953434927 / 27612328656000),
    gapWord (5, 4, 5, 2)), ((17944677 / 500), gapWord (5, 4, 4, 3)),
    ((2237897 / 125), gapWord (5, 4, 3, 4)), ((4368699 / 500), gapWord (5, 3, 5, 3)), ((1166939 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary8 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((344781 / 1000), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)),
    ((-68417 / 500), gapWord (13, 2, 0, 1)), ((344781 / 500), gapWord (13, 1, 2, 0)), ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)),
    ((-3673731928376951 / 9204109552000), gapWord (13, 0, 3, 0)), ((-39259 / 250),
    gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 / 500), gapWord (12, 3, 0, 1)), ((138623 / 200), gapWord (12, 2, 2, 0)), ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000), gapWord (12, 2, 0, 2)), ((-3709572730972439 /
    4602054776000), gapWord (12, 1, 3, 0)), ((344781 / 1000), gapWord (12, 1, 2, 1)), ((-82998701901683 / 230102738800), gapWord (12, 0, 4, 0)), ((-18111 /
    125), gapWord (11, 5, 0, 0)), ((-67282403981583 / 83673723200), gapWord (11, 4, 1, 0)), ((-39259 / 250), gapWord (11, 4, 0, 1)), ((2049949621640231 /
    4602054776000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000),
    gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)),
    ((-9164905733336079 / 9204109552000), gapWord (11, 2, 3, 0)), ((138623 / 200),
    gapWord (11, 2, 2, 1)), ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)), ((-153042519300317 / 209184308000), gapWord (11, 1, 4, 0)),
    ((-3745413533567927 / 9204109552000), gapWord (11, 1, 3, 1)), ((-2475167088260491 /
    4602054776000), gapWord (11, 0, 5, 0)), ((-33707 / 250), gapWord (10, 6, 0, 0)), ((-232652536508697 / 460205477600), gapWord (10, 5, 1, 0)), ((-18111 / 125),
    gapWord (10, 5, 0, 1)), ((-207387 / 500), gapWord (10, 4, 2, 0)),
    ((-67282403981583 / 83673723200), gapWord (10, 4, 1, 1)), ((-39259 / 250), gapWord (10, 4, 0, 2)), ((-5964231579708959 / 9204109552000), gapWord (10, 3, 3, 0)), ((2049949621640231 / 4602054776000), gapWord (10, 3, 2, 1)),
    ((-5882465934293823 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((-647148679811883 / 920410955200), gapWord (10, 2, 4, 0)), ((-1847317467705411 / 1840821910400), gapWord (10, 2, 3, 1)), ((174167 /
    500), gapWord (10, 2, 2, 2)), ((-1025707875241451 / 920410955200), gapWord (10, 1, 5, 0)), ((-853480693286657 / 2301027388000), gapWord (10, 1, 4, 1)), ((-554950036947817 / 1150513694000), gapWord (10, 0, 6, 0)), ((-35413 / 250),
    gapWord (9, 7, 0, 0)), ((-895622748892731 / 1840821910400), gapWord (9, 6, 1, 0)), ((-33707 / 250), gapWord (9, 6, 0, 1)), ((-23224701251061319 /
    36816438208000), gapWord (9, 5, 2, 0)), ((-232652536508697 / 460205477600),
    gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-1664156284953061 / 2301027388000), gapWord (9, 4, 3, 0)), ((-207387 / 500),
    gapWord (9, 4, 2, 1)), ((-67282403981583 / 83673723200), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)), ((-999907768455851 /
    1150513694000), gapWord (9, 3, 4, 0)), ((-1207182636979987 / 1840821910400),
    gapWord (9, 3, 3, 1)), ((2066300722259359 / 4602054776000), gapWord (9, 3, 2, 2)), ((-5918914208119743 / 9204109552000), gapWord (9, 3, 1, 3)),
    ((-20154492071957957 / 22089862924800), gapWord (9, 2, 5, 0)), ((-3282730747599069 /
    4602054776000), gapWord (9, 2, 4, 1)), ((-62399702329081 / 104592154000), gapWord (9, 2, 3, 2)), ((-94497802881855121 / 110449314624000), gapWord (9, 1, 6, 0)), ((-663343071986691 / 1150513694000), gapWord (9, 1, 5, 1)),
    ((-1421468942581541 / 3808597056000), gapWord (9, 0, 7, 0)), ((-17379 / 500),
    gapWord (8, 8, 0, 0)), ((-348524190130021 / 920410955200), gapWord (8, 7, 1, 0)), ((-34863 / 250), gapWord (8, 7, 0, 1)), ((-1820420266127681 /
    4602054776000), gapWord (8, 6, 2, 0)), ((-891572940689851 / 1840821910400),
    gapWord (8, 6, 1, 1)), ((-33707 / 250), gapWord (8, 6, 0, 2)),
    ((-1009789833386911 / 1840821910400), gapWord (8, 5, 3, 0)), ((-23143705087003719 /
    36816438208000), gapWord (8, 5, 2, 1)), ((-232652536508697 / 460205477600),
    gapWord (8, 5, 1, 2)), ((-18111 / 125), gapWord (8, 5, 0, 3)), ((-241519
    / 500), gapWord (8, 4, 4, 0)), ((-2108751592752869 / 2301027388000), gapWord (8, 4, 3, 1)), ((-219559 / 500), gapWord (8, 4, 2, 2)),
    ((-376150717073963 / 460205477600), gapWord (8, 4, 1, 3)), ((-12089 / 250), gapWord (8, 4, 0, 4)), ((-3075693818035507 / 4602054776000), gapWord (8, 3, 5, 0)), ((-1583628897882489 / 2301027388000), gapWord (8, 3, 4, 1)),
    ((-165259846551401 / 143814211750), gapWord (8, 3, 3, 2)), ((456879330106191 /
    4602054776000), gapWord (8, 3, 2, 3)), ((-558062525601941 / 8283698596800),
    gapWord (8, 2, 6, 0)), ((-13440702732328211 / 10040846784000), gapWord (8, 2, 5, 1)), ((-4516799904669299 / 4602054776000), gapWord (8, 2, 4, 2)),
    ((69063689089079873 / 66269588774400), gapWord (8, 1, 7, 0)), ((-24399878525625821 /
    22089862924800), gapWord (8, 1, 6, 1)), ((82927755218270027 / 82836985968000),
    gapWord (8, 0, 8, 0)), ((-51369 / 250), gapWord (7, 7, 2, 0)),
    ((-1582662730745897 / 4602054776000), gapWord (7, 7, 1, 1)), ((-48357 / 125), gapWord (7, 6, 3, 0)), ((-324312477696937 / 460205477600), gapWord (7, 6, 2, 1)), ((-5065556832510503 / 9204109552000), gapWord (7, 6, 1, 2)), ((-2812 /
    125), gapWord (7, 6, 0, 3)), ((-775327433075111 / 1150513694000), gapWord (7, 5, 4, 0)), ((-165318546501499 / 167347446400), gapWord (7, 5, 3, 1)),
    ((-24406361651785287 / 36816438208000), gapWord (7, 5, 2, 2)),
    ((-320731805362701 / 1150513694000), gapWord (7, 5, 1, 3)), ((28118 / 125), gapWord (7, 5, 0, 4)), ((-102394 / 125), gapWord (7, 4, 5, 0)), ((-504079 / 500),
    gapWord (7, 4, 4, 1)), ((-1659683087710789 / 2301027388000), gapWord (7, 4, 3, 2)), ((-651307 / 500), gapWord (7, 4, 2, 3)), ((-23693 / 25), gapWord (7, 4, 1, 4)), ((6657342366993883 / 3808597056000), gapWord (7, 3, 6, 0)),
    ((-3759 / 8), gapWord (7, 3, 5, 1)), ((-7670666277593291 / 4602054776000), gapWord (7, 3, 4, 2)), ((-177539 / 125), gapWord (7, 3, 3, 3)),
    ((5882049115886299 / 3808597056000), gapWord (7, 2, 7, 0)), ((-117805948120524223 /
    66269588774400), gapWord (7, 2, 6, 1)), ((-128728556542020049 / 110449314624000),
    gapWord (7, 2, 5, 2)), ((-61960365056728213 / 82836985968000), gapWord (7, 1, 7, 1)), ((-8113 / 125), gapWord (6, 6, 4, 0)), ((-6512377774370439 /
    9204109552000), gapWord (6, 6, 3, 1)), ((-1584086345160977 / 4602054776000),
    gapWord (6, 6, 2, 2)), ((335613 / 250), gapWord (6, 5, 5, 0)), ((-109408 /
    125), gapWord (6, 5, 4, 1)), ((-1835693762099311 / 1840821910400), gapWord (6, 5, 3, 2)), ((-61821322091942343 / 36816438208000), gapWord (6, 5, 2, 3)), ((-85648 / 125), gapWord (6, 5, 1, 4)), ((124486 / 125), gapWord (6, 5, 0, 5)), ((39959 / 25), gapWord (6, 4, 6, 0)), ((-11929 / 25), gapWord (6, 4, 5, 1)), ((-878511 / 500), gapWord (6, 4, 4, 2)),
    ((-6116957220457829 / 2301027388000), gapWord (6, 4, 3, 3)), ((-134182 / 125),
    gapWord (6, 4, 2, 4)), ((-61575037368149521 / 110449314624000), gapWord (6, 3, 6, 1)), ((-9184878904158437 / 3808597056000), gapWord (6, 3, 5, 2)),
    ((-616757 / 500), gapWord (6, 3, 4, 3)), ((-14852245905028967 / 16567397193600),
    gapWord (6, 2, 6, 2)), ((-597 / 2), gapWord (5, 5, 5, 1)), ((-254609 /
    125), gapWord (5, 5, 4, 2)), ((-7906438610229371 / 9204109552000), gapWord (5, 5, 3, 3)), ((-108822 / 125), gapWord (5, 4, 5, 2)), ((17944677 / 500),
    gapWord (5, 4, 4, 3)), ((2237897 / 125), gapWord (5, 4, 3, 4)),
    ((4368699 / 500), gapWord (5, 3, 5, 3)), ((1166939 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary9 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((344781 / 1000), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)),
    ((-68417 / 500), gapWord (13, 2, 0, 1)), ((344781 / 500), gapWord (13, 1, 2, 0)), ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)),
    ((-3673731928376951 / 9204109552000), gapWord (13, 0, 3, 0)), ((-39259 / 250),
    gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 / 500), gapWord (12, 3, 0, 1)), ((138623 / 200), gapWord (12, 2, 2, 0)), ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000), gapWord (12, 2, 0, 2)), ((-3709572730972439 /
    4602054776000), gapWord (12, 1, 3, 0)), ((344781 / 1000), gapWord (12, 1, 2, 1)), ((-82998701901683 / 230102738800), gapWord (12, 0, 4, 0)), ((-18111 /
    125), gapWord (11, 5, 0, 0)), ((-161068712518923 / 209184308000), gapWord (11, 4, 1, 0)), ((-39259 / 250), gapWord (11, 4, 0, 1)), ((2049949621640231 /
    4602054776000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000),
    gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)),
    ((-9164905733336079 / 9204109552000), gapWord (11, 2, 3, 0)), ((138623 / 200),
    gapWord (11, 2, 2, 1)), ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)), ((-153042519300317 / 209184308000), gapWord (11, 1, 4, 0)),
    ((-3745413533567927 / 9204109552000), gapWord (11, 1, 3, 1)), ((-2475167088260491 /
    4602054776000), gapWord (11, 0, 5, 0)), ((-33707 / 250), gapWord (10, 6, 0, 0)), ((-29869206843061 / 71907105875), gapWord (10, 5, 1, 0)), ((-18111 / 125),
    gapWord (10, 5, 0, 1)), ((-7906385317321 / 83673723200), gapWord (10, 4, 2, 0)), ((-161068712518923 / 209184308000), gapWord (10, 4, 1, 1)), ((-39259 / 250),
    gapWord (10, 4, 0, 2)), ((-5964231579708959 / 9204109552000), gapWord (10, 3, 3, 0)), ((2049949621640231 / 4602054776000), gapWord (10, 3, 2, 1)),
    ((-5882465934293823 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((-647148679811883 / 920410955200), gapWord (10, 2, 4, 0)), ((-1847317467705411 / 1840821910400), gapWord (10, 2, 3, 1)), ((174167 /
    500), gapWord (10, 2, 2, 2)), ((-1025707875241451 / 920410955200), gapWord (10, 1, 5, 0)), ((-853480693286657 / 2301027388000), gapWord (10, 1, 4, 1)), ((-554950036947817 / 1150513694000), gapWord (10, 0, 6, 0)), ((-35413 / 250),
    gapWord (9, 7, 0, 0)), ((-411339320704699 / 920410955200), gapWord (9, 6, 1, 0)), ((-33707 / 250), gapWord (9, 6, 0, 1)), ((-21341761335351367 /
    36816438208000), gapWord (9, 5, 2, 0)), ((-29869206843061 / 71907105875), gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-1610252417361773 / 2301027388000), gapWord (9, 4, 3, 0)), ((-7906385317321 /
    83673723200), gapWord (9, 4, 2, 1)), ((-161068712518923 / 209184308000), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)),
    ((-176689634058879 / 230102738800), gapWord (9, 3, 4, 0)), ((-1207182636979987 /
    1840821910400), gapWord (9, 3, 3, 1)), ((2066300722259359 / 4602054776000),
    gapWord (9, 3, 2, 2)), ((-5918914208119743 / 9204109552000), gapWord (9, 3, 1, 3)), ((-20154492071957957 / 22089862924800), gapWord (9, 2, 5, 0)),
    ((-3282730747599069 / 4602054776000), gapWord (9, 2, 4, 1)), ((-62399702329081 /
    104592154000), gapWord (9, 2, 3, 2)), ((-94497802881855121 / 110449314624000),
    gapWord (9, 1, 6, 0)), ((-663343071986691 / 1150513694000), gapWord (9, 1, 5, 1)), ((-1421468942581541 / 3808597056000), gapWord (9, 0, 7, 0)),
    ((-17379 / 500), gapWord (8, 8, 0, 0)), ((-216251 / 500), gapWord (8, 7, 1, 0)), ((-34863 / 250), gapWord (8, 7, 0, 1)), ((-65089 / 125), gapWord (8, 6, 2, 0)), ((-409314416603259 / 920410955200), gapWord (8, 6, 1, 1)),
    ((-33707 / 250), gapWord (8, 6, 0, 2)), ((-7019254490512091 / 9204109552000),
    gapWord (8, 5, 3, 0)), ((-21260765171293767 / 36816438208000), gapWord (8, 5, 2, 1)), ((-29869206843061 / 71907105875), gapWord (8, 5, 1, 2)), ((-18111 /
    125), gapWord (8, 5, 0, 3)), ((-184403 / 500), gapWord (8, 4, 4, 0)), ((-2054847725161581 / 2301027388000), gapWord (8, 4, 3, 1)),
    ((-49716692174509 / 418368616000), gapWord (8, 4, 2, 2)), ((-3604486627168871 /
    4602054776000), gapWord (8, 4, 1, 3)), ((-12089 / 250), gapWord (8, 4, 0, 4)), ((-4318211791117299 / 4602054776000), gapWord (8, 3, 5, 0)),
    ((-994289763267929 / 2301027388000), gapWord (8, 3, 4, 1)), ((-165259846551401 /
    143814211750), gapWord (8, 3, 3, 2)), ((456879330106191 / 4602054776000),
    gapWord (8, 3, 2, 3)), ((-558062525601941 / 8283698596800), gapWord (8, 2, 6, 0)), ((-160181503202110129 / 110449314624000), gapWord (8, 2, 5, 1)),
    ((-4516799904669299 / 4602054776000), gapWord (8, 2, 4, 2)), ((102386689108399169 /
    66269588774400), gapWord (8, 1, 7, 0)), ((-202776185921393521 / 110449314624000),
    gapWord (8, 1, 6, 1)), ((82927755218270027 / 82836985968000), gapWord (8, 0, 8, 0)), ((-53943 / 250), gapWord (7, 7, 2, 0)), ((-49718 / 125), gapWord (7, 7, 1, 1)), ((-108851 / 250), gapWord (7, 6, 3, 0)), ((-441849 / 500),
    gapWord (7, 6, 2, 1)), ((-479560180704123 / 920410955200), gapWord (7, 6, 1, 2)), ((-20537 / 125), gapWord (7, 6, 0, 3)), ((-504165161563639 /
    1150513694000), gapWord (7, 5, 4, 0)), ((-92467034154551 / 73632876416), gapWord (7, 5, 3, 1)), ((-22142887030757447 / 36816438208000), gapWord (7, 5, 2, 2)), ((-473372319604221 / 2301027388000), gapWord (7, 5, 1, 3)), ((-33581 /
    125), gapWord (7, 5, 0, 4)), ((-2349396990952741 / 2301027388000), gapWord (7, 4, 5, 0)), ((-47979 / 100), gapWord (7, 4, 4, 1)), ((-157420541016781 /
    2301027388000), gapWord (7, 4, 3, 2)), ((-671889395772749 / 418368616000),
    gapWord (7, 4, 2, 3)), ((-186092 / 125), gapWord (7, 4, 1, 4)),
    ((9724710263955163 / 3808597056000), gapWord (7, 3, 6, 0)), ((233466937410447 /
    1150513694000), gapWord (7, 3, 5, 1)), ((-615055262050357 / 287628423500), gapWord (7, 3, 4, 2)), ((-330903905131357 / 143814211750), gapWord (7, 3, 3, 3)), ((12122450626530523 / 3808597056000), gapWord (7, 2, 7, 0)),
    ((-789210047622945947 / 331347943872000), gapWord (7, 2, 6, 1)),
    ((-279338363719957393 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-20214104273147777 / 16567397193600), gapWord (7, 1, 7, 1)), ((-33343 / 125),
    gapWord (6, 6, 4, 0)), ((-659449834748427 / 920410955200), gapWord (6, 6, 3, 1)), ((-234679 / 500), gapWord (6, 6, 2, 2)), ((263389 / 250), gapWord (6, 5, 5, 0)), ((30972 / 125), gapWord (6, 5, 4, 1)), ((-11576448407270073 /
    9204109552000), gapWord (6, 5, 3, 2)), ((-70152734792659911 / 36816438208000),
    gapWord (6, 5, 2, 3)), ((-17597 / 125), gapWord (6, 5, 1, 4)), ((30334 /
    25), gapWord (6, 5, 0, 5)), ((147253 / 125), gapWord (6, 4, 6, 0)),
    ((-97191 / 250), gapWord (6, 4, 5, 1)), ((-53367 / 20), gapWord (6, 4, 4, 2)), ((-8343721189986387 / 4602054776000), gapWord (6, 4, 3, 3)), ((207181 /
    125), gapWord (6, 4, 2, 4)), ((-94606173125752561 / 110449314624000), gapWord (6, 3, 6, 1)), ((-5390449829206757 / 3808597056000), gapWord (6, 3, 5, 2)), ((-934589 / 500), gapWord (6, 3, 4, 3)), ((80168118587614973 /
    82836985968000), gapWord (6, 2, 6, 2)), ((-7329 / 10), gapWord (5, 5, 5, 1)), ((-2227 / 125), gapWord (5, 5, 4, 2)), ((-36807 / 100), gapWord (5, 5, 3, 3)), ((176424 / 125), gapWord (5, 4, 5, 2)), ((14614617 / 500), gapWord (5, 4, 4, 3)), ((1812074 / 125), gapWord (5, 4, 3, 4)), ((3537311 / 500),
    gapWord (5, 3, 5, 3)), ((896448 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary10 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((31093 / 100), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)), ((-68417 /
    500), gapWord (13, 2, 0, 1)), ((31093 / 50), gapWord (13, 1, 2, 0)),
    ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)), ((-4273434890347063 /
    9204109552000), gapWord (13, 0, 3, 0)), ((-39259 / 250), gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 /
    500), gapWord (12, 3, 0, 1)), ((314483 / 500), gapWord (12, 2, 2, 0)),
    ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000),
    gapWord (12, 2, 0, 2)), ((-4309275692942551 / 4602054776000), gapWord (12, 1, 3, 0)), ((31093 / 100), gapWord (12, 1, 2, 1)), ((7719027831513 /
    1150513694000), gapWord (12, 0, 4, 0)), ((-18111 / 125), gapWord (11, 5, 0, 0)), ((-161068712518923 / 209184308000), gapWord (11, 4, 1, 0)), ((-39259 /
    250), gapWord (11, 4, 0, 1)), ((989673017688039 / 2301027388000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000), gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)), ((-10479627464997749 /
    9204109552000), gapWord (11, 2, 3, 0)), ((314483 / 500), gapWord (11, 2, 2, 1)), ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)),
    ((26845225659 / 8367372320), gapWord (11, 1, 4, 0)), ((-4345116495538039 /
    9204109552000), gapWord (11, 1, 3, 1)), ((-2485807038902603 / 4602054776000),
    gapWord (11, 0, 5, 0)), ((-33707 / 250), gapWord (10, 6, 0, 0)),
    ((-29869206843061 / 71907105875), gapWord (10, 5, 1, 0)), ((-18111 / 125), gapWord (10, 5, 0, 1)), ((-41578585856077 / 418368616000), gapWord (10, 4, 2, 0)), ((-161068712518923 / 209184308000), gapWord (10, 4, 1, 1)), ((-39259 / 250),
    gapWord (10, 4, 0, 2)), ((-4689777111141223 / 9204109552000), gapWord (10, 3, 3, 0)), ((989673017688039 / 2301027388000), gapWord (10, 3, 2, 1)),
    ((-5882465934293823 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((-325192264197319 / 4602054776000), gapWord (10, 2, 4, 0)), ((-422052362807549 / 368164382080), gapWord (10, 2, 3, 1)), ((79509 /
    250), gapWord (10, 2, 2, 2)), ((-5325475106236623 / 4602054776000), gapWord (10, 1, 5, 0)), ((-8055618606801 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((-678732654771583 / 1150513694000), gapWord (10, 0, 6, 0)), ((-35413 / 500),
    gapWord (9, 7, 0, 0)), ((-411339320704699 / 920410955200), gapWord (9, 6, 1, 0)), ((-33707 / 250), gapWord (9, 6, 0, 1)), ((-20490270752476743 /
    36816438208000), gapWord (9, 5, 2, 0)), ((-29869206843061 / 71907105875), gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-1508565415031277 / 2301027388000), gapWord (9, 4, 3, 0)), ((-41578585856077 /
    418368616000), gapWord (9, 4, 2, 1)), ((-161068712518923 / 209184308000), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)),
    ((-848251655367547 / 1150513694000), gapWord (9, 3, 4, 0)), ((-4761458716332199 /
    9204109552000), gapWord (9, 3, 3, 1)), ((1006024118307167 / 2301027388000),
    gapWord (9, 3, 2, 2)), ((-5918914208119743 / 9204109552000), gapWord (9, 3, 1, 3)), ((-83707276736931769 / 110449314624000), gapWord (9, 2, 5, 0)),
    ((-372179612736973 / 4602054776000), gapWord (9, 2, 4, 1)), ((-3103096287325343 /
    4602054776000), gapWord (9, 2, 3, 2)), ((-112039915277011921 / 110449314624000),
    gapWord (9, 1, 6, 0)), ((-141983403366701 / 230102738800), gapWord (9, 1, 5, 1)), ((-1733743432397093 / 3808597056000), gapWord (9, 0, 7, 0)), ((-17379 /
    500), gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)), ((-34313 / 500), gapWord (8, 7, 0, 1)), ((-21993 / 50), gapWord (8, 6, 2, 0)), ((-409314416603259 / 920410955200), gapWord (8, 6, 1, 1)), ((-16964 /
    125), gapWord (8, 6, 0, 2)), ((-6494509796733467 / 9204109552000), gapWord (8, 5, 3, 0)), ((-20409274588419143 / 36816438208000), gapWord (8, 5, 2, 1)), ((-59865545449309 / 143814211750), gapWord (8, 5, 1, 2)), ((-18111 / 125),
    gapWord (8, 5, 0, 3)), ((-199677 / 500), gapWord (8, 4, 4, 0)),
    ((-390632144566217 / 460205477600), gapWord (8, 4, 3, 1)), ((-30826512424877 /
    418368616000), gapWord (8, 4, 2, 2)), ((-3604486627168871 / 4602054776000), gapWord (8, 4, 1, 3)), ((-12089 / 250), gapWord (8, 4, 0, 4)),
    ((-569843499679799 / 920410955200), gapWord (8, 3, 5, 0)), ((-923896733414233 /
    2301027388000), gapWord (8, 3, 4, 1)), ((-4291799596516087 / 4602054776000),
    gapWord (8, 3, 3, 2)), ((271029950032207 / 2301027388000), gapWord (8, 3, 2, 3)), ((-8468829434609089 / 41418492984000), gapWord (8, 2, 6, 0)),
    ((-127468293848829937 / 110449314624000), gapWord (8, 2, 5, 1)),
    ((-378641454199651 / 4602054776000), gapWord (8, 2, 4, 2)), ((469005331325715013 /
    331347943872000), gapWord (8, 1, 7, 0)), ((-41687033401093757 / 22089862924800),
    gapWord (8, 1, 6, 1)), ((80957726017979051 / 82836985968000), gapWord (8, 0, 8, 0)), ((-9921 / 500), gapWord (7, 7, 2, 0)), ((-35187 / 125), gapWord (7, 7, 1, 1)), ((-193199 / 500), gapWord (7, 6, 3, 0)), ((-343299 / 500),
    gapWord (7, 6, 2, 1)), ((-1822065442823911 / 4602054776000), gapWord (7, 6, 1, 2)), ((-4763 / 125), gapWord (7, 6, 0, 3)), ((-86885124697627 /
    230102738800), gapWord (7, 5, 4, 0)), ((-2031097778280607 / 1840821910400), gapWord (7, 5, 3, 1)), ((-18385548613001799 / 36816438208000), gapWord (7, 5, 2, 2)), ((-799658003222621 / 2301027388000), gapWord (7, 5, 1, 3)), ((-33581 /
    125), gapWord (7, 5, 0, 4)), ((-505733086539409 / 460205477600), gapWord (7, 4, 5, 0)), ((-255169 / 500), gapWord (7, 4, 4, 1)), ((1590936884823827 /
    2301027388000), gapWord (7, 4, 3, 2)), ((-778001064586061 / 418368616000),
    gapWord (7, 4, 2, 3)), ((-186092 / 125), gapWord (7, 4, 1, 4)),
    ((8474191697991067 / 3808597056000), gapWord (7, 3, 6, 0)), ((797659294215249 /
    1150513694000), gapWord (7, 3, 5, 1)), ((-121507006888123 / 71907105875), gapWord (7, 3, 4, 2)), ((-883489483169963 / 287628423500), gapWord (7, 3, 3, 3)), ((11546697392380891 / 3808597056000), gapWord (7, 2, 7, 0)),
    ((-169312215028017439 / 66269588774400), gapWord (7, 2, 6, 1)),
    ((-11571010706321977 / 4417972584960), gapWord (7, 2, 5, 2)), ((-103040550566029861 /
    82836985968000), gapWord (7, 1, 7, 1)), ((-62634 / 125), gapWord (6, 6, 4, 0)), ((-679533201790891 / 920410955200), gapWord (6, 6, 3, 1)), ((-37191 / 100),
    gapWord (6, 6, 2, 2)), ((230259 / 250), gapWord (6, 5, 5, 0)), ((23217 /
    125), gapWord (6, 5, 4, 1)), ((-1468982853079077 / 1840821910400), gapWord (6, 5, 3, 2)), ((-72723405774095303 / 36816438208000), gapWord (6, 5, 2, 3)), ((-46888 / 125), gapWord (6, 5, 1, 4)), ((30334 / 25), gapWord (6, 5, 0, 5)), ((291827 / 250), gapWord (6, 4, 6, 0)), ((-119347 / 250), gapWord (6, 4, 5, 1)), ((-1364931 / 500), gapWord (6, 4, 4, 2)),
    ((-6624172627043539 / 4602054776000), gapWord (6, 4, 3, 3)), ((133961 / 125), gapWord (6, 4, 2, 4)), ((-150535938862312177 / 110449314624000), gapWord (6, 3, 6, 1)), ((-4219321468874981 / 3808597056000), gapWord (6, 3, 5, 2)), ((504011 /
    500), gapWord (6, 3, 4, 3)), ((76504073024278397 / 82836985968000), gapWord (6, 2, 6, 2)), ((-43271 / 50), gapWord (5, 5, 5, 1)), ((-83631 / 125), gapWord (5, 5, 4, 2)), ((186229 / 500), gapWord (5, 5, 3, 3)), ((137931 / 125),
    gapWord (5, 4, 5, 2)), ((13894721 / 500), gapWord (5, 4, 4, 3)),
    ((1569192 / 125), gapWord (5, 4, 3, 4)), ((2731239 / 500), gapWord (5, 3, 5, 3)), ((896448 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary11 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((31093 / 100), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)), ((-68417 /
    500), gapWord (13, 2, 0, 1)), ((31093 / 50), gapWord (13, 1, 2, 0)),
    ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)), ((-2201074400056951 /
    4602054776000), gapWord (13, 0, 3, 0)), ((-39259 / 250), gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 /
    500), gapWord (12, 3, 0, 1)), ((314483 / 500), gapWord (12, 2, 2, 0)),
    ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000),
    gapWord (12, 2, 0, 2)), ((-2236915202652439 / 2301027388000), gapWord (12, 1, 3, 0)), ((31093 / 100), gapWord (12, 1, 2, 1)), ((-94087627923159 /
    1150513694000), gapWord (12, 0, 4, 0)), ((-18111 / 125), gapWord (11, 5, 0, 0)), ((-161068712518923 / 209184308000), gapWord (11, 4, 1, 0)), ((-39259 /
    250), gapWord (11, 4, 0, 1)), ((989673017688039 / 2301027388000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000), gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)), ((-2652085343691147 /
    2301027388000), gapWord (11, 2, 3, 0)), ((314483 / 500), gapWord (11, 2, 2, 1)), ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)),
    ((-2310720063609 / 41836861600), gapWord (11, 1, 4, 0)), ((-2272756005247927 /
    4602054776000), gapWord (11, 1, 3, 1)), ((-499952093796687 / 920410955200),
    gapWord (11, 0, 5, 0)), ((-33707 / 500), gapWord (10, 6, 0, 0)),
    ((-2250301380197 / 5752568470), gapWord (10, 5, 1, 0)), ((-18111 / 125), gapWord (10, 5, 0, 1)), ((-53201 / 250), gapWord (10, 4, 2, 0)),
    ((-161068712518923 / 209184308000), gapWord (10, 4, 1, 1)), ((-39259 / 250),
    gapWord (10, 4, 0, 2)), ((-2409245510454031 / 4602054776000), gapWord (10, 3, 3, 0)), ((989673017688039 / 2301027388000), gapWord (10, 3, 2, 1)),
    ((-5882465934293823 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((-732418887216007 / 4602054776000), gapWord (10, 2, 4, 0)), ((-537585229257327 / 460205477600), gapWord (10, 2, 3, 1)), ((79509 /
    250), gapWord (10, 2, 2, 2)), ((-1067885707263491 / 920410955200), gapWord (10, 1, 5, 0)), ((61085652347823 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((117764208992971 / 460205477600), gapWord (10, 0, 6, 0)), ((-35413 / 500),
    gapWord (9, 7, 0, 0)), ((-1294324485912311 / 4602054776000), gapWord (9, 6, 1, 0)), ((-33707 / 500), gapWord (9, 6, 0, 1)), ((-9396299794383687 /
    18408219104000), gapWord (9, 5, 2, 0)), ((-2250301380197 / 5752568470), gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-2892274368089619 / 4602054776000), gapWord (9, 4, 3, 0)), ((-53201 / 250),
    gapWord (9, 4, 2, 1)), ((-161068712518923 / 209184308000), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)), ((-700129920347211 /
    1150513694000), gapWord (9, 3, 4, 0)), ((-2480927115645007 / 4602054776000),
    gapWord (9, 3, 3, 1)), ((1006024118307167 / 2301027388000), gapWord (9, 3, 2, 2)), ((-5918914208119743 / 9204109552000), gapWord (9, 3, 1, 3)),
    ((-65052064780746649 / 110449314624000), gapWord (9, 2, 5, 0)), ((-9355882833109
    / 184082191040), gapWord (9, 2, 4, 1)), ((-3103096287325343 / 4602054776000),
    gapWord (9, 2, 3, 2)), ((-8106951320345549 / 22089862924800), gapWord (9, 1, 6, 0)), ((-141983403366701 / 230102738800), gapWord (9, 1, 5, 1)),
    ((-2951138629765157 / 3808597056000), gapWord (9, 0, 7, 0)), ((-17379 / 500),
    gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)),
    ((-34313 / 500), gapWord (8, 7, 0, 1)), ((-1726427899382657 / 4602054776000),
    gapWord (8, 6, 2, 0)), ((-1284199965405111 / 4602054776000), gapWord (8, 6, 1, 1)), ((-34149 / 500), gapWord (8, 6, 0, 2)), ((-6576904985442971 /
    9204109552000), gapWord (8, 5, 3, 0)), ((-9355801712354887 / 18408219104000),
    gapWord (8, 5, 2, 1)), ((-28192333134056 / 71907105875), gapWord (8, 5, 1, 2)), ((-14431 / 125), gapWord (8, 5, 0, 3)), ((-1131 / 100), gapWord (8, 4, 4, 0)), ((-3366138744264787 / 4602054776000), gapWord (8, 4, 3, 1)),
    ((-23388 / 125), gapWord (8, 4, 2, 2)), ((-904191644696123 / 920410955200),
    gapWord (8, 4, 1, 3)), ((-12089 / 250), gapWord (8, 4, 0, 4)),
    ((-1245235734991059 / 4602054776000), gapWord (8, 3, 5, 0)), ((-923896733414233 /
    2301027388000), gapWord (8, 3, 4, 1)), ((-4291799596516087 / 4602054776000),
    gapWord (8, 3, 3, 2)), ((271029950032207 / 2301027388000), gapWord (8, 3, 2, 3)), ((-52953014949299 / 1428223896000), gapWord (8, 2, 6, 0)),
    ((-157932865605680113 / 110449314624000), gapWord (8, 2, 5, 1)),
    ((-663934399568639 / 920410955200), gapWord (8, 2, 4, 2)), ((373308068960154949 /
    331347943872000), gapWord (8, 1, 7, 0)), ((-41687033401093757 / 22089862924800),
    gapWord (8, 1, 6, 1)), ((61452597954009899 / 82836985968000), gapWord (8, 0, 8, 0)), ((-9921 / 500), gapWord (7, 7, 2, 0)), ((-35187 / 125), gapWord (7, 7, 1, 1)), ((-1076807524079 / 83673723200), gapWord (7, 6, 3, 0)),
    ((-572385938140669 / 920410955200), gapWord (7, 6, 2, 1)), ((-1059693325212727 /
    4602054776000), gapWord (7, 6, 1, 2)), ((153591 / 500), gapWord (7, 6, 0, 3)), ((48783450098853 / 230102738800), gapWord (7, 5, 4, 0)),
    ((-9856760311783323 / 9204109552000), gapWord (7, 5, 3, 1)), ((-1668787744929243 /
    3681643820800), gapWord (7, 5, 2, 2)), ((-139397041023973 / 575256847000),
    gapWord (7, 5, 1, 3)), ((-81486 / 125), gapWord (7, 5, 0, 4)),
    ((-2176221669731861 / 2301027388000), gapWord (7, 4, 5, 0)), ((-284239 / 500),
    gapWord (7, 4, 4, 1)), ((3186561377309677 / 4602054776000), gapWord (7, 4, 3, 2)), ((-493257 / 250), gapWord (7, 4, 2, 3)), ((-186092 / 125), gapWord (7, 4, 1, 4)), ((10173343954166683 / 3808597056000), gapWord (7, 3, 6, 0)), ((274828057557133 / 230102738800), gapWord (7, 3, 5, 1)),
    ((-162918021533112 / 71907105875), gapWord (7, 3, 4, 2)), ((-883489483169963 /
    287628423500), gapWord (7, 3, 3, 3)), ((2220602213949023 / 761719411200), gapWord (7, 2, 7, 0)), ((-973464686859512219 / 331347943872000), gapWord (7, 2, 6, 1)), ((-376635373958531473 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-103040550566029861 / 82836985968000), gapWord (7, 1, 7, 1)), ((-63139 / 125),
    gapWord (6, 6, 4, 0)), ((-74562868337631 / 287628423500), gapWord (6, 6, 3, 1)), ((-1490093978415953 / 4602054776000), gapWord (6, 6, 2, 2)), ((288221 /
    250), gapWord (6, 5, 5, 0)), ((173576 / 125), gapWord (6, 5, 4, 1)),
    ((-4872532498965179 / 9204109552000), gapWord (6, 5, 3, 2)), ((-46154659750968171 /
    18408219104000), gapWord (6, 5, 2, 3)), ((-144414 / 125), gapWord (6, 5, 1, 4)), ((32122 / 125), gapWord (6, 5, 0, 5)), ((685833 / 250), gapWord (6, 4, 6, 0)), ((1192247721506563 / 1150513694000), gapWord (6, 4, 5, 1)), ((-1600799 / 500), gapWord (6, 4, 4, 2)), ((-104248282806671 /
    39672886000), gapWord (6, 4, 3, 3)), ((54292 / 125), gapWord (6, 4, 2, 4)), ((-160919941626002161 / 110449314624000), gapWord (6, 3, 6, 1)),
    ((-7595627524630757 / 3808597056000), gapWord (6, 3, 5, 2)), ((246351 / 500), gapWord (6, 3, 4, 3)), ((25093052246851103 / 82836985968000), gapWord (6, 2, 6, 2)), ((-316093 / 250), gapWord (5, 5, 5, 1)), ((18154 / 125), gapWord (5, 5, 4, 2)), ((11589150107737403 / 9204109552000), gapWord (5, 5, 3, 3)),
    ((488233 / 125), gapWord (5, 4, 5, 2)), ((13443049 / 500), gapWord (5, 4, 4, 3)), ((1223663 / 125), gapWord (5, 4, 3, 4)), ((2052523 / 500), gapWord (5, 3, 5, 3)), ((1055981 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary12 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((31093 / 100), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)), ((-68417 /
    500), gapWord (13, 2, 0, 1)), ((31093 / 50), gapWord (13, 1, 2, 0)),
    ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)), ((-2201074400056951 /
    4602054776000), gapWord (13, 0, 3, 0)), ((-39259 / 250), gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 /
    500), gapWord (12, 3, 0, 1)), ((314483 / 500), gapWord (12, 2, 2, 0)),
    ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000),
    gapWord (12, 2, 0, 2)), ((-2236915202652439 / 2301027388000), gapWord (12, 1, 3, 0)), ((31093 / 100), gapWord (12, 1, 2, 1)), ((-94087627923159 /
    1150513694000), gapWord (12, 0, 4, 0)), ((-18111 / 125), gapWord (11, 5, 0, 0)), ((-158794879090963 / 209184308000), gapWord (11, 4, 1, 0)), ((-39259 /
    250), gapWord (11, 4, 0, 1)), ((992742588223631 / 2301027388000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000), gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)), ((-6481143857835263 /
    4602054776000), gapWord (11, 2, 3, 0)), ((314483 / 500), gapWord (11, 2, 2, 1)), ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)),
    ((-3188457419977 / 41836861600), gapWord (11, 1, 4, 0)), ((-2272756005247927 /
    4602054776000), gapWord (11, 1, 3, 1)), ((-499952093796687 / 920410955200),
    gapWord (11, 0, 5, 0)), ((-33707 / 500), gapWord (10, 6, 0, 0)),
    ((-2250301380197 / 5752568470), gapWord (10, 5, 1, 0)), ((-18111 / 125), gapWord (10, 5, 0, 1)), ((32579 / 250), gapWord (10, 4, 2, 0)),
    ((-158794879090963 / 209184308000), gapWord (10, 4, 1, 1)), ((-39259 / 250),
    gapWord (10, 4, 0, 2)), ((-86161358431847 / 184082191040), gapWord (10, 3, 3, 0)), ((992742588223631 / 2301027388000), gapWord (10, 3, 2, 1)),
    ((-5882465934293823 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((7018640030571 / 230102738800), gapWord (10, 2, 4, 0)), ((-6552825463026239 / 4602054776000), gapWord (10, 2, 3, 1)), ((79509 /
    250), gapWord (10, 2, 2, 2)), ((-1300915352901027 / 920410955200), gapWord (10, 1, 5, 0)), ((12810097747583 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((117764208992971 / 460205477600), gapWord (10, 0, 6, 0)), ((-35413 / 500),
    gapWord (9, 7, 0, 0)), ((-1294324485912311 / 4602054776000), gapWord (9, 6, 1, 0)), ((-33707 / 500), gapWord (9, 6, 0, 1)), ((-9396299794383687 /
    18408219104000), gapWord (9, 5, 2, 0)), ((-2250301380197 / 5752568470), gapWord (9, 5, 1, 1)), ((-18111 / 125), gapWord (9, 5, 0, 2)),
    ((-3124214035388317 / 4602054776000), gapWord (9, 4, 3, 0)), ((32579 / 250), gapWord (9, 4, 2, 1)), ((-158794879090963 / 209184308000), gapWord (9, 4, 1, 2)), ((-39259 / 250), gapWord (9, 4, 0, 3)), ((-726775817500251 /
    1150513694000), gapWord (9, 3, 4, 0)), ((-2225715565987151 / 4602054776000),
    gapWord (9, 3, 3, 1)), ((1009093688842759 / 2301027388000), gapWord (9, 3, 2, 2)), ((-5918914208119743 / 9204109552000), gapWord (9, 3, 1, 3)),
    ((-11190296610597509 / 22089862924800), gapWord (9, 2, 5, 0)), ((271171753899611 /
    2301027388000), gapWord (9, 2, 4, 1)), ((-48637152929299 / 52296077000), gapWord (9, 2, 3, 2)), ((40131329696391647 / 110449314624000), gapWord (9, 1, 6, 0)), ((-40048162955217 / 46020547760), gapWord (9, 1, 5, 1)),
    ((-2951138629765157 / 3808597056000), gapWord (9, 0, 7, 0)), ((-17379 / 500),
    gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)),
    ((-34313 / 500), gapWord (8, 7, 0, 1)), ((-1726427899382657 / 4602054776000),
    gapWord (8, 6, 2, 0)), ((-1284199965405111 / 4602054776000), gapWord (8, 6, 1, 1)), ((-34149 / 500), gapWord (8, 6, 0, 2)), ((-3682074469695691 /
    4602054776000), gapWord (8, 5, 3, 0)), ((-9355801712354887 / 18408219104000),
    gapWord (8, 5, 2, 1)), ((-28192333134056 / 71907105875), gapWord (8, 5, 1, 2)), ((-14431 / 125), gapWord (8, 5, 0, 3)), ((378687334646861 / 2301027388000),
    gapWord (8, 4, 4, 0)), ((-719615682312697 / 920410955200), gapWord (8, 4, 3, 1)), ((19502 / 125), gapWord (8, 4, 2, 2)), ((-894186777613099 / 920410955200),
    gapWord (8, 4, 1, 3)), ((-12089 / 250), gapWord (8, 4, 0, 4)),
    ((20471270547273 / 920410955200), gapWord (8, 3, 5, 0)), ((-545837933565833 /
    2301027388000), gapWord (8, 3, 4, 1)), ((-219624554422377 / 143814211750),
    gapWord (8, 3, 3, 2)), ((-1595512844510857 / 2301027388000), gapWord (8, 3, 2, 3)), ((408614670864397 / 1428223896000), gapWord (8, 2, 6, 0)),
    ((-137941981455994609 / 110449314624000), gapWord (8, 2, 5, 1)), ((-531693 /
    1000), gapWord (8, 2, 4, 2)), ((332692763392100677 / 331347943872000), gapWord (8, 1, 7, 0)), ((-68223738265627249 / 110449314624000), gapWord (8, 1, 6, 1)), ((61452597954009899 / 82836985968000), gapWord (8, 0, 8, 0)), ((-9921 /
    500), gapWord (7, 7, 2, 0)), ((-35187 / 125), gapWord (7, 7, 1, 1)),
    ((-1076807524079 / 83673723200), gapWord (7, 6, 3, 0)), ((-572385938140669 /
    920410955200), gapWord (7, 6, 2, 1)), ((-1059693325212727 / 4602054776000), gapWord (7, 6, 1, 2)), ((153591 / 500), gapWord (7, 6, 0, 3)), ((-28485049590187
    / 230102738800), gapWord (7, 5, 4, 0)), ((-5322002132865867 / 4602054776000),
    gapWord (7, 5, 3, 1)), ((-1668787744929243 / 3681643820800), gapWord (7, 5, 2, 2)), ((-139397041023973 / 575256847000), gapWord (7, 5, 1, 3)), ((-81486 /
    125), gapWord (7, 5, 0, 4)), ((-1301614965717389 / 1150513694000), gapWord (7, 4, 5, 0)), ((388756630496749 / 2301027388000), gapWord (7, 4, 4, 1)),
    ((4834689943540707 / 4602054776000), gapWord (7, 4, 3, 2)), ((-655249 / 250),
    gapWord (7, 4, 2, 3)), ((-49988 / 25), gapWord (7, 4, 1, 4)),
    ((9156631352873371 / 3808597056000), gapWord (7, 3, 6, 0)), ((2280174423865441 /
    1150513694000), gapWord (7, 3, 5, 1)), ((-9044221822697797 / 4602054776000),
    gapWord (7, 3, 4, 2)), ((-1185757042912419 / 287628423500), gapWord (7, 3, 3, 3)), ((10404697182333403 / 3808597056000), gapWord (7, 2, 7, 0)),
    ((-626392294963122587 / 331347943872000), gapWord (7, 2, 6, 1)),
    ((-372520474292899729 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-997200565164281 / 662695887744), gapWord (7, 1, 7, 1)), ((-63139 / 125), gapWord (6, 6, 4, 0)), ((-74562868337631 / 287628423500), gapWord (6, 6, 3, 1)), ((-1490093978415953 / 4602054776000), gapWord (6, 6, 2, 2)), ((509627 /
    250), gapWord (6, 5, 5, 0)), ((52867 / 25), gapWord (6, 5, 4, 1)),
    ((-2400314025445851 / 4602054776000), gapWord (6, 5, 3, 2)), ((-61687662296676203 /
    18408219104000), gapWord (6, 5, 2, 3)), ((-153192 / 125), gapWord (6, 5, 1, 4)), ((32122 / 125), gapWord (6, 5, 0, 5)), ((589337 / 250), gapWord (6, 4, 6, 0)), ((314631273668587 / 1150513694000), gapWord (6, 4, 5, 1)),
    ((-8608683845622643 / 2301027388000), gapWord (6, 4, 4, 2)), ((-2144794825207371 /
    2301027388000), gapWord (6, 4, 3, 3)), ((78992 / 25), gapWord (6, 4, 2, 4)), ((-260548757794918129 / 110449314624000), gapWord (6, 3, 6, 1)),
    ((-2350701878095589 / 3808597056000), gapWord (6, 3, 5, 2)), ((1401911 / 500),
    gapWord (6, 3, 4, 3)), ((199808846875230239 / 82836985968000), gapWord (6, 2, 6, 2)), ((-448961 / 250), gapWord (5, 5, 5, 1)), ((15252 / 25), gapWord (5, 5, 4, 2)), ((392043 / 250), gapWord (5, 5, 3, 3)), ((459852 / 125), gapWord (5, 4, 5, 2)), ((1823637944080373 / 92041095520), gapWord (5, 4, 4, 3)), ((793506 / 125), gapWord (5, 4, 3, 4)), ((137419 / 80), gapWord (5, 3, 5, 3)), ((157098 / 25), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary13 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((31093 / 100), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-5846017660467903 / 4602054776000), gapWord (13, 2, 1, 0)), ((-68417 /
    500), gapWord (13, 2, 0, 1)), ((31093 / 50), gapWord (13, 1, 2, 0)),
    ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)), ((-2201074400056951 /
    4602054776000), gapWord (13, 0, 3, 0)), ((-39259 / 250), gapWord (12, 4, 0, 0)), ((-5882465934293823 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 /
    500), gapWord (12, 3, 0, 1)), ((77384 / 125), gapWord (12, 2, 2, 0)),
    ((-5846017660467903 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000),
    gapWord (12, 2, 0, 2)), ((-2248783901919743 / 2301027388000), gapWord (12, 1, 3, 0)), ((31093 / 100), gapWord (12, 1, 2, 1)), ((-489787431471 /
    23010273880), gapWord (12, 0, 4, 0)), ((-18111 / 250), gapWord (11, 5, 0, 0)), ((-158794879090963 / 209184308000), gapWord (11, 4, 1, 0)), ((-39259 / 250),
    gapWord (11, 4, 0, 1)), ((992742588223631 / 2301027388000), gapWord (11, 3, 2, 0)), ((-5882465934293823 / 4602054776000), gapWord (11, 3, 1, 1)),
    ((-68417 / 500), gapWord (11, 3, 0, 2)), ((-1351114717647539 / 920410955200),
    gapWord (11, 2, 3, 0)), ((77384 / 125), gapWord (11, 2, 2, 1)),
    ((-5846017660467903 / 9204109552000), gapWord (11, 2, 1, 2)), ((-5155907442173 /
    104592154000), gapWord (11, 1, 4, 0)), ((-459298680756507 / 920410955200), gapWord (11, 1, 3, 1)), ((-805261245027807 / 920410955200), gapWord (11, 0, 5, 0)), ((-33707 / 500), gapWord (10, 6, 0, 0)), ((-305928159758549 /
    1150513694000), gapWord (10, 5, 1, 0)), ((-18111 / 250), gapWord (10, 5, 0, 1)), ((32579 / 250), gapWord (10, 4, 2, 0)), ((-158794879090963 / 209184308000),
    gapWord (10, 4, 1, 1)), ((-39259 / 250), gapWord (10, 4, 0, 2)),
    ((-86161358431847 / 184082191040), gapWord (10, 3, 3, 0)), ((992742588223631 /
    2301027388000), gapWord (10, 3, 2, 1)), ((-5882465934293823 / 4602054776000),
    gapWord (10, 3, 1, 2)), ((-68417 / 1000), gapWord (10, 3, 0, 3)),
    ((1372156912339973 / 4602054776000), gapWord (10, 2, 4, 0)), ((-6850992591963279 /
    4602054776000), gapWord (10, 2, 3, 1)), ((154071 / 500), gapWord (10, 2, 2, 2)), ((-828352786413889 / 418368616000), gapWord (10, 1, 5, 0)),
    ((-32225610290353 / 1150513694000), gapWord (10, 1, 4, 1)), ((134589034464103 /
    2301027388000), gapWord (10, 0, 6, 0)), ((-35413 / 500), gapWord (9, 7, 0, 0)), ((-1294324485912311 / 4602054776000), gapWord (9, 6, 1, 0)), ((-33707 /
    500), gapWord (9, 6, 0, 1)), ((-8360727020469063 / 18408219104000), gapWord (9, 5, 2, 0)), ((-305928159758549 / 1150513694000), gapWord (9, 5, 1, 1)), ((-18111 / 250), gapWord (9, 5, 0, 2)), ((-3124214035388317 /
    4602054776000), gapWord (9, 4, 3, 0)), ((32579 / 250), gapWord (9, 4, 2, 1)), ((-158794879090963 / 209184308000), gapWord (9, 4, 1, 2)), ((-39259 / 250),
    gapWord (9, 4, 0, 3)), ((-63030386228619 / 115051369400), gapWord (9, 3, 4, 0)), ((-2249452964521759 / 4602054776000), gapWord (9, 3, 3, 1)),
    ((986327323865887 / 2301027388000), gapWord (9, 3, 2, 2)), ((-5918914208119743 /
    9204109552000), gapWord (9, 3, 1, 3)), ((-73019229447011257 / 110449314624000),
    gapWord (9, 2, 5, 0)), ((121928359770251 / 418368616000), gapWord (9, 2, 4, 1)), ((-51755672592963 / 52296077000), gapWord (9, 2, 3, 2)),
    ((102590417116263647 / 110449314624000), gapWord (9, 1, 6, 0)),
    ((-317848401588359 / 287628423500), gapWord (9, 1, 5, 1)), ((-4753610506875941 /
    3808597056000), gapWord (9, 0, 7, 0)), ((-17379 / 500), gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)), ((-34313 / 500), gapWord (8, 7, 0, 1)), ((-1726427899382657 / 4602054776000), gapWord (8, 6, 2, 0)),
    ((-1284199965405111 / 4602054776000), gapWord (8, 6, 1, 1)), ((-34149 / 500), gapWord (8, 6, 0, 2)), ((-2934702700054131 / 4602054776000), gapWord (8, 5, 3, 0)), ((-8320228938440263 / 18408219104000), gapWord (8, 5, 2, 1)),
    ((-61389042772809 / 230102738800), gapWord (8, 5, 1, 2)), ((-10751 / 250), gapWord (8, 5, 0, 3)), ((781495985080589 / 2301027388000), gapWord (8, 4, 4, 0)), ((-3345480829018397 / 4602054776000), gapWord (8, 4, 3, 1)), ((33511 /
    250), gapWord (8, 4, 2, 2)), ((-905194892637291 / 920410955200), gapWord (8, 4, 1, 3)), ((-64328 / 125), gapWord (8, 4, 0, 4)), ((-2185527566823379 /
    4602054776000), gapWord (8, 3, 5, 0)), ((-50727933934653 / 230102738800), gapWord (8, 3, 4, 1)), ((-126016459251149 / 143814211750), gapWord (8, 3, 3, 2)), ((1066057922860087 / 2301027388000), gapWord (8, 3, 2, 3)),
    ((239341574710477 / 1428223896000), gapWord (8, 2, 6, 0)), ((-79889715774840241 /
    110449314624000), gapWord (8, 2, 5, 1)), ((1296110707553613 / 4602054776000),
    gapWord (8, 2, 4, 2)), ((68867531106307649 / 66269588774400), gapWord (8, 1, 7, 0)), ((75158027601181583 / 110449314624000), gapWord (8, 1, 6, 1)),
    ((32619908799947119 / 16567397193600), gapWord (8, 0, 8, 0)), ((-9921 / 500), gapWord (7, 7, 2, 0)), ((-35187 / 125), gapWord (7, 7, 1, 1)), ((-1076807524079
    / 83673723200), gapWord (7, 6, 3, 0)), ((-572385938140669 / 920410955200),
    gapWord (7, 6, 2, 1)), ((-1059693325212727 / 4602054776000), gapWord (7, 6, 1, 2)), ((153591 / 500), gapWord (7, 6, 0, 3)), ((365715232195881 /
    1150513694000), gapWord (7, 5, 4, 0)), ((-2787853058132811 / 4602054776000),
    gapWord (7, 5, 3, 1)), ((-4952555702678087 / 18408219104000), gapWord (7, 5, 2, 2)), ((288755125061187 / 575256847000), gapWord (7, 5, 1, 3)), ((-40238 /
    125), gapWord (7, 5, 0, 4)), ((-1378275994175997 / 1150513694000), gapWord (7, 4, 5, 0)), ((1074297118148813 / 2301027388000), gapWord (7, 4, 4, 1)), ((5217175920083619 / 4602054776000), gapWord (7, 4, 3, 2)), ((-597701
    / 250), gapWord (7, 4, 2, 3)), ((-344376 / 125), gapWord (7, 4, 1, 4)),
    ((8998620278214043 / 3808597056000), gapWord (7, 3, 6, 0)), ((1168550393750029 /
    575256847000), gapWord (7, 3, 5, 1)), ((-94825391849853 / 57525684700), gapWord (7, 3, 4, 2)), ((-1127920719515039 / 287628423500), gapWord (7, 3, 3, 3)), ((1852539394457183 / 761719411200), gapWord (7, 2, 7, 0)),
    ((-552117339864775067 / 331347943872000), gapWord (7, 2, 6, 1)),
    ((-364687908508393777 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-146259590725040389 / 82836985968000), gapWord (7, 1, 7, 1)), ((-37053 / 125),
    gapWord (6, 6, 4, 0)), ((72555618741537 / 287628423500), gapWord (6, 6, 3, 1)), ((-1084192747172753 / 4602054776000), gapWord (6, 6, 2, 2)), ((21671 /
    10), gapWord (6, 5, 5, 0)), ((284879 / 125), gapWord (6, 5, 4, 1)),
    ((-2060203769280347 / 4602054776000), gapWord (6, 5, 3, 2)), ((-58129574442502251 /
    18408219104000), gapWord (6, 5, 2, 3)), ((-6816 / 5), gapWord (6, 5, 1, 4)), ((55526 / 25), gapWord (6, 5, 0, 5)), ((632167 / 250), gapWord (6, 4, 6, 0)), ((-9988466120901 / 1150513694000), gapWord (6, 4, 5, 1)),
    ((-8800515896905427 / 2301027388000), gapWord (6, 4, 4, 2)), ((-3348563497075243 /
    2301027388000), gapWord (6, 4, 3, 3)), ((311488 / 125), gapWord (6, 4, 2, 4)), ((-63295704706295549 / 22089862924800), gapWord (6, 3, 6, 1)),
    ((-3663174892369637 / 3808597056000), gapWord (6, 3, 5, 2)), ((124923 / 50), gapWord (6, 3, 4, 3)), ((196144801311893663 / 82836985968000), gapWord (6, 2, 6, 2)), ((-605013 / 250), gapWord (5, 5, 5, 1)), ((-15467 / 125), gapWord (5, 5, 4, 2)), ((313067 / 250), gapWord (5, 5, 3, 3)), ((83333 / 25), gapWord (5, 4, 5, 2)), ((43092456247680717 / 2301027388000), gapWord (5, 4, 4, 3)), ((137871 / 25), gapWord (5, 4, 3, 4)), ((2824787 / 2000), gapWord (5, 3, 5, 3)), ((157098 / 25), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary14 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 500), gapWord (14, 2, 0, 0)), ((-5846017660467903 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((31093 / 100), gapWord (14, 0, 2, 0)), ((-68417 / 500), gapWord (13, 3, 0, 0)), ((-6091675344410783 / 4602054776000), gapWord (13, 2, 1, 0)), ((-68417 /
    500), gapWord (13, 2, 0, 1)), ((615519 / 1000), gapWord (13, 1, 2, 0)), ((-5846017660467903 / 9204109552000), gapWord (13, 1, 1, 1)),
    ((-2260652601187047 / 4602054776000), gapWord (13, 0, 3, 0)), ((-39259 / 500),
    gapWord (12, 4, 0, 0)), ((-6109899481323743 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 / 500), gapWord (12, 3, 0, 1)), ((157721 / 125), gapWord (12, 2, 2, 0)), ((-6091675344410783 / 4602054776000), gapWord (12, 2, 1, 1)), ((-68417 / 1000), gapWord (12, 2, 0, 2)), ((-2454012534655463 /
    2301027388000), gapWord (12, 1, 3, 0)), ((304589 / 1000), gapWord (12, 1, 2, 1)), ((-56636106156071 / 575256847000), gapWord (12, 0, 4, 0)), ((-18111 /
    250), gapWord (11, 5, 0, 0)), ((-1391373152725669 / 1840821910400), gapWord (11, 4, 1, 0)), ((-39259 / 500), gapWord (11, 4, 0, 1)), ((2126560027496303 /
    2301027388000), gapWord (11, 3, 2, 0)), ((-6109899481323743 / 4602054776000),
    gapWord (11, 3, 1, 1)), ((-68417 / 500), gapWord (11, 3, 0, 2)),
    ((-1433206170741827 / 920410955200), gapWord (11, 2, 3, 0)), ((1255427 / 1000),
    gapWord (11, 2, 2, 1)), ((-6337333028353663 / 9204109552000), gapWord (11, 2, 1, 2)), ((25661752365311 / 104592154000), gapWord (11, 1, 4, 0)),
    ((-2647372468123879 / 4602054776000), gapWord (11, 1, 3, 1)), ((-38417815609797 /
    41836861600), gapWord (11, 0, 5, 0)), ((-33707 / 500), gapWord (10, 6, 0, 0)), ((-305928159758549 / 1150513694000), gapWord (10, 5, 1, 0)), ((-18111 / 250),
    gapWord (10, 5, 0, 1)), ((39597 / 250), gapWord (10, 4, 2, 0)),
    ((-1391373152725669 / 1840821910400), gapWord (10, 4, 1, 1)), ((-39259 / 500),
    gapWord (10, 4, 0, 2)), ((-2189810334624799 / 4602054776000), gapWord (10, 3, 3, 0)), ((422393842565799 / 460205477600), gapWord (10, 3, 2, 1)),
    ((-6355557165266623 / 4602054776000), gapWord (10, 3, 1, 2)), ((-68417 / 1000),
    gapWord (10, 3, 0, 3)), ((661894186431237 / 4602054776000), gapWord (10, 2, 4, 0)), ((-7552750720645967 / 4602054776000), gapWord (10, 2, 3, 1)), ((475419 /
    500), gapWord (10, 2, 2, 2)), ((-4776948377607339 / 2301027388000), gapWord (10, 1, 5, 0)), ((395551488330563 / 1150513694000), gapWord (10, 1, 4, 1)),
    ((194858750691487 / 209184308000), gapWord (10, 0, 6, 0)), ((-35413 / 500),
    gapWord (9, 7, 0, 0)), ((-1294324485912311 / 4602054776000), gapWord (9, 6, 1, 0)), ((-33707 / 500), gapWord (9, 6, 0, 1)), ((-8360727020469063 /
    18408219104000), gapWord (9, 5, 2, 0)), ((-305928159758549 / 1150513694000),
    gapWord (9, 5, 1, 1)), ((-18111 / 250), gapWord (9, 5, 0, 2)),
    ((-2767168217647133 / 4602054776000), gapWord (9, 4, 3, 0)), ((9323 / 50), gapWord (9, 4, 2, 1)), ((-3463378423627159 / 4602054776000), gapWord (9, 4, 1, 2)), ((-39259 / 500), gapWord (9, 4, 0, 3)), ((-238992526655071 / 575256847000),
    gapWord (9, 3, 4, 0)), ((-440369861983763 / 920410955200), gapWord (9, 3, 3, 1)), ((3253962202411231 / 2301027388000), gapWord (9, 3, 2, 2)),
    ((-6373781302179583 / 9204109552000), gapWord (9, 3, 1, 3)), ((-39962124934184569 /
    55224657312000), gapWord (9, 2, 5, 0)), ((281489129489259 / 418368616000), gapWord (9, 2, 4, 1)), ((-54874192256627 / 52296077000), gapWord (9, 2, 3, 2)), ((166879231244092799 / 110449314624000), gapWord (9, 1, 6, 0)),
    ((-337869640891347 / 287628423500), gapWord (9, 1, 5, 1)), ((-233770223768813 /
    152343882240), gapWord (9, 0, 7, 0)), ((-17379 / 500), gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)), ((-34313 / 500), gapWord (8, 7, 0, 1)), ((-1726427899382657 / 4602054776000), gapWord (8, 6, 2, 0)),
    ((-1284199965405111 / 4602054776000), gapWord (8, 6, 1, 1)), ((-34149 / 500), gapWord (8, 6, 0, 2)), ((-2187330930412571 / 4602054776000), gapWord (8, 5, 3, 0)), ((-7325154246554439 / 18408219104000), gapWord (8, 5, 2, 1)),
    ((-80898021738849 / 575256847000), gapWord (8, 5, 1, 2)), ((-18111 / 250), gapWord (8, 5, 0, 3)), ((102653 / 125), gapWord (8, 4, 4, 0)),
    ((-2478969139354909 / 4602054776000), gapWord (8, 4, 3, 1)), ((26479 / 50), gapWord (8, 4, 2, 2)), ((-3463378423627159 / 4602054776000), gapWord (8, 4, 1, 3)), ((-316445588557657 / 2301027388000), gapWord (8, 3, 5, 0)),
    ((-87174144315793 / 1150513694000), gapWord (8, 3, 4, 1)), ((-92979458527939 /
    143814211750), gapWord (8, 3, 3, 2)), ((1066057922860087 / 2301027388000),
    gapWord (8, 3, 2, 3)), ((43913139778639 / 5522465731200), gapWord (8, 2, 6, 0)), ((-5047473558384947 / 5020423392000), gapWord (8, 2, 5, 1)), ((183429 /
    500), gapWord (8, 2, 4, 2)), ((223542111809449669 / 331347943872000), gapWord (8, 1, 7, 0)), ((70258937801719439 / 110449314624000), gapWord (8, 1, 6, 1)), ((143594415935766443 / 82836985968000), gapWord (8, 0, 8, 0)), ((-9921 /
    500), gapWord (7, 7, 2, 0)), ((-35187 / 125), gapWord (7, 7, 1, 1)),
    ((124263376054613 / 418368616000), gapWord (7, 6, 3, 0)), ((-1844673094797201 /
    4602054776000), gapWord (7, 6, 2, 1)), ((61197267667961 / 4602054776000), gapWord (7, 6, 1, 2)), ((287587 / 500), gapWord (7, 6, 0, 3)), ((179638275599637
    / 230102738800), gapWord (7, 5, 4, 0)), ((-2458309119733003 / 4602054776000),
    gapWord (7, 5, 3, 1)), ((-4497651792180039 / 18408219104000), gapWord (7, 5, 2, 2)), ((193527106608807 / 575256847000), gapWord (7, 5, 1, 3)), ((-24436 /
    125), gapWord (7, 5, 0, 4)), ((-1422555642482801 / 1104493146240), gapWord (7, 4, 5, 0)), ((26768 / 125), gapWord (7, 4, 4, 1)), ((2466022263086133 /
    2301027388000), gapWord (7, 4, 3, 2)), ((-575397 / 250), gapWord (7, 4, 2, 3)), ((-324626 / 125), gapWord (7, 4, 1, 4)), ((6971532581128603 /
    3808597056000), gapWord (7, 3, 6, 0)), ((2236774267612717 / 1150513694000),
    gapWord (7, 3, 5, 1)), ((-540732498022313 / 287628423500), gapWord (7, 3, 4, 2)), ((-1127920719515039 / 287628423500), gapWord (7, 3, 3, 3)),
    ((8686943738136283 / 3808597056000), gapWord (7, 2, 7, 0)), ((-200838894419669381 /
    110449314624000), gapWord (7, 2, 6, 1)), ((-188383786292599537 / 55224657312000),
    gapWord (7, 2, 5, 2)), ((-29645923985066273 / 16567397193600), gapWord (7, 1, 7, 1)), ((-18397 / 125), gapWord (6, 6, 4, 0)), ((64867886238229 /
    287628423500), gapWord (6, 6, 3, 1)), ((-142131 / 500), gapWord (6, 6, 2, 2)), ((404919 / 250), gapWord (6, 5, 5, 0)), ((271454 / 125), gapWord (6, 5, 4, 1)), ((-3307728777958427 / 4602054776000), gapWord (6, 5, 3, 2)),
    ((-63814858588029127 / 18408219104000), gapWord (6, 5, 2, 3)), ((-187296 / 125),
    gapWord (6, 5, 1, 4)), ((8519 / 5), gapWord (6, 5, 0, 5)), ((262202 /
    125), gapWord (6, 4, 6, 0)), ((-8933346363762761 / 27612328656000), gapWord (6, 4, 5, 1)), ((-558943 / 125), gapWord (6, 4, 4, 2)),
    ((-3756876205021067 / 2301027388000), gapWord (6, 4, 3, 3)), ((315749 / 125), gapWord (6, 4, 2, 4)), ((-318838162689104881 / 110449314624000), gapWord (6, 3, 6, 1)), ((-2253987316604789 / 1904298528000), gapWord (6, 3, 5, 2)), ((124923 /
    50), gapWord (6, 3, 4, 3)), ((93996490130936561 / 41418492984000), gapWord (6, 2, 6, 2)), ((-64709 / 25), gapWord (5, 5, 5, 1)), ((-85434 / 125), gapWord (5, 5, 4, 2)), ((313067 / 250), gapWord (5, 5, 3, 3)), ((74022 / 25),
    gapWord (5, 4, 5, 2)), ((2250097 / 125), gapWord (5, 4, 4, 3)),
    ((659166 / 125), gapWord (5, 4, 3, 4)), ((2824787 / 2000), gapWord (5, 3, 5, 3)), ((751179 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary15 : Terms :=
  [((-68417 / 1000), gapWord (16, 0, 0, 0)), ((-68417 / 500), gapWord (15, 1, 0, 0)), ((-5846017660467903 / 9204109552000), gapWord (15, 0, 1, 0)),
    ((-68417 / 1000), gapWord (14, 2, 0, 0)), ((-6091675344410783 / 4602054776000),
    gapWord (14, 1, 1, 0)), ((-68417 / 1000), gapWord (14, 1, 0, 1)),
    ((304589 / 1000), gapWord (14, 0, 2, 0)), ((-68417 / 1000), gapWord (13, 3, 0, 0)), ((-6337333028353663 / 4602054776000), gapWord (13, 2, 1, 0)),
    ((-68417 / 1000), gapWord (13, 2, 0, 1)), ((625937 / 500), gapWord (13, 1, 2, 0)), ((-6337333028353663 / 9204109552000), gapWord (13, 1, 1, 1)),
    ((-2611531665528391 / 4602054776000), gapWord (13, 0, 3, 0)), ((-39259 / 500),
    gapWord (12, 4, 0, 0)), ((-6355557165266623 / 4602054776000), gapWord (12, 3, 1, 0)), ((-68417 / 1000), gapWord (12, 3, 0, 1)), ((624543 / 500), gapWord (12, 2, 2, 0)), ((-6582990712296543 / 4602054776000), gapWord (12, 2, 1, 1)), ((-2804891598996807 / 2301027388000), gapWord (12, 1, 3, 0)), ((189457 /
    200), gapWord (12, 1, 2, 1)), ((157252443154387 / 575256847000), gapWord (12, 0, 4, 0)), ((-18111 / 250), gapWord (11, 5, 0, 0)), ((-1391373152725669 /
    1840821910400), gapWord (11, 4, 1, 0)), ((-39259 / 500), gapWord (11, 4, 0, 1)), ((2097378398161687 / 2301027388000), gapWord (11, 3, 2, 0)),
    ((-6601214849209503 / 4602054776000), gapWord (11, 3, 1, 1)), ((-303059524767223 /
    184082191040), gapWord (11, 2, 3, 0)), ((945891 / 500), gapWord (11, 2, 2, 1)), ((-6828648396239423 / 9204109552000), gapWord (11, 2, 1, 2)),
    ((11295882434559 / 20918430800), gapWord (11, 1, 4, 0)), ((-2998251532465223 /
    4602054776000), gapWord (11, 1, 3, 1)), ((-38710673640997 / 41836861600), gapWord (11, 0, 5, 0)), ((-33707 / 500), gapWord (10, 6, 0, 0)),
    ((-305928159758549 / 1150513694000), gapWord (10, 5, 1, 0)), ((-18111 / 250),
    gapWord (10, 5, 0, 1)), ((9323 / 50), gapWord (10, 4, 2, 0)),
    ((-3463378423627159 / 4602054776000), gapWord (10, 4, 1, 1)), ((-2225586708453423 /
    4602054776000), gapWord (10, 3, 3, 0)), ((3231195837434359 / 2301027388000),
    gapWord (10, 3, 2, 1)), ((-6828648396239423 / 4602054776000), gapWord (10, 3, 1, 2)), ((2257481801927749 / 4602054776000), gapWord (10, 2, 4, 0)),
    ((-7850917849583007 / 4602054776000), gapWord (10, 2, 3, 1)), ((117618 / 125),
    gapWord (10, 2, 2, 2)), ((-5177781829746483 / 2301027388000), gapWord (10, 1, 5, 0)), ((450067429207059 / 1150513694000), gapWord (10, 1, 4, 1)),
    ((164039208225231 / 209184308000), gapWord (10, 0, 6, 0)), ((-35413 / 500),
    gapWord (9, 7, 0, 0)), ((-1294324485912311 / 4602054776000), gapWord (9, 6, 1, 0)), ((-33707 / 500), gapWord (9, 6, 0, 1)), ((-7325154246554439 /
    18408219104000), gapWord (9, 5, 2, 0)), ((-80898021738849 / 575256847000), gapWord (9, 5, 1, 1)), ((-2478969139354909 / 4602054776000), gapWord (9, 4, 3, 0)), ((26479 / 50), gapWord (9, 4, 2, 1)), ((-3413354088212039 /
    4602054776000), gapWord (9, 4, 1, 2)), ((-148449399964659 / 575256847000),
    gapWord (9, 3, 4, 0)), ((-1168402685310703 / 4602054776000), gapWord (9, 3, 3, 1)), ((3234265407969951 / 2301027388000), gapWord (9, 3, 2, 2)),
    ((-6828648396239423 / 9204109552000), gapWord (9, 3, 1, 3)), ((-37685985458413177 /
    55224657312000), gapWord (9, 2, 5, 0)), ((848004804660391 / 1150513694000),
    gapWord (9, 2, 4, 1)), ((-11569277499369 / 10459215400), gapWord (9, 2, 3, 2)), ((68402672579041631 / 55224657312000), gapWord (9, 1, 6, 0)),
    ((-402457178645119 / 287628423500), gapWord (9, 1, 5, 1)), ((-3147338507104997 /
    1904298528000), gapWord (9, 0, 7, 0)), ((-17379 / 500), gapWord (8, 8, 0, 0)), ((-158127 / 500), gapWord (8, 7, 1, 0)), ((-35413 / 500), gapWord (8, 7, 0, 1)), ((-1084192747172753 / 4602054776000), gapWord (8, 6, 2, 0)),
    ((-531952368301127 / 4602054776000), gapWord (8, 6, 1, 1)), ((-589070756157327 /
    920410955200), gapWord (8, 5, 3, 0)), ((-5016027242148679 / 18408219104000), gapWord (8, 5, 2, 1)), ((-66974505014061 / 575256847000), gapWord (8, 5, 1, 2)), ((11542 / 25), gapWord (8, 4, 4, 0)), ((-1245626954853387 /
    2301027388000), gapWord (8, 4, 3, 1)), ((126581 / 250), gapWord (8, 4, 2, 2)), ((-3413354088212039 / 4602054776000), gapWord (8, 4, 1, 3)),
    ((-720054996522409 / 2301027388000), gapWord (8, 3, 5, 0)), ((-75546815341621 /
    230102738800), gapWord (8, 3, 4, 1)), ((-53581208045362 / 71907105875), gapWord (8, 3, 3, 2)), ((1069127493395679 / 2301027388000), gapWord (8, 3, 2, 3)), ((-29333827877821 / 142822389600), gapWord (8, 2, 6, 0)),
    ((-1077199137456823 / 1004084678400), gapWord (8, 2, 5, 1)), ((43161 / 125), gapWord (8, 2, 4, 2)), ((64038666958205989 / 165673971936000), gapWord (8, 1, 7, 0)), ((31368648020408687 / 55224657312000), gapWord (8, 1, 6, 1)),
    ((66736282842727463 / 41418492984000), gapWord (8, 0, 8, 0)), ((704 / 25), gapWord (7, 7, 2, 0)), ((-20656 / 125), gapWord (7, 7, 1, 1)), ((4034 / 125),
    gapWord (7, 6, 3, 0)), ((-230941 / 500), gapWord (7, 6, 2, 1)),
    ((-373936215512391 / 4602054776000), gapWord (7, 6, 1, 2)), ((59631 / 125), gapWord (7, 6, 0, 3)), ((345005985703881 / 1150513694000), gapWord (7, 5, 4, 0)), ((-752554150019951 / 920410955200), gapWord (7, 5, 3, 1)),
    ((-4759637566468167 / 18408219104000), gapWord (7, 5, 2, 2)), ((41490124666719 /
    115051369400), gapWord (7, 5, 1, 3)), ((-24436 / 125), gapWord (7, 5, 0, 4)), ((-363492777522801 / 230102738800), gapWord (7, 4, 5, 0)), ((-14726 / 125),
    gapWord (7, 4, 4, 1)), ((96729565133877 / 92041095520), gapWord (7, 4, 3, 2)), ((-581211 / 250), gapWord (7, 4, 2, 3)), ((-324626 / 125), gapWord (7, 4, 1, 4)), ((3233074648511899 / 1904298528000), gapWord (7, 3, 6, 0)),
    ((2049888274700439 / 1150513694000), gapWord (7, 3, 5, 1)), ((-138713044332982 /
    71907105875), gapWord (7, 3, 4, 2)), ((-113993956081941 / 28762842350), gapWord (7, 3, 3, 3)), ((4242112926737371 / 1904298528000), gapWord (7, 2, 7, 0)),
    ((-65873313578690911 / 33134794387200), gapWord (7, 2, 6, 1)),
    ((-188385001235060401 / 55224657312000), gapWord (7, 2, 5, 2)),
    ((-78190720487675953 / 41418492984000), gapWord (7, 1, 7, 1)), ((-50466 / 125),
    gapWord (6, 6, 4, 0)), ((-355012566273479 / 4602054776000), gapWord (6, 6, 3, 1)), ((-72343 / 250), gapWord (6, 6, 2, 2)), ((181421 / 125), gapWord (6, 5, 5, 0)), ((220826 / 125), gapWord (6, 5, 4, 1)), ((-3458740603378091 /
    4602054776000), gapWord (6, 5, 3, 2)), ((-12815368872463451 / 3681643820800),
    gapWord (6, 5, 2, 3)), ((-187296 / 125), gapWord (6, 5, 1, 4)),
    ((8519 / 5), gapWord (6, 5, 0, 5)), ((255016 / 125), gapWord (6, 4, 6, 0)), ((-612406640408853 / 1150513694000), gapWord (6, 4, 5, 1)), ((-1126963
    / 250), gapWord (6, 4, 4, 2)), ((-152186373590411 / 92041095520), gapWord (6, 4, 3, 3)), ((315749 / 125), gapWord (6, 4, 2, 4)), ((-162390962770644241 /
    55224657312000), gapWord (6, 3, 6, 1)), ((-457447083350881 / 380859705600), gapWord (6, 3, 5, 2)), ((123547 / 50), gapWord (6, 3, 4, 3)),
    ((93274255159528061 / 41418492984000), gapWord (6, 2, 6, 2)), ((-64709 / 25), gapWord (5, 5, 5, 1)), ((-85434 / 125), gapWord (5, 5, 4, 2)), ((306141 / 250),
    gapWord (5, 5, 3, 3)), ((74022 / 25), gapWord (5, 4, 5, 2)), ((4491117 /
    250), gapWord (5, 4, 4, 3)), ((659166 / 125), gapWord (5, 4, 3, 4)),
    ((348739 / 250), gapWord (5, 3, 5, 3)), ((751179 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary16 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((262559 / 500), gapWord (14, 0, 2, 0)), ((-1523020548203923 /
    1840821910400), gapWord (13, 2, 1, 0)), ((262559 / 250), gapWord (13, 1, 2, 0)), ((-42723 / 500), gapWord (13, 1, 1, 1)), ((-9619257397261007 /
    9204109552000), gapWord (13, 0, 3, 0)), ((-1523020548203923 / 1840821910400), gapWord (12, 3, 1, 0)), ((733031 / 500), gapWord (12, 2, 2, 0)),
    ((-1523020548203923 / 1840821910400), gapWord (12, 2, 1, 1)), ((-9619257397261007 /
    4602054776000), gapWord (12, 1, 3, 0)), ((262559 / 500), gapWord (12, 1, 2, 1)), ((46108386917169 / 230102738800), gapWord (12, 0, 4, 0)),
    ((-3835380919390343 / 9204109552000), gapWord (11, 4, 1, 0)), ((5525444398749311 /
    4602054776000), gapWord (11, 3, 2, 0)), ((-1523020548203923 / 1840821910400),
    gapWord (11, 3, 1, 1)), ((-8985296739538351 / 4602054776000), gapWord (11, 2, 3, 0)), ((733031 / 500), gapWord (11, 2, 2, 1)), ((-6828648396239423 /
    9204109552000), gapWord (11, 2, 1, 2)), ((1126963593291809 / 2301027388000),
    gapWord (11, 1, 4, 0)), ((-9619257397261007 / 9204109552000), gapWord (11, 1, 3, 1)), ((-4855099473858427 / 4602054776000), gapWord (11, 0, 5, 0)),
    ((-74084679642981 / 1150513694000), gapWord (10, 5, 1, 0)), ((65501 / 125), gapWord (10, 4, 2, 0)), ((-3835380919390343 / 9204109552000), gapWord (10, 4, 1, 1)), ((-1755402070651343 / 4602054776000), gapWord (10, 3, 3, 0)),
    ((5525444398749311 / 4602054776000), gapWord (10, 3, 2, 1)), ((-6828648396239423 /
    4602054776000), gapWord (10, 3, 1, 2)), ((294391374451799 / 575256847000), gapWord (10, 2, 4, 0)), ((-8985296739538351 / 4602054776000), gapWord (10, 2, 3, 1)), ((117618 / 125), gapWord (10, 2, 2, 2)), ((-11727557345510799 /
    4602054776000), gapWord (10, 1, 5, 0)), ((665879724120119 / 2301027388000),
    gapWord (10, 1, 4, 1)), ((161698718759621 / 287628423500), gapWord (10, 0, 6, 0)), ((-554134272321447 / 9204109552000), gapWord (9, 6, 1, 0)),
    ((-180568764759537 / 669389785600), gapWord (9, 5, 2, 0)), ((-74084679642981 /
    1150513694000), gapWord (9, 5, 1, 1)), ((-2898965755733923 / 4602054776000),
    gapWord (9, 4, 3, 0)), ((65501 / 125), gapWord (9, 4, 2, 1)),
    ((-3413354088212039 / 4602054776000), gapWord (9, 4, 1, 2)), ((-731191245194901 /
    1150513694000), gapWord (9, 3, 4, 0)), ((-1755402070651343 / 4602054776000),
    gapWord (9, 3, 3, 1)), ((3234265407969951 / 2301027388000), gapWord (9, 3, 2, 2)), ((-6828648396239423 / 9204109552000), gapWord (9, 3, 1, 3)),
    ((-81376879825488961 / 110449314624000), gapWord (9, 2, 5, 0)),
    ((774369627217003 / 1150513694000), gapWord (9, 2, 4, 1)), ((-11569277499369 /
    10459215400), gapWord (9, 2, 3, 2)), ((24992605249078531 / 22089862924800), gapWord (9, 1, 6, 0)), ((-1718114467913093 / 1150513694000), gapWord (9, 1, 5, 1)), ((-183992520004849201 / 110449314624000), gapWord (9, 0, 7, 0)), ((-24497 /
    250), gapWord (8, 7, 1, 0)), ((-19598 / 125), gapWord (8, 6, 2, 0)),
    ((-554134272321447 / 9204109552000), gapWord (8, 6, 1, 1)), ((-3230000072791787 /
    4602054776000), gapWord (8, 5, 3, 0)), ((-180568764759537 / 669389785600),
    gapWord (8, 5, 2, 1)), ((-66974505014061 / 575256847000), gapWord (8, 5, 1, 2)), ((98897 / 500), gapWord (8, 4, 4, 0)), ((-2898965755733923 /
    4602054776000), gapWord (8, 4, 3, 1)), ((126581 / 250), gapWord (8, 4, 2, 2)), ((-3413354088212039 / 4602054776000), gapWord (8, 4, 1, 3)),
    ((-160661003381311 / 460205477600), gapWord (8, 3, 5, 0)), ((-68200545860187 /
    143814211750), gapWord (8, 3, 4, 1)), ((-53581208045362 / 71907105875), gapWord (8, 3, 3, 2)), ((1069127493395679 / 2301027388000), gapWord (8, 3, 2, 3)), ((-172505352611771 / 714111948000), gapWord (8, 2, 6, 0)),
    ((-118358482919369713 / 110449314624000), gapWord (8, 2, 5, 1)), ((43161 / 125),
    gapWord (8, 2, 4, 2)), ((104501594648420381 / 331347943872000), gapWord (8, 1, 7, 0)), ((5715519840154381 / 10040846784000), gapWord (8, 1, 6, 1)),
    ((13047556495162567 / 8283698596800), gapWord (8, 0, 8, 0)), ((704 / 25), gapWord (7, 7, 2, 0)), ((-24497 / 250), gapWord (7, 7, 1, 1)), ((4034 / 125),
    gapWord (7, 6, 3, 0)), ((-83601 / 250), gapWord (7, 6, 2, 1)),
    ((-373936215512391 / 4602054776000), gapWord (7, 6, 1, 2)), ((59631 / 125), gapWord (7, 6, 0, 3)), ((345005985703881 / 1150513694000), gapWord (7, 5, 4, 0)), ((-4047417042104907 / 4602054776000), gapWord (7, 5, 3, 1)),
    ((-4759637566468167 / 18408219104000), gapWord (7, 5, 2, 2)), ((41490124666719 /
    115051369400), gapWord (7, 5, 1, 3)), ((-24436 / 125), gapWord (7, 5, 0, 4)), ((-363492777522801 / 230102738800), gapWord (7, 4, 5, 0)), ((-190847 / 500),
    gapWord (7, 4, 4, 1)), ((96729565133877 / 92041095520), gapWord (7, 4, 3, 2)), ((-581211 / 250), gapWord (7, 4, 2, 3)), ((-324626 / 125), gapWord (7, 4, 1, 4)), ((3233074648511899 / 1904298528000), gapWord (7, 3, 6, 0)),
    ((1004131632254183 / 575256847000), gapWord (7, 3, 5, 1)), ((-138713044332982 /
    71907105875), gapWord (7, 3, 4, 2)), ((-113993956081941 / 28762842350), gapWord (7, 3, 3, 3)), ((4242112926737371 / 1904298528000), gapWord (7, 2, 7, 0)),
    ((-335360569361113067 / 165673971936000), gapWord (7, 2, 6, 1)),
    ((-188385001235060401 / 55224657312000), gapWord (7, 2, 5, 2)),
    ((-79689220854590581 / 41418492984000), gapWord (7, 1, 7, 1)), ((-50466 / 125),
    gapWord (6, 6, 4, 0)), ((-355012566273479 / 4602054776000), gapWord (6, 6, 3, 1)), ((-72343 / 250), gapWord (6, 6, 2, 2)), ((181421 / 125), gapWord (6, 5, 5, 0)), ((220826 / 125), gapWord (6, 5, 4, 1)), ((-3458740603378091 /
    4602054776000), gapWord (6, 5, 3, 2)), ((-12815368872463451 / 3681643820800),
    gapWord (6, 5, 2, 3)), ((-187296 / 125), gapWord (6, 5, 1, 4)),
    ((8519 / 5), gapWord (6, 5, 0, 5)), ((255016 / 125), gapWord (6, 4, 6, 0)), ((-612406640408853 / 1150513694000), gapWord (6, 4, 5, 1)), ((-1126963
    / 250), gapWord (6, 4, 4, 2)), ((-152186373590411 / 92041095520), gapWord (6, 4, 3, 3)), ((315749 / 125), gapWord (6, 4, 2, 4)), ((-162390962770644241 /
    55224657312000), gapWord (6, 3, 6, 1)), ((-457447083350881 / 380859705600), gapWord (6, 3, 5, 2)), ((123547 / 50), gapWord (6, 3, 4, 3)),
    ((93274255159528061 / 41418492984000), gapWord (6, 2, 6, 2)), ((-64709 / 25), gapWord (5, 5, 5, 1)), ((-85434 / 125), gapWord (5, 5, 4, 2)), ((306141 / 250),
    gapWord (5, 5, 3, 3)), ((74022 / 25), gapWord (5, 4, 5, 2)), ((4491117 /
    250), gapWord (5, 4, 4, 3)), ((659166 / 125), gapWord (5, 4, 3, 4)),
    ((348739 / 250), gapWord (5, 3, 5, 3)), ((751179 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary17 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((262559 / 500), gapWord (14, 0, 2, 0)), ((-42723 / 250), gapWord (13, 2, 1, 0)), ((262559 / 250), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((-9619257397261007 / 9204109552000), gapWord (13, 0, 3, 0)), ((-42723 / 250), gapWord (12, 3, 1, 0)), ((262559 / 250), gapWord (12, 2, 2, 0)), ((-42723 / 250), gapWord (12, 2, 1, 1)),
    ((-9619257397261007 / 4602054776000), gapWord (12, 1, 3, 0)), ((262559 / 500),
    gapWord (12, 1, 2, 1)), ((46108386917169 / 230102738800), gapWord (12, 0, 4, 0)), ((-11463 / 125), gapWord (11, 4, 1, 0)), ((722358073892867 / 920410955200),
    gapWord (11, 3, 2, 0)), ((-42723 / 250), gapWord (11, 3, 1, 1)),
    ((-21545873014338047 / 9204109552000), gapWord (11, 2, 3, 0)), ((262559 / 250),
    gapWord (11, 2, 2, 1)), ((-42723 / 500), gapWord (11, 2, 1, 2)),
    ((1126963593291809 / 2301027388000), gapWord (11, 1, 4, 0)), ((-9619257397261007 /
    9204109552000), gapWord (11, 1, 3, 1)), ((-4855099473858427 / 4602054776000),
    gapWord (11, 0, 5, 0)), ((-309 / 25), gapWord (10, 5, 1, 0)), ((36968 /
    125), gapWord (10, 4, 2, 0)), ((-11463 / 125), gapWord (10, 4, 1, 1)),
    ((-7086083676564031 / 9204109552000), gapWord (10, 3, 3, 0)), ((722358073892867 /
    920410955200), gapWord (10, 3, 2, 1)), ((-42723 / 250), gapWord (10, 3, 1, 2)), ((578981909895909 / 1150513694000), gapWord (10, 2, 4, 0)),
    ((-21545873014338047 / 9204109552000), gapWord (10, 2, 3, 1)), ((262559 / 500),
    gapWord (10, 2, 2, 2)), ((-11727557345510799 / 4602054776000), gapWord (10, 1, 5, 0)), ((665879724120119 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((161698718759621 / 287628423500), gapWord (10, 0, 6, 0)), ((-2749 / 250), gapWord (9, 6, 1, 0)), ((-1600014638356699 / 7363287641600), gapWord (9, 5, 2, 0)), ((-309 / 25), gapWord (9, 5, 1, 1)), ((-2684031389475619 /
    4602054776000), gapWord (9, 4, 3, 0)), ((36968 / 125), gapWord (9, 4, 2, 1)), ((-11463 / 125), gapWord (9, 4, 1, 2)), ((-6736291674569 / 10459215400),
    gapWord (9, 3, 4, 0)), ((-7086083676564031 / 9204109552000), gapWord (9, 3, 3, 1)), ((722358073892867 / 920410955200), gapWord (9, 3, 2, 2)), ((-42723 /
    500), gapWord (9, 3, 1, 3)), ((-79028157966007993 / 110449314624000), gapWord (9, 2, 5, 0)), ((1362759674740247 / 2301027388000), gapWord (9, 2, 4, 1)), ((-13552972292133 / 10459215400), gapWord (9, 2, 3, 2)),
    ((24992605249078531 / 22089862924800), gapWord (9, 1, 6, 0)), ((-1718114467913093 /
    1150513694000), gapWord (9, 1, 5, 1)), ((-183992520004849201 / 110449314624000),
    gapWord (9, 0, 7, 0)), ((-4589 / 250), gapWord (8, 7, 1, 0)), ((-75259 /
    500), gapWord (8, 6, 2, 0)), ((-2749 / 250), gapWord (8, 6, 1, 1)),
    ((-2180648746877819 / 4602054776000), gapWord (8, 5, 3, 0)), ((-1600014638356699 /
    7363287641600), gapWord (8, 5, 2, 1)), ((-309 / 25), gapWord (8, 5, 1, 2)), ((23593 / 500), gapWord (8, 4, 4, 0)), ((-2684031389475619 /
    4602054776000), gapWord (8, 4, 3, 1)), ((36968 / 125), gapWord (8, 4, 2, 2)), ((-11463 / 125), gapWord (8, 4, 1, 3)), ((-318999666722639 / 920410955200),
    gapWord (8, 3, 5, 0)), ((-1277188313456751 / 2301027388000), gapWord (8, 3, 4, 1)), ((-293545059261877 / 287628423500), gapWord (8, 3, 3, 2)),
    ((1195168569600767 / 4602054776000), gapWord (8, 3, 2, 3)), ((-7094464784811853 /
    20709246492000), gapWord (8, 2, 6, 0)), ((-11585887228460243 / 10040846784000),
    gapWord (8, 2, 5, 1)), ((37857 / 125), gapWord (8, 2, 4, 2)),
    ((104501594648420381 / 331347943872000), gapWord (8, 1, 7, 0)),
    ((5715519840154381 / 10040846784000), gapWord (8, 1, 6, 1)), ((13047556495162567 /
    8283698596800), gapWord (8, 0, 8, 0)), ((63 / 25), gapWord (7, 7, 2, 0)), ((-4589 / 250), gapWord (7, 7, 1, 1)), ((6503 / 125), gapWord (7, 6, 3, 0)), ((-84437 / 500), gapWord (7, 6, 2, 1)), ((-2119 / 250), gapWord (7, 6, 1, 2)), ((59631 / 125), gapWord (7, 6, 0, 3)), ((220925384833369 /
    1150513694000), gapWord (7, 5, 4, 0)), ((-90604962573843 / 184082191040), gapWord (7, 5, 3, 1)), ((-1581459153499867 / 7363287641600), gapWord (7, 5, 2, 2)), ((58086 / 125), gapWord (7, 5, 1, 3)), ((-24436 / 125), gapWord (7, 5, 0, 4)), ((-1654339454023909 / 1150513694000), gapWord (7, 4, 5, 0)),
    ((-189187 / 500), gapWord (7, 4, 4, 1)), ((613950404597049 / 920410955200), gapWord (7, 4, 3, 2)), ((-169122 / 125), gapWord (7, 4, 2, 3)), ((-99727 /
    125), gapWord (7, 4, 1, 4)), ((178567905105799727 / 110449314624000), gapWord (7, 3, 6, 0)), ((1592715571487639 / 1150513694000), gapWord (7, 3, 5, 1)), ((-2404435459706031 / 1150513694000), gapWord (7, 3, 4, 2)),
    ((-1164608181098829 / 287628423500), gapWord (7, 3, 3, 3)), ((246178401836570063 /
    110449314624000), gapWord (7, 2, 7, 0)), ((-395434617883372483 / 331347943872000),
    gapWord (7, 2, 6, 1)), ((-376634150384318257 / 110449314624000), gapWord (7, 2, 5, 2)), ((-316509180380633 / 331347943872), gapWord (7, 1, 7, 1)), ((-34414 /
    125), gapWord (6, 6, 4, 0)), ((10257 / 250), gapWord (6, 6, 3, 1)),
    ((-75259 / 500), gapWord (6, 6, 2, 2)), ((137687 / 125), gapWord (6, 5, 5, 0)), ((1185746168621769 / 1150513694000), gapWord (6, 5, 4, 1)),
    ((-2092280091069067 / 4602054776000), gapWord (6, 5, 3, 2)), ((-95207057321968071 /
    36816438208000), gapWord (6, 5, 2, 3)), ((1351 / 25), gapWord (6, 5, 1, 4)), ((319727 / 250), gapWord (6, 5, 0, 5)), ((229301 / 125), gapWord (6, 4, 6, 0)), ((158575596214427 / 1150513694000), gapWord (6, 4, 5, 1)),
    ((-1844643 / 500), gapWord (6, 4, 4, 2)), ((-11218081766090019 / 4602054776000),
    gapWord (6, 4, 3, 3)), ((471991 / 250), gapWord (6, 4, 2, 4)),
    ((-122810995911588337 / 110449314624000), gapWord (6, 3, 6, 1)),
    ((-112298765389264561 / 110449314624000), gapWord (6, 3, 5, 2)),
    ((2093519600040921 / 1150513694000), gapWord (6, 3, 4, 3)), ((13925405857240201 /
    8283698596800), gapWord (6, 2, 6, 2)), ((-95156 / 125), gapWord (5, 5, 5, 1)), ((-35252 / 125), gapWord (5, 5, 4, 2)), ((104073 / 100), gapWord (5, 5, 3, 3)), ((343502 / 125), gapWord (5, 4, 5, 2)), ((1344189 / 100), gapWord (5, 4, 4, 3)), ((396121 / 125), gapWord (5, 4, 3, 4)), ((193959 / 500),
    gapWord (5, 3, 5, 3)), ((119478 / 25), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary18 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((27323 / 250), gapWord (14, 0, 2, 0)), ((-42723 / 250), gapWord (13, 2, 1, 0)), ((27323 / 125), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((-6838316940107069 / 41418492984000), gapWord (13, 0, 3, 0)), ((-42723 / 250), gapWord (12, 3, 1, 0)), ((27323 / 125), gapWord (12, 2, 2, 0)), ((-42723 / 250), gapWord (12, 2, 1, 1)), ((-6838316940107069 /
    20709246492000), gapWord (12, 1, 3, 0)), ((27323 / 250), gapWord (12, 1, 2, 1)), ((59001149752879 / 230102738800), gapWord (12, 0, 4, 0)), ((-11463 / 125),
    gapWord (11, 4, 1, 0)), ((41017 / 250), gapWord (11, 3, 2, 0)), ((-42723 /
    250), gapWord (11, 3, 1, 1)), ((-48119491738772573 / 82836985968000), gapWord (11, 2, 3, 0)), ((27323 / 125), gapWord (11, 2, 2, 1)), ((-42723 / 500),
    gapWord (11, 2, 1, 2)), ((125892622727819 / 209184308000), gapWord (11, 1, 4, 0)), ((-6838316940107069 / 41418492984000), gapWord (11, 1, 3, 1)),
    ((-5957273184491323 / 4602054776000), gapWord (11, 0, 5, 0)), ((-309 / 25), gapWord (10, 5, 1, 0)), ((21291 / 250), gapWord (10, 4, 2, 0)), ((-11463 / 125),
    gapWord (10, 4, 1, 1)), ((244069170648769 / 9204109552000), gapWord (10, 3, 3, 0)), ((41017 / 250), gapWord (10, 3, 2, 1)), ((-42723 / 250), gapWord (10, 3, 1, 2)), ((625009892641803 / 1150513694000), gapWord (10, 2, 4, 0)), ((-48119491738772573 / 82836985968000), gapWord (10, 2, 3, 1)), ((27323 /
    250), gapWord (10, 2, 2, 2)), ((-13225360501126863 / 4602054776000), gapWord (10, 1, 5, 0)), ((794807352477219 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((152094230442109 / 287628423500), gapWord (10, 0, 6, 0)), ((-2749 / 250), gapWord (9, 6, 1, 0)), ((-1213772864358491 / 7363287641600), gapWord (9, 5, 2, 0)), ((-309 / 25), gapWord (9, 5, 1, 1)), ((-2340018590860067 /
    4602054776000), gapWord (9, 4, 3, 0)), ((21291 / 250), gapWord (9, 4, 2, 1)), ((-11463 / 125), gapWord (9, 4, 1, 2)), ((-20021618468291 / 52296077000),
    gapWord (9, 3, 4, 0)), ((244069170648769 / 9204109552000), gapWord (9, 3, 3, 1)), ((41017 / 250), gapWord (9, 3, 2, 2)), ((-42723 / 500), gapWord (9, 3, 1, 3)), ((-110610697685482297 / 110449314624000), gapWord (9, 2, 5, 0)),
    ((290963128046407 / 460205477600), gapWord (9, 2, 4, 1)), ((-626233779246517 /
    1506127017600), gapWord (9, 2, 3, 2)), ((114144338985535247 / 110449314624000),
    gapWord (9, 1, 6, 0)), ((-363404365831777 / 230102738800), gapWord (9, 1, 5, 1)), ((-6590451163820069 / 3808597056000), gapWord (9, 0, 7, 0)), ((-4589 /
    500), gapWord (8, 7, 1, 0)), ((-80451 / 500), gapWord (8, 6, 2, 0)),
    ((-2749 / 250), gapWord (8, 6, 1, 1)), ((-2436118011603131 / 4602054776000),
    gapWord (8, 5, 3, 0)), ((-1213772864358491 / 7363287641600), gapWord (8, 5, 2, 1)), ((-309 / 25), gapWord (8, 5, 1, 2)), ((102771 / 500), gapWord (8, 4, 4, 0)), ((-2340018590860067 / 4602054776000), gapWord (8, 4, 3, 1)), ((21291 / 250), gapWord (8, 4, 2, 2)), ((-11463 / 125), gapWord (8, 4, 1, 3)), ((-1783602510906643 / 4602054776000), gapWord (8, 3, 5, 0)),
    ((-5409242861251 / 18408219104), gapWord (8, 3, 4, 1)), ((-64477782786477 /
    287628423500), gapWord (8, 3, 3, 2)), ((6847 / 125), gapWord (8, 3, 2, 3)), ((-805538458259747 / 1428223896000), gapWord (8, 2, 6, 0)),
    ((-2583095215580791 / 2008169356800), gapWord (8, 2, 5, 1)), ((35854 / 125), gapWord (8, 2, 4, 2)), ((20800788193124149 / 331347943872000), gapWord (8, 1, 7, 0)), ((55740154495765391 / 110449314624000), gapWord (8, 1, 6, 1)),
    ((122686925549438441 / 82836985968000), gapWord (8, 0, 8, 0)), ((-289 / 25),
    gapWord (7, 7, 2, 0)), ((-4589 / 500), gapWord (7, 7, 1, 1)), ((-1298 /
    25), gapWord (7, 6, 3, 0)), ((-4252 / 25), gapWord (7, 6, 2, 1)),
    ((-5639 / 250), gapWord (7, 6, 1, 2)), ((59631 / 250), gapWord (7, 6, 0, 3)), ((-21197921041543 / 1150513694000), gapWord (7, 5, 4, 0)),
    ((-2478355670337259 / 4602054776000), gapWord (7, 5, 3, 1)), ((-1298892469495387 /
    7363287641600), gapWord (7, 5, 2, 2)), ((56541 / 250), gapWord (7, 5, 1, 3)), ((-12218 / 125), gapWord (7, 5, 0, 4)), ((-1252083050163301 /
    1150513694000), gapWord (7, 4, 5, 0)), ((-126777 / 500), gapWord (7, 4, 4, 1)), ((3578776097649053 / 4602054776000), gapWord (7, 4, 3, 2)), ((-318927
    / 250), gapWord (7, 4, 2, 3)), ((-157191 / 125), gapWord (7, 4, 1, 4)),
    ((130817352914405807 / 110449314624000), gapWord (7, 3, 6, 0)),
    ((1012462501912437 / 1150513694000), gapWord (7, 3, 5, 1)), ((-1648950642540931 /
    1150513694000), gapWord (7, 3, 4, 2)), ((-561331723595153 / 287628423500), gapWord (7, 3, 3, 3)), ((8243028899677147 / 3808597056000), gapWord (7, 2, 7, 0)), ((-335730685014418091 / 331347943872000), gapWord (7, 2, 6, 1)),
    ((-383408890444725169 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-86915934497345479 / 82836985968000), gapWord (7, 1, 7, 1)), ((-34414 / 125),
    gapWord (6, 6, 4, 0)), ((-15729 / 250), gapWord (6, 6, 3, 1)), ((-80451 /
    500), gapWord (6, 6, 2, 2)), ((137687 / 125), gapWord (6, 5, 5, 0)),
    ((943622862746857 / 1150513694000), gapWord (6, 5, 4, 1)), ((-1988531368198923 /
    4602054776000), gapWord (6, 5, 3, 2)), ((-71366793659006919 / 36816438208000),
    gapWord (6, 5, 2, 3)), ((1351 / 25), gapWord (6, 5, 1, 4)), ((319727 /
    250), gapWord (6, 5, 0, 5)), ((229301 / 125), gapWord (6, 4, 6, 0)),
    ((152924272949499 / 1150513694000), gapWord (6, 4, 5, 1)), ((-1427371 / 500),
    gapWord (6, 4, 4, 2)), ((-2676226304575523 / 4602054776000), gapWord (6, 4, 3, 3)), ((287312 / 125), gapWord (6, 4, 2, 4)), ((-146311296584136817 /
    110449314624000), gapWord (6, 3, 6, 1)), ((-43407811380361 / 30468776448), gapWord (6, 3, 5, 2)), ((630923 / 500), gapWord (6, 3, 4, 3)),
    ((131465419170214781 / 82836985968000), gapWord (6, 2, 6, 2)), ((-95156 / 125),
    gapWord (5, 5, 5, 1)), ((70464 / 125), gapWord (5, 5, 4, 2)), ((444301 /
    500), gapWord (5, 5, 3, 3)), ((52512 / 25), gapWord (5, 4, 5, 2)),
    ((5099213 / 500), gapWord (5, 4, 4, 3)), ((501653 / 125), gapWord (5, 4, 3, 4)), ((-351837 / 500), gapWord (5, 3, 5, 3)), ((751179 / 250), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary19 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((27323 / 250), gapWord (14, 0, 2, 0)), ((-42723 / 250), gapWord (13, 2, 1, 0)), ((27323 / 125), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((-4168559063415113 / 7530635088000), gapWord (13, 0, 3, 0)), ((-42723 / 250), gapWord (12, 3, 1, 0)), ((27323 / 125), gapWord (12, 2, 2, 0)), ((-42723 / 250), gapWord (12, 2, 1, 1)), ((-4168559063415113 /
    3765317544000), gapWord (12, 1, 3, 0)), ((27323 / 250), gapWord (12, 1, 2, 1)), ((71893912588589 / 230102738800), gapWord (12, 0, 4, 0)), ((-11463 / 125),
    gapWord (11, 4, 1, 0)), ((41017 / 250), gapWord (11, 3, 2, 0)), ((-42723 /
    250), gapWord (11, 3, 1, 1)), ((-4363994105218889 / 3765317544000), gapWord (11, 2, 3, 0)), ((27323 / 125), gapWord (11, 2, 2, 1)), ((-42723 / 500),
    gapWord (11, 2, 1, 2)), ((1642674106720209 / 2301027388000), gapWord (11, 1, 4, 0)), ((-4168559063415113 / 7530635088000), gapWord (11, 1, 3, 1)),
    ((-937940897841851 / 4602054776000), gapWord (11, 0, 5, 0)), ((-309 / 25), gapWord (10, 5, 1, 0)), ((21291 / 250), gapWord (10, 4, 2, 0)), ((-11463 / 125),
    gapWord (10, 4, 1, 1)), ((-104100323894143 / 287628423500), gapWord (10, 3, 3, 0)), ((41017 / 250), gapWord (10, 3, 2, 1)), ((-42723 / 250), gapWord (10, 3, 1, 2)), ((133667293846837 / 230102738800), gapWord (10, 2, 4, 0)), ((-4363994105218889 / 3765317544000), gapWord (10, 2, 3, 1)), ((27323 /
    250), gapWord (10, 2, 2, 2)), ((-3194675890809503 / 4602054776000), gapWord (10, 1, 5, 0)), ((923734980834319 / 2301027388000), gapWord (10, 1, 4, 1)),
    ((1011142407648823 / 2301027388000), gapWord (10, 0, 6, 0)), ((-2749 / 500), gapWord (9, 6, 1, 0)), ((-18044 / 125), gapWord (9, 5, 2, 0)), ((-309 / 25),
    gapWord (9, 5, 1, 1)), ((-2156092869682451 / 4602054776000), gapWord (9, 4, 3, 0)), ((21291 / 250), gapWord (9, 4, 2, 1)), ((-11463 / 125), gapWord (9, 4, 1, 2)), ((-8276756311323 / 52296077000), gapWord (9, 3, 4, 0)),
    ((-104100323894143 / 287628423500), gapWord (9, 3, 3, 1)), ((41017 / 250), gapWord (9, 3, 2, 2)), ((-42723 / 500), gapWord (9, 3, 1, 3)),
    ((-4210013138339641 / 110449314624000), gapWord (9, 2, 5, 0)), ((1541468793416799 /
    2301027388000), gapWord (9, 2, 4, 1)), ((-911885829404533 / 1506127017600),
    gapWord (9, 2, 3, 2)), ((87259076593566719 / 110449314624000), gapWord (9, 1, 6, 0)), ((-564183748241913 / 1150513694000), gapWord (9, 1, 5, 1)),
    ((-7634996992398629 / 3808597056000), gapWord (9, 0, 7, 0)), ((-4589 / 500), gapWord (8, 7, 1, 0)), ((-11241 / 500), gapWord (8, 6, 2, 0)), ((-2749 / 500),
    gapWord (8, 6, 1, 1)), ((-3755794035059339 / 9204109552000), gapWord (8, 5, 3, 0)), ((-18044 / 125), gapWord (8, 5, 2, 1)), ((-309 / 25), gapWord (8, 5, 1, 2)), ((32297 / 100), gapWord (8, 4, 4, 0)), ((-2156092869682451 /
    4602054776000), gapWord (8, 4, 3, 1)), ((21291 / 250), gapWord (8, 4, 2, 2)), ((-11463 / 125), gapWord (8, 4, 1, 3)), ((-1629820248511827 /
    4602054776000), gapWord (8, 3, 5, 0)), ((-159381422749783 / 2301027388000),
    gapWord (8, 3, 4, 1)), ((-119029389587487 / 287628423500), gapWord (8, 3, 3, 2)), ((6847 / 125), gapWord (8, 3, 2, 3)), ((-108114300925207 / 285644779200),
    gapWord (8, 2, 6, 0)), ((-652019480388343 / 2008169356800), gapWord (8, 2, 5, 1)), ((13423 / 50), gapWord (8, 2, 4, 2)), ((-25275046706604991 /
    66269588774400), gapWord (8, 1, 7, 0)), ((7744848205284643 / 22089862924800),
    gapWord (8, 1, 6, 1)), ((115649358719461643 / 82836985968000), gapWord (8, 0, 8, 0)), ((-289 / 25), gapWord (7, 7, 2, 0)), ((-4589 / 500), gapWord (7, 7, 1, 1)), ((-3272 / 125), gapWord (7, 6, 3, 0)), ((-1583 / 50), gapWord (7, 6, 2, 1)), ((-8529 / 500), gapWord (7, 6, 1, 2)), ((26067 / 250),
    gapWord (7, 6, 0, 3)), ((79909222387177 / 2301027388000), gapWord (7, 5, 4, 0)), ((-768053870505519 / 1840821910400), gapWord (7, 5, 3, 1)), ((-19489 /
    125), gapWord (7, 5, 2, 2)), ((22977 / 250), gapWord (7, 5, 1, 3)),
    ((-12218 / 125), gapWord (7, 5, 0, 4)), ((-3378959481329909 / 2301027388000),
    gapWord (7, 4, 5, 0)), ((-68063 / 500), gapWord (7, 4, 4, 1)),
    ((2050332461334381 / 4602054776000), gapWord (7, 4, 3, 2)), ((-432037 / 250),
    gapWord (7, 4, 2, 3)), ((-157191 / 125), gapWord (7, 4, 1, 4)),
    ((757045963060511 / 761719411200), gapWord (7, 3, 6, 0)), ((209782615353149 /
    230102738800), gapWord (7, 3, 5, 1)), ((-1023057386840603 / 1150513694000),
    gapWord (7, 3, 4, 2)), ((-561331723595153 / 287628423500), gapWord (7, 3, 3, 3)), ((6021367596194779 / 3808597056000), gapWord (7, 2, 7, 0)),
    ((-31187727977183983 / 66269588774400), gapWord (7, 2, 6, 1)),
    ((-188716790976190897 / 110449314624000), gapWord (7, 2, 5, 2)),
    ((-93953501327322277 / 82836985968000), gapWord (7, 1, 7, 1)), ((-74528 / 125),
    gapWord (6, 6, 4, 0)), ((-15837 / 500), gapWord (6, 6, 3, 1)), ((-11241 /
    500), gapWord (6, 6, 2, 2)), ((185539 / 250), gapWord (6, 5, 5, 0)),
    ((1272669779230857 / 2301027388000), gapWord (6, 5, 4, 1)), ((-2042964472089451 /
    9204109552000), gapWord (6, 5, 3, 2)), ((-210452 / 125), gapWord (6, 5, 2, 3)), ((-143329 / 125), gapWord (6, 5, 1, 4)), ((8519 / 10), gapWord (6, 5, 0, 5)), ((34822 / 25), gapWord (6, 4, 6, 0)), ((474340982614891 /
    2301027388000), gapWord (6, 4, 5, 1)), ((-786083 / 500), gapWord (6, 4, 4, 2)), ((-6191763560290579 / 4602054776000), gapWord (6, 4, 3, 3)), ((20772 /
    125), gapWord (6, 4, 2, 4)), ((35918130853196783 / 110449314624000), gapWord (6, 3, 6, 1)), ((-1100811730645733 / 3808597056000), gapWord (6, 3, 5, 2)), ((73067 / 100), gapWord (6, 3, 4, 3)), ((9506466840777241 /
    16567397193600), gapWord (6, 2, 6, 2)), ((-32572 / 25), gapWord (5, 5, 5, 1)), ((-14893 / 25), gapWord (5, 5, 4, 2)), ((298677 / 500), gapWord (5, 5, 3, 3)), ((178629 / 125), gapWord (5, 4, 5, 2)), ((4500637 / 500), gapWord (5, 4, 4, 3)), ((329483 / 125), gapWord (5, 4, 3, 4)), ((366759 / 500),
    gapWord (5, 3, 5, 3)), ((751179 / 250), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary20 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((27323 / 250), gapWord (14, 0, 2, 0)), ((-42723 / 250), gapWord (13, 2, 1, 0)), ((27323 / 125), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((-4168559063415113 / 7530635088000), gapWord (13, 0, 3, 0)), ((-42723 / 250), gapWord (12, 3, 1, 0)), ((27323 / 125), gapWord (12, 2, 2, 0)), ((-42723 / 250), gapWord (12, 2, 1, 1)), ((-4168559063415113 /
    3765317544000), gapWord (12, 1, 3, 0)), ((27323 / 250), gapWord (12, 1, 2, 1)), ((75981 / 250), gapWord (12, 0, 4, 0)), ((-11463 / 125), gapWord (11, 4, 1, 0)), ((41017 / 250), gapWord (11, 3, 2, 0)), ((-42723 / 250),
    gapWord (11, 3, 1, 1)), ((-4363994105218889 / 3765317544000), gapWord (11, 2, 3, 0)), ((27323 / 125), gapWord (11, 2, 2, 1)), ((-42723 / 500), gapWord (11, 2, 1, 2)), ((308353 / 500), gapWord (11, 1, 4, 0)),
    ((-4168559063415113 / 7530635088000), gapWord (11, 1, 3, 1)), ((-2021780022247163 /
    4602054776000), gapWord (11, 0, 5, 0)), ((-309 / 50), gapWord (10, 5, 1, 0)), ((45047 / 500), gapWord (10, 4, 2, 0)), ((-11463 / 125), gapWord (10, 4, 1, 1)), ((-114057 / 250), gapWord (10, 3, 3, 0)), ((41017 / 250), gapWord (10, 3, 2, 1)), ((-42723 / 250), gapWord (10, 3, 1, 2)), ((66244 / 125), gapWord (10, 2, 4, 0)), ((-4363994105218889 / 3765317544000), gapWord (10, 2, 3, 1)), ((27323 / 250), gapWord (10, 2, 2, 2)), ((-1047369380353811 /
    920410955200), gapWord (10, 1, 5, 0)), ((156391 / 500), gapWord (10, 1, 4, 1)), ((378804887689143 / 1150513694000), gapWord (10, 0, 6, 0)), ((-2749 / 500),
    gapWord (9, 6, 1, 0)), ((-9242 / 125), gapWord (9, 5, 2, 0)), ((-309 /
    50), gapWord (9, 5, 1, 1)), ((-247071 / 500), gapWord (9, 4, 3, 0)), ((45047 / 500), gapWord (9, 4, 2, 1)), ((-11463 / 125), gapWord (9, 4, 1, 2)), ((-8685908283942 / 71907105875), gapWord (9, 3, 4, 0)), ((-114057
    / 250), gapWord (9, 3, 3, 1)), ((41017 / 250), gapWord (9, 3, 2, 2)),
    ((-42723 / 500), gapWord (9, 3, 1, 3)), ((-36368435584263481 / 110449314624000),
    gapWord (9, 2, 5, 0)), ((53881 / 100), gapWord (9, 2, 4, 1)),
    ((-911885829404533 / 1506127017600), gapWord (9, 2, 3, 2)), ((63342470880062063 /
    110449314624000), gapWord (9, 1, 6, 0)), ((-803766719880473 / 1150513694000),
    gapWord (9, 1, 5, 1)), ((-635068624251553 / 761719411200), gapWord (9, 0, 7, 0)), ((-4589 / 500), gapWord (8, 7, 1, 0)), ((-11241 / 500), gapWord (8, 6, 2, 0)), ((-2749 / 500), gapWord (8, 6, 1, 1)), ((-1776579133435467 /
    9204109552000), gapWord (8, 5, 3, 0)), ((-9242 / 125), gapWord (8, 5, 2, 1)), ((-309 / 50), gapWord (8, 5, 1, 2)), ((187501 / 500), gapWord (8, 4, 4, 0)), ((-247071 / 500), gapWord (8, 4, 3, 1)), ((45047 / 500), gapWord (8, 4, 2, 2)), ((-11463 / 125), gapWord (8, 4, 1, 3)),
    ((-599843573204819 / 4602054776000), gapWord (8, 3, 5, 0)), ((-6439164112081 /
    57525684700), gapWord (8, 3, 4, 1)), ((-127033 / 250), gapWord (8, 3, 3, 2)), ((6847 / 125), gapWord (8, 3, 2, 3)), ((-156287870272691 /
    1428223896000), gapWord (8, 2, 6, 0)), ((-5909756378077907 / 10040846784000),
    gapWord (8, 2, 5, 1)), ((56507 / 250), gapWord (8, 2, 4, 2)),
    ((173950590441902917 / 331347943872000), gapWord (8, 1, 7, 0)),
    ((186049666633823 / 761719411200), gapWord (8, 1, 6, 1)), ((66014047871318963 /
    82836985968000), gapWord (8, 0, 8, 0)), ((-289 / 25), gapWord (7, 7, 2, 0)), ((-4589 / 500), gapWord (7, 7, 1, 1)), ((-3272 / 125), gapWord (7, 6, 3, 0)), ((-1583 / 50), gapWord (7, 6, 2, 1)), ((-8529 / 500), gapWord (7, 6, 1, 2)), ((26067 / 250), gapWord (7, 6, 0, 3)), ((7696810302033 /
    92041095520), gapWord (7, 5, 4, 0)), ((-1861054450903723 / 9204109552000), gapWord (7, 5, 3, 1)), ((-10687 / 125), gapWord (7, 5, 2, 2)), ((12261 / 125),
    gapWord (7, 5, 1, 3)), ((-6419 / 125), gapWord (7, 5, 0, 4)), ((-71794 /
    125), gapWord (7, 4, 5, 0)), ((56169 / 500), gapWord (7, 4, 4, 1)),
    ((41989 / 100), gapWord (7, 4, 3, 2)), ((-1082689 / 500), gapWord (7, 4, 2, 3)), ((-42931 / 25), gapWord (7, 4, 1, 4)), ((3361013040817051 /
    3808597056000), gapWord (7, 3, 6, 0)), ((585035159454497 / 1150513694000), gapWord (7, 3, 5, 1)), ((-12428790363761 / 14381421175), gapWord (7, 3, 4, 2)), ((-279214 / 125), gapWord (7, 3, 3, 3)), ((4242112926737371 /
    3808597056000), gapWord (7, 2, 7, 0)), ((60540249588086101 / 331347943872000),
    gapWord (7, 2, 6, 1)), ((-194863074436387249 / 110449314624000), gapWord (7, 2, 5, 2)), ((16378737023176283 / 82836985968000), gapWord (7, 1, 7, 1)),
    ((-16416 / 125), gapWord (6, 6, 4, 0)), ((-15837 / 500), gapWord (6, 6, 3, 1)), ((-11241 / 500), gapWord (6, 6, 2, 2)), ((9444 / 25), gapWord (6, 5, 5, 0)), ((1232687127336969 / 2301027388000), gapWord (6, 5, 4, 1)),
    ((-1367198748781611 / 9204109552000), gapWord (6, 5, 3, 2)), ((-113452 / 125),
    gapWord (6, 5, 2, 3)), ((-102236 / 125), gapWord (6, 5, 1, 4)),
    ((106223 / 250), gapWord (6, 5, 0, 5)), ((80906 / 125), gapWord (6, 4, 6, 0)), ((16992 / 25), gapWord (6, 4, 5, 1)), ((-288387 / 500), gapWord (6, 4, 4, 2)), ((-80643 / 100), gapWord (6, 4, 3, 3)), ((-55149 / 125), gapWord (6, 4, 2, 4)), ((44218617745819631 / 110449314624000), gapWord (6, 3, 6, 1)), ((424241936906011 / 3808597056000), gapWord (6, 3, 5, 2)), ((35379444123303
    / 230102738800), gapWord (6, 3, 4, 3)), ((9506466840777241 / 16567397193600),
    gapWord (6, 2, 6, 2)), ((8226 / 25), gapWord (5, 5, 5, 1)), ((58247 /
    125), gapWord (5, 5, 4, 2)), ((70799 / 500), gapWord (5, 5, 3, 3)),
    ((101124 / 125), gapWord (5, 4, 5, 2)), ((2297637 / 500), gapWord (5, 4, 4, 3)), ((51809 / 25), gapWord (5, 4, 3, 4)), ((555167 / 500), gapWord (5, 3, 5, 3)), ((153789 / 125), gapWord (4, 4, 4, 4))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary21 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((27323 / 250), gapWord (14, 0, 2, 0)), ((-42723 / 250), gapWord (13, 2, 1, 0)), ((27323 / 125), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((-4168559063415113 / 7530635088000), gapWord (13, 0, 3, 0)), ((-42723 / 250), gapWord (12, 3, 1, 0)), ((27323 / 125), gapWord (12, 2, 2, 0)), ((-42723 / 250), gapWord (12, 2, 1, 1)), ((-4356350510604569 /
    3765317544000), gapWord (12, 1, 3, 0)), ((27323 / 250), gapWord (12, 1, 2, 1)), ((152217 / 500), gapWord (12, 0, 4, 0)), ((-11463 / 250), gapWord (11, 4, 1, 0)), ((3417 / 25), gapWord (11, 3, 2, 0)), ((-42723 / 250),
    gapWord (11, 3, 1, 1)), ((-4454068031506457 / 3765317544000), gapWord (11, 2, 3, 0)), ((27323 / 125), gapWord (11, 2, 2, 1)), ((-42723 / 500), gapWord (11, 2, 1, 2)), ((58093 / 125), gapWord (11, 1, 4, 0)),
    ((-181765678311761 / 301225403520), gapWord (11, 1, 3, 1)), ((-82933 / 125),
    gapWord (11, 0, 5, 0)), ((-309 / 50), gapWord (10, 5, 1, 0)), ((21291 /
    500), gapWord (10, 4, 2, 0)), ((-11463 / 250), gapWord (10, 4, 1, 1)),
    ((-43493 / 250), gapWord (10, 3, 3, 0)), ((3417 / 25), gapWord (10, 3, 2, 1)), ((-42723 / 250), gapWord (10, 3, 1, 2)), ((209311 / 500), gapWord (10, 2, 4, 0)), ((-4641859478695913 / 3765317544000), gapWord (10, 2, 3, 1)),
    ((27323 / 250), gapWord (10, 2, 2, 2)), ((-269729 / 500), gapWord (10, 1, 5, 0)), ((16031 / 100), gapWord (10, 1, 4, 1)), ((231493114309383 /
    1150513694000), gapWord (10, 0, 6, 0)), ((-2749 / 500), gapWord (9, 6, 1, 0)), ((-9242 / 125), gapWord (9, 5, 2, 0)), ((-309 / 50), gapWord (9, 5, 1, 1)), ((-132399 / 500), gapWord (9, 4, 3, 0)), ((21291 / 500), gapWord (9, 4, 2, 1)), ((-11463 / 250), gapWord (9, 4, 1, 2)), ((-132640942253147 /
    1150513694000), gapWord (9, 3, 4, 0)), ((-111923 / 500), gapWord (9, 3, 3, 1)), ((3417 / 25), gapWord (9, 3, 2, 2)), ((-42723 / 500), gapWord (9, 3, 1, 3)), ((-62443 / 500), gapWord (9, 2, 5, 0)), ((137249 / 500),
    gapWord (9, 2, 4, 1)), ((-4739576999597801 / 7530635088000), gapWord (9, 2, 3, 2)), ((2781841578475309 / 10040846784000), gapWord (9, 1, 6, 0)),
    ((62003 / 500), gapWord (9, 1, 5, 1)), ((1229939218311643 / 3808597056000),
    gapWord (9, 0, 7, 0)), ((-4589 / 500), gapWord (8, 7, 1, 0)), ((-11241 /
    500), gapWord (8, 6, 2, 0)), ((-2749 / 500), gapWord (8, 6, 1, 1)),
    ((-1776579133435467 / 9204109552000), gapWord (8, 5, 3, 0)), ((-9242 / 125), gapWord (8, 5, 2, 1)), ((-309 / 50), gapWord (8, 5, 1, 2)), ((-11384 / 125),
    gapWord (8, 4, 4, 0)), ((-17727 / 500), gapWord (8, 4, 3, 1)), ((21291 /
    500), gapWord (8, 4, 2, 2)), ((-11463 / 250), gapWord (8, 4, 1, 3)),
    ((44953 / 250), gapWord (8, 3, 5, 0)), ((18918527684861 / 1150513694000), gapWord (8, 3, 4, 1)), ((-124899 / 500), gapWord (8, 3, 3, 2)), ((6847 / 250),
    gapWord (8, 3, 2, 3)), ((882618728697053 / 3313479438720), gapWord (8, 2, 6, 0)), ((7841 / 125), gapWord (8, 2, 5, 1)), ((587 / 250), gapWord (8, 2, 4, 2)), ((161740810005789901 / 331347943872000), gapWord (8, 1, 7, 0)),
    ((11473917171584591 / 110449314624000), gapWord (8, 1, 6, 1)),
    ((16378737023176283 / 82836985968000), gapWord (8, 0, 8, 0)), ((-289 / 25), gapWord (7, 7, 2, 0)), ((-4589 / 500), gapWord (7, 7, 1, 1)), ((-3272 / 125),
    gapWord (7, 6, 3, 0)), ((-1583 / 50), gapWord (7, 6, 2, 1)), ((-8529 /
    500), gapWord (7, 6, 1, 2)), ((26067 / 250), gapWord (7, 6, 0, 3)),
    ((495806116603849 / 2301027388000), gapWord (7, 5, 4, 0)), ((86492476740369 /
    1840821910400), gapWord (7, 5, 3, 1)), ((-88 / 25), gapWord (7, 5, 2, 2)), ((-309 / 50), gapWord (7, 5, 1, 3)), ((45934 / 125), gapWord (7, 4, 5, 0)), ((15008 / 125), gapWord (7, 4, 4, 1)), ((3369 / 500), gapWord (7, 4, 3, 2)), ((-493 / 100), gapWord (7, 4, 2, 3)), ((2967476753817901 /
    10040846784000), gapWord (7, 3, 6, 0)), ((92773 / 500), gapWord (7, 3, 5, 1)), ((5669 / 500), gapWord (7, 3, 4, 2)), ((1067 / 125), gapWord (7, 3, 3, 3)), ((48239390759519 / 761719411200), gapWord (7, 2, 7, 0)),
    ((40119509291704673 / 331347943872000), gapWord (7, 2, 6, 1)), ((-4599 / 500),
    gapWord (7, 2, 5, 2)), ((1868234038639897 / 16567397193600), gapWord (7, 1, 7, 1)), ((8412 / 25), gapWord (6, 6, 4, 0)), ((18191 / 500), gapWord (6, 6, 3, 1)), ((-333 / 20), gapWord (6, 6, 2, 2)), ((8226 / 25), gapWord (6, 5, 5, 0)), ((29418 / 125), gapWord (6, 5, 4, 1)), ((-3543 / 250),
    gapWord (6, 5, 3, 2)), ((-88 / 25), gapWord (6, 5, 2, 3)), ((5143 /
    25), gapWord (6, 4, 6, 0)), ((20182 / 125), gapWord (6, 4, 5, 1)),
    ((883 / 25), gapWord (6, 4, 4, 2)), ((3369 / 500), gapWord (6, 4, 3, 3)), ((-1151764881714097 / 110449314624000), gapWord (6, 3, 6, 1)), ((14143 /
    500), gapWord (6, 3, 5, 2)), ((899 / 100), gapWord (6, 3, 4, 3)),
    ((9371 / 500), gapWord (6, 2, 6, 2)), ((1239 / 500), gapWord (5, 5, 3, 3)), ((883 / 25), gapWord (5, 4, 4, 3)), ((9371 / 500), gapWord (5, 3, 5, 3))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary22 : Terms :=
  [((-42723 / 500), gapWord (15, 0, 1, 0)), ((-42723 / 250), gapWord (14, 1, 1, 0)), ((27323 / 500), gapWord (14, 0, 2, 0)), ((-42723 / 500), gapWord (13, 2, 1, 0)), ((27323 / 250), gapWord (13, 1, 2, 0)), ((-42723 / 500),
    gapWord (13, 1, 1, 1)), ((24937 / 500), gapWord (13, 0, 3, 0)), ((-42723 /
    500), gapWord (12, 3, 1, 0)), ((27323 / 500), gapWord (12, 2, 2, 0)),
    ((-42723 / 500), gapWord (12, 2, 1, 1)), ((24937 / 250), gapWord (12, 1, 3, 0)), ((27323 / 500), gapWord (12, 1, 2, 1)), ((-51 / 100), gapWord (12, 0, 4, 0)), ((-11463 / 250), gapWord (11, 4, 1, 0)), ((6847 / 250), gapWord (11, 3, 2, 0)), ((-42723 / 500), gapWord (11, 3, 1, 1)), ((11961 / 500), gapWord (11, 2, 3, 0)), ((27323 / 500), gapWord (11, 2, 2, 1)), ((916 / 125),
    gapWord (11, 1, 4, 0)), ((24937 / 500), gapWord (11, 1, 3, 1)), ((-498 /
    125), gapWord (11, 0, 5, 0)), ((-309 / 50), gapWord (10, 5, 1, 0)),
    ((-493 / 100), gapWord (10, 4, 2, 0)), ((-11463 / 250), gapWord (10, 4, 1, 1)), ((1067 / 125), gapWord (10, 3, 3, 0)), ((6847 / 250), gapWord (10, 3, 2, 1)), ((587 / 250), gapWord (10, 2, 4, 0)), ((11961 / 500), gapWord (10, 2, 3, 1)), ((-9 / 4), gapWord (10, 1, 5, 0)), ((3919 / 500), gapWord (10, 1, 4, 1)), ((867 / 500), gapWord (10, 0, 6, 0)), ((-2749 / 500), gapWord (9, 6, 1, 0)), ((-88 / 25), gapWord (9, 5, 2, 0)), ((-309 / 50),
    gapWord (9, 5, 1, 1)), ((3369 / 500), gapWord (9, 4, 3, 0)), ((-493 /
    100), gapWord (9, 4, 2, 1)), ((899 / 100), gapWord (9, 3, 4, 0)),
    ((1067 / 125), gapWord (9, 3, 3, 1)), ((-4599 / 500), gapWord (9, 2, 5, 0)), ((587 / 250), gapWord (9, 2, 4, 1)), ((-933 / 125), gapWord (9, 1, 6, 0)), ((867 / 500), gapWord (9, 1, 5, 1)), ((-4599 / 500), gapWord (9, 0, 7, 0)), ((-4589 / 500), gapWord (8, 7, 1, 0)), ((-333 / 20), gapWord (8, 6, 2, 0)), ((-2749 / 500), gapWord (8, 6, 1, 1)), ((1239 / 500),
    gapWord (8, 5, 3, 0)), ((-88 / 25), gapWord (8, 5, 2, 1)), ((883 /
    25), gapWord (8, 4, 4, 0)), ((3369 / 500), gapWord (8, 4, 3, 1)),
    ((9371 / 500), gapWord (8, 3, 5, 0)), ((899 / 100), gapWord (8, 3, 4, 1)), ((9371 / 500), gapWord (8, 2, 6, 0)), ((-4599 / 500), gapWord (8, 2, 5, 1)), ((14143 / 500), gapWord (8, 1, 7, 0)), ((-4599 / 500), gapWord (8, 1, 6, 1)), ((9371 / 500), gapWord (8, 0, 8, 0)), ((-4589 / 500), gapWord (7, 7, 1, 1)), ((-333 / 20), gapWord (7, 6, 2, 1)), ((1239 / 500),
    gapWord (7, 5, 3, 1)), ((883 / 25), gapWord (7, 4, 4, 1)), ((9371 /
    500), gapWord (7, 3, 5, 1)), ((9371 / 500), gapWord (7, 2, 6, 1)),
    ((9371 / 500), gapWord (7, 1, 7, 1))]

set_option maxHeartbeats 3000000 in
-- Elaborate the rational coefficients for this block.
private def summary23 : Terms :=
  []

section

set_option maxRecDepth 25000
-- Check each block of rational cyclic coefficients independently.
set_option maxHeartbeats 12000000

private theorem check0 :
    coefficientsVanish ((chunk 0 ++ summary1) ++ scaleTerms (-1) summary0) = true := by
  decide +kernel

private theorem check1 :
    coefficientsVanish ((chunk 1 ++ summary2) ++ scaleTerms (-1) summary1) = true := by
  decide +kernel

private theorem check2 :
    coefficientsVanish ((chunk 2 ++ summary3) ++ scaleTerms (-1) summary2) = true := by
  decide +kernel

private theorem check3 :
    coefficientsVanish ((chunk 3 ++ summary4) ++ scaleTerms (-1) summary3) = true := by
  decide +kernel

private theorem check4 :
    coefficientsVanish ((chunk 4 ++ summary5) ++ scaleTerms (-1) summary4) = true := by
  decide +kernel

private theorem check5 :
    coefficientsVanish ((chunk 5 ++ summary6) ++ scaleTerms (-1) summary5) = true := by
  decide +kernel

private theorem check6 :
    coefficientsVanish ((chunk 6 ++ summary7) ++ scaleTerms (-1) summary6) = true := by
  decide +kernel

private theorem check7 :
    coefficientsVanish ((chunk 7 ++ summary8) ++ scaleTerms (-1) summary7) = true := by
  decide +kernel

private theorem check8 :
    coefficientsVanish ((chunk 8 ++ summary9) ++ scaleTerms (-1) summary8) = true := by
  decide +kernel

private theorem check9 :
    coefficientsVanish ((chunk 9 ++ summary10) ++ scaleTerms (-1) summary9) = true := by
  decide +kernel

private theorem check10 :
    coefficientsVanish ((chunk 10 ++ summary11) ++ scaleTerms (-1) summary10) = true := by
  decide +kernel

private theorem check11 :
    coefficientsVanish ((chunk 11 ++ summary12) ++ scaleTerms (-1) summary11) = true := by
  decide +kernel

private theorem check12 :
    coefficientsVanish ((chunk 12 ++ summary13) ++ scaleTerms (-1) summary12) = true := by
  decide +kernel

private theorem check13 :
    coefficientsVanish ((chunk 13 ++ summary14) ++ scaleTerms (-1) summary13) = true := by
  decide +kernel

private theorem check14 :
    coefficientsVanish ((chunk 14 ++ summary15) ++ scaleTerms (-1) summary14) = true := by
  decide +kernel

private theorem check15 :
    coefficientsVanish ((chunk 15 ++ summary16) ++ scaleTerms (-1) summary15) = true := by
  decide +kernel

private theorem check16 :
    coefficientsVanish ((chunk 16 ++ summary17) ++ scaleTerms (-1) summary16) = true := by
  decide +kernel

private theorem check17 :
    coefficientsVanish ((chunk 17 ++ summary18) ++ scaleTerms (-1) summary17) = true := by
  decide +kernel

private theorem check18 :
    coefficientsVanish ((chunk 18 ++ summary19) ++ scaleTerms (-1) summary18) = true := by
  decide +kernel

private theorem check19 :
    coefficientsVanish ((chunk 19 ++ summary20) ++ scaleTerms (-1) summary19) = true := by
  decide +kernel

private theorem check20 :
    coefficientsVanish ((chunk 20 ++ summary21) ++ scaleTerms (-1) summary20) = true := by
  decide +kernel

private theorem check21 :
    coefficientsVanish ((chunk 21 ++ summary22) ++ scaleTerms (-1) summary21) = true := by
  decide +kernel

private theorem check22 :
    coefficientsVanish ((chunk 22 ++ summary23) ++ scaleTerms (-1) summary22) = true := by
  decide +kernel

private theorem lastDrop : allTerms.drop (192 * 23) = [] := by decide +kernel

end

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem summarizePrevious (f : Word → ℝ)
    (hf : ∀ w, f (Algebra84.representative w) = f w)
    (i : ℕ) (prev next : Terms)
    (hnext : weightedSum ℝ f (allTerms.drop (192 * (i + 1))) = weightedSum ℝ f next)
    (checked : coefficientsVanish ((chunk i ++ next) ++ scaleTerms (-1) prev) = true) :
    weightedSum ℝ f (allTerms.drop (192 * i)) = weightedSum ℝ f prev := by
  have h := coefficients_sound f hf _ checked
  simp only [weightedSum_append, weightedSum_scale, Rat.cast_neg, Rat.cast_one] at h
  have hs : chunk i ++ allTerms.drop (192 * (i + 1)) = allTerms.drop (192 * i) := by
    simpa only [chunk, Nat.mul_succ] using List.drop_take_append_drop allTerms (192 * i) 192
  rw [← hs, weightedSum_append, hnext]
  linarith only [h]

private theorem checkedTraceSum (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    weightedSum ℝ (traceWord A B) allTerms = 0 := by
  let f := traceWord A B
  have hrep := traceWord_representative A B hA hB
  have h23 : weightedSum ℝ f (allTerms.drop (192 * 23)) =
      weightedSum ℝ f summary23 := by rw [lastDrop, summary23]
  have h22 := summarizePrevious f hrep 22 summary22 summary23 h23 check22
  have h21 := summarizePrevious f hrep 21 summary21 summary22 h22 check21
  have h20 := summarizePrevious f hrep 20 summary20 summary21 h21 check20
  have h19 := summarizePrevious f hrep 19 summary19 summary20 h20 check19
  have h18 := summarizePrevious f hrep 18 summary18 summary19 h19 check18
  have h17 := summarizePrevious f hrep 17 summary17 summary18 h18 check17
  have h16 := summarizePrevious f hrep 16 summary16 summary17 h17 check16
  have h15 := summarizePrevious f hrep 15 summary15 summary16 h16 check15
  have h14 := summarizePrevious f hrep 14 summary14 summary15 h15 check14
  have h13 := summarizePrevious f hrep 13 summary13 summary14 h14 check13
  have h12 := summarizePrevious f hrep 12 summary12 summary13 h13 check12
  have h11 := summarizePrevious f hrep 11 summary11 summary12 h12 check11
  have h10 := summarizePrevious f hrep 10 summary10 summary11 h11 check10
  have h9 := summarizePrevious f hrep 9 summary9 summary10 h10 check9
  have h8 := summarizePrevious f hrep 8 summary8 summary9 h9 check8
  have h7 := summarizePrevious f hrep 7 summary7 summary8 h8 check7
  have h6 := summarizePrevious f hrep 6 summary6 summary7 h7 check6
  have h5 := summarizePrevious f hrep 5 summary5 summary6 h6 check5
  have h4 := summarizePrevious f hrep 4 summary4 summary5 h5 check4
  have h3 := summarizePrevious f hrep 3 summary3 summary4 h4 check3
  have h2 := summarizePrevious f hrep 2 summary2 summary3 h3 check2
  have h1 := summarizePrevious f hrep 1 summary1 summary2 h2 check1
  have h0 := summarizePrevious f hrep 0 summary0 summary1 h1 check0
  simpa only [summary0, weightedSum, Nat.mul_zero, List.drop_zero] using h0

end
end Algebra164
end RefinedBMV
