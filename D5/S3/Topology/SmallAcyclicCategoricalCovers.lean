/- GID: D5/S3/Topology/SmallAcyclicCategoricalCovers
   generality: G
   mirror-B: D5/B/S3/Topology/SmallAcyclicCategoricalCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The small finite-space category census has explicit kernel-checked two-covers. -/

module

public import D5.S3.Topology.FiniteCategoricalCoverCertificate
public import Mathlib.Data.Fin.VecNotation

import OmegaBuild.Commands

/-! Explicit category certificates for the three finite-space census sizes. -/

compile_only_with_mathlib

public section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Topology.SmallAcyclicCategoricalCovers

open D5.S3.Topology.ConnectedCategoryGraft
open D5.S3.Topology.FiniteCategoricalCoverCertificate

/-- A relation table with a category bound for the order it defines. -/
structure CertifiedOrder (n : ℕ) where
  le : Fin n → Fin n → Bool
  valid : ValidOrder le
  cover : @HasCategoricalCover (Fin n) (tableOrder le valid) 2

private def orderFromMasks {n : ℕ} (masks : Fin n → ℕ) (x y : Fin n) : Bool :=
  (masks y).testBit x.val

private def domainsFromMasks {n : ℕ} (masks : Fin 2 → ℕ) (i : Fin 2) (x : Fin n) : Bool :=
  (masks i).testBit x.val

/-- A move replaces one image value throughout the current map.
The certificate checker verifies the resulting map on the piece. -/
private def applyMoves {n : ℕ} (f : Fin n → Fin n) :
    List (Fin n × Fin n) → List (Fin n → Fin n)
  | [] => []
  | (old, new) :: moves =>
    let g := fun x => if f x = old then new else f x
    g :: applyMoves g moves

private def certify {n : ℕ} (masks : Fin n → ℕ) (domains : Fin 2 → ℕ)
    (c : Fin 2 → Fin n) (moves : Fin 2 → List (Fin n × Fin n))
    (hv : ValidOrder (orderFromMasks masks))
    (hlow : ∀ (i : Fin 2) (x y : Fin n), orderFromMasks masks x y = true →
      domainsFromMasks domains i y = true → domainsFromMasks domains i x = true)
    (hcover : ∀ (x : Fin n), ∃ (i : Fin 2), domainsFromMasks domains i x = true)
    (hfence : ∀ i, Contracts (orderFromMasks masks) (domainsFromMasks domains i) (c i) id
      (applyMoves id (moves i))) : CertifiedOrder n :=
  ⟨orderFromMasks masks, hv,
    hasCategoricalCover_of_tables _ hv _ _ (fun i => applyMoves id (moves i)) hlow hcover hfence⟩

private def order9_1 : CertifiedOrder 9 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 183, 319] ![447, 111] ![8, 6]
    ![[(3, 8), (0, 4), (1, 5), (4, 2), (2, 5), (7, 5), (5, 8)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order9_2 : CertifiedOrder 9 :=
  certify ![1, 2, 4, 13, 22, 39, 95, 175, 311] ![447, 95] ![8, 6]
    ![[(3, 7), (0, 5), (4, 8), (1, 5), (2, 5), (7, 5), (5, 8)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (4, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_1 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 8, 19, 45, 78, 191, 351, 639] ![895, 191] ![9, 7]
    ![[(5, 9), (0, 4), (2, 6), (3, 6), (4, 1), (1, 6), (8, 6), (6, 9)],
      [(1, 4), (2, 5), (3, 5), (4, 0), (0, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_2 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 8, 25, 46, 79, 191, 351, 623] ![895, 191] ![9, 7]
    ![[(4, 8), (0, 6), (5, 9), (1, 6), (2, 6), (3, 6), (8, 6), (6, 9)],
      [(0, 4), (1, 5), (2, 5), (4, 3), (3, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_3 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 8, 27, 45, 78, 191, 351, 623] ![895, 191] ![3, 7]
    ![[(4, 8), (1, 6), (5, 9), (2, 6), (3, 6), (6, 3), (8, 4), (4, 7), (0, 5), (5, 3), (7, 3), (9, 3)],
      [(1, 4), (2, 5), (4, 7), (0, 5), (3, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_4 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 175, 343, 639] ![895, 175] ![9, 7]
    ![[(3, 9), (0, 4), (4, 2), (5, 9), (1, 6), (2, 6), (8, 6), (6, 9)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_5 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 175, 351, 631] ![895, 175] ![9, 7]
    ![[(3, 8), (0, 4), (4, 2), (5, 9), (1, 6), (2, 6), (8, 6), (6, 9)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_6 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 11, 21, 38, 95, 175, 311, 575] ![831, 255] ![9, 2]
    ![[(3, 9), (0, 4), (1, 5), (4, 2), (2, 5), (8, 5), (5, 9)],
      [(4, 6), (0, 3), (3, 1), (5, 7), (7, 5), (5, 9), (1, 3), (3, 0), (0, 4), (4, 2), (6, 2), (9, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_7 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 183, 311, 575] ![959, 111] ![9, 6]
    ![[(3, 9), (0, 4), (1, 5), (4, 2), (2, 5), (7, 5), (8, 5), (5, 9)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_8 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 13, 21, 38, 70, 175, 343, 639] ![895, 175] ![9, 7]
    ![[(3, 9), (0, 4), (4, 2), (5, 9), (1, 6), (2, 6), (8, 6), (6, 9)],
      [(0, 3), (1, 5), (3, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_9 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 13, 21, 38, 70, 175, 351, 631] ![895, 175] ![9, 7]
    ![[(3, 8), (0, 4), (4, 2), (5, 9), (1, 6), (2, 6), (8, 6), (6, 9)],
      [(0, 3), (1, 5), (3, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order10_10 : CertifiedOrder 10 :=
  certify ![1, 2, 4, 13, 22, 39, 95, 159, 303, 567] ![831, 223] ![9, 7]
    ![[(3, 8), (0, 5), (4, 9), (1, 5), (2, 5), (8, 5), (5, 9)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (6, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_1 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 16, 35, 93, 158, 383, 703, 1279] ![1791, 383] ![10, 8]
    ![[(6, 10), (0, 5), (2, 7), (3, 7), (4, 7), (5, 1), (1, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (3, 6), (4, 6), (5, 0), (0, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_2 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 16, 49, 94, 159, 383, 703, 1247] ![1791, 383] ![10, 8]
    ![[(5, 9), (0, 7), (6, 10), (1, 7), (2, 7), (3, 7), (4, 7), (9, 7), (7, 10)],
      [(0, 5), (1, 6), (2, 6), (3, 6), (5, 4), (4, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_3 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 16, 51, 92, 159, 383, 703, 1247] ![1791, 383] ![10, 8]
    ![[(5, 9), (0, 7), (1, 7), (6, 10), (2, 7), (3, 7), (4, 7), (9, 7), (7, 10)],
      [(0, 5), (1, 5), (2, 6), (3, 6), (5, 4), (4, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_4 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 16, 51, 93, 158, 383, 703, 1247] ![1791, 383] ![4, 8]
    ![[(5, 9), (1, 7), (6, 10), (2, 7), (3, 7), (4, 7), (7, 4), (9, 5), (5, 8), (0, 6), (6, 4), (8, 4), (10, 4)],
      [(1, 5), (2, 6), (3, 6), (5, 8), (0, 6), (4, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_5 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 37, 74, 140, 462, 703, 1279] ![1791, 462] ![10, 8]
    ![[(6, 10), (1, 4), (3, 7), (4, 0), (0, 5), (5, 2), (2, 7), (9, 7), (7, 10)],
      [(1, 6), (2, 7), (6, 3), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_6 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 37, 74, 140, 479, 751, 1279] ![1791, 479] ![10, 8]
    ![[(4, 10), (0, 5), (1, 6), (5, 2), (2, 7), (6, 3), (3, 7), (9, 7), (7, 10)],
      [(0, 4), (2, 7), (4, 1), (1, 6), (6, 3), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_7 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 41, 76, 142, 462, 639, 1215] ![1791, 462] ![3, 8]
    ![[(6, 9), (7, 10), (1, 4), (3, 5), (4, 0), (0, 5), (5, 3), (9, 6), (6, 8), (2, 7), (7, 3), (8, 3), (10, 3)],
      [(1, 7), (6, 8), (2, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_8 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 42, 76, 141, 366, 671, 1279] ![1791, 366] ![10, 8]
    ![[(5, 10), (1, 4), (4, 0), (0, 7), (6, 10), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_9 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 42, 76, 141, 366, 703, 1247] ![1791, 366] ![10, 8]
    ![[(5, 9), (1, 4), (4, 0), (0, 7), (6, 10), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_10 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 44, 69, 138, 479, 751, 1279] ![1791, 479] ![10, 8]
    ![[(4, 10), (0, 6), (1, 7), (6, 2), (2, 5), (5, 3), (3, 7), (9, 7), (7, 10)],
      [(2, 6), (3, 7), (4, 8), (0, 6), (1, 7), (6, 8), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_11 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 44, 73, 142, 383, 735, 1263] ![1791, 383] ![10, 8]
    ![[(4, 9), (0, 6), (1, 7), (5, 10), (2, 7), (6, 3), (3, 7), (9, 7), (7, 10)],
      [(1, 4), (2, 5), (4, 0), (0, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_12 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 44, 73, 142, 463, 639, 1279] ![1791, 463] ![10, 8]
    ![[(7, 10), (1, 4), (2, 5), (4, 0), (0, 6), (5, 3), (3, 6), (9, 6), (6, 10)],
      [(0, 6), (1, 7), (2, 7), (6, 3), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_13 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 19, 45, 78, 191, 351, 607, 1151] ![1919, 191] ![10, 7]
    ![[(5, 10), (0, 4), (2, 6), (3, 6), (4, 1), (1, 6), (8, 6), (9, 6), (6, 10)],
      [(1, 4), (2, 5), (3, 5), (4, 0), (0, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_14 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 38, 73, 138, 349, 686, 1279] ![1791, 349] ![10, 8]
    ![[(4, 10), (0, 6), (2, 5), (5, 1), (1, 7), (6, 3), (3, 7), (9, 7), (7, 10)],
      [(2, 4), (3, 6), (4, 0), (0, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_15 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 41, 78, 142, 351, 687, 1279] ![1791, 351] ![10, 8]
    ![[(4, 10), (0, 5), (5, 3), (6, 10), (1, 7), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 6), (3, 6), (4, 2), (2, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_16 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 41, 78, 142, 351, 703, 1263] ![1791, 351] ![10, 8]
    ![[(4, 9), (0, 5), (5, 3), (6, 10), (1, 7), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 6), (3, 6), (4, 2), (2, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_17 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 76, 143, 415, 639, 1263] ![1791, 415] ![2, 8]
    ![[(4, 9), (7, 10), (1, 5), (2, 6), (5, 3), (3, 6), (6, 2), (9, 4), (4, 8), (0, 7), (7, 2), (8, 2), (10, 2)],
      [(1, 7), (3, 7), (4, 8), (0, 7), (2, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_18 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 76, 143, 463, 639, 1215] ![1791, 463] ![3, 8]
    ![[(6, 9), (7, 10), (0, 4), (1, 5), (2, 4), (3, 5), (4, 2), (5, 3), (9, 6), (6, 8), (2, 7), (7, 3), (8, 3), (10, 3)],
      [(0, 7), (1, 7), (6, 8), (2, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_19 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 76, 207, 383, 735, 1263] ![1791, 383] ![10, 8]
    ![[(4, 9), (0, 7), (2, 6), (5, 10), (1, 7), (3, 6), (6, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 5), (4, 2), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_20 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 77, 142, 367, 671, 1279] ![1791, 367] ![10, 8]
    ![[(5, 10), (1, 7), (6, 10), (0, 4), (3, 7), (4, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_21 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 77, 142, 367, 703, 1247] ![1791, 367] ![10, 8]
    ![[(5, 9), (1, 7), (6, 10), (0, 4), (3, 7), (4, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_22 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 42, 77, 142, 463, 639, 1215] ![1791, 463] ![3, 8]
    ![[(6, 9), (0, 4), (4, 2), (7, 10), (1, 5), (3, 5), (5, 3), (9, 6), (6, 8), (2, 7), (7, 3), (8, 3), (10, 3)],
      [(0, 6), (1, 7), (6, 8), (2, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_23 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 142, 367, 671, 1279] ![1791, 367] ![10, 8]
    ![[(5, 10), (6, 10), (0, 4), (1, 7), (3, 7), (4, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 6), (2, 5), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_24 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 142, 367, 703, 1247] ![1791, 367] ![10, 8]
    ![[(5, 9), (6, 10), (0, 4), (1, 7), (3, 7), (4, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 6), (2, 5), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_25 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 142, 415, 639, 1263] ![1791, 415] ![10, 8]
    ![[(4, 9), (0, 6), (7, 10), (1, 6), (2, 5), (5, 3), (3, 6), (9, 6), (6, 10)],
      [(0, 4), (1, 7), (3, 7), (4, 2), (2, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_26 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 142, 463, 639, 1215] ![1791, 463] ![3, 8]
    ![[(6, 9), (0, 4), (4, 2), (7, 10), (2, 5), (3, 5), (5, 3), (9, 6), (6, 8), (1, 7), (7, 3), (8, 3), (10, 3)],
      [(0, 6), (2, 7), (6, 8), (1, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_27 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 174, 367, 703, 1279] ![1791, 367] ![10, 8]
    ![[(5, 7), (6, 10), (0, 4), (1, 7), (3, 7), (4, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 6), (2, 5), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_28 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 21, 44, 75, 174, 383, 703, 1263] ![1791, 383] ![2, 8]
    ![[(4, 9), (2, 5), (5, 3), (6, 10), (1, 7), (3, 7), (7, 2), (9, 4), (4, 8), (0, 6), (6, 3), (3, 5), (5, 2), (8, 2), (10, 2)],
      [(1, 6), (4, 8), (0, 6), (2, 5), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_29 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 41, 78, 142, 351, 687, 1279] ![1791, 351] ![10, 8]
    ![[(4, 10), (0, 5), (5, 3), (6, 10), (1, 7), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 6), (2, 6), (4, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_30 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 41, 78, 142, 351, 703, 1263] ![1791, 351] ![10, 8]
    ![[(4, 9), (0, 5), (5, 3), (6, 10), (1, 7), (2, 7), (3, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 6), (2, 6), (4, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_31 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 69, 142, 383, 735, 1263] ![1791, 383] ![10, 8]
    ![[(4, 9), (0, 6), (5, 10), (1, 7), (3, 7), (6, 2), (2, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (4, 8), (0, 6), (3, 5), (5, 8), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_32 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 69, 142, 463, 639, 1279] ![1791, 463] ![10, 8]
    ![[(7, 10), (1, 5), (2, 6), (5, 3), (3, 4), (4, 0), (0, 6), (9, 6), (6, 10)],
      [(0, 6), (1, 7), (3, 7), (6, 2), (2, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_33 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 76, 135, 366, 671, 1279] ![1791, 366] ![10, 8]
    ![[(5, 10), (1, 7), (6, 10), (2, 7), (3, 4), (4, 0), (0, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_34 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 76, 135, 366, 703, 1247] ![1791, 366] ![10, 8]
    ![[(5, 9), (1, 7), (6, 10), (2, 7), (3, 4), (4, 0), (0, 7), (9, 7), (7, 10)],
      [(1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_35 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 76, 135, 383, 735, 1263] ![1791, 383] ![10, 8]
    ![[(4, 9), (0, 7), (5, 10), (1, 7), (3, 6), (6, 2), (2, 7), (9, 7), (7, 10)],
      [(0, 4), (1, 5), (2, 6), (4, 3), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_36 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 76, 135, 463, 639, 1279] ![1791, 463] ![10, 8]
    ![[(7, 10), (0, 4), (1, 5), (2, 6), (4, 3), (5, 3), (3, 6), (9, 6), (6, 10)],
      [(0, 7), (1, 7), (3, 6), (6, 2), (2, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_37 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 76, 143, 415, 639, 1263] ![1791, 415] ![3, 8]
    ![[(4, 9), (7, 10), (1, 5), (2, 6), (5, 3), (3, 6), (6, 3), (9, 4), (4, 8), (0, 7), (7, 3), (8, 3), (10, 3)],
      [(1, 7), (2, 7), (4, 8), (0, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_38 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 77, 142, 367, 671, 1279] ![1791, 367] ![10, 8]
    ![[(5, 10), (1, 7), (6, 10), (0, 4), (2, 7), (4, 3), (3, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_39 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 77, 142, 367, 703, 1247] ![1791, 367] ![10, 8]
    ![[(5, 9), (1, 7), (6, 10), (0, 4), (2, 7), (4, 3), (3, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 5), (2, 6), (5, 3), (3, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_40 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 42, 77, 142, 463, 639, 1215] ![1791, 463] ![3, 8]
    ![[(6, 9), (0, 4), (4, 3), (7, 10), (1, 5), (3, 5), (5, 3), (9, 6), (6, 8), (2, 7), (7, 3), (8, 3), (10, 3)],
      [(0, 6), (1, 7), (6, 8), (2, 7), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_41 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 25, 46, 79, 191, 319, 607, 1135] ![1663, 447] ![10, 8]
    ![[(4, 9), (0, 6), (5, 10), (1, 6), (2, 6), (3, 6), (9, 6), (6, 10)],
      [(0, 4), (1, 5), (2, 5), (4, 3), (3, 5), (7, 5), (5, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_42 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 28, 44, 71, 139, 351, 687, 1279] ![1791, 351] ![10, 8]
    ![[(4, 10), (6, 10), (0, 7), (1, 7), (2, 5), (5, 3), (3, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 6), (3, 4), (4, 2), (2, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_43 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 8, 28, 44, 71, 139, 351, 703, 1263] ![1791, 351] ![10, 8]
    ![[(4, 9), (6, 10), (0, 7), (1, 7), (2, 5), (5, 3), (3, 7), (9, 7), (7, 10)],
      [(0, 6), (1, 6), (3, 4), (4, 2), (2, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_44 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 230, 303, 599, 1119] ![1631, 495] ![10, 8]
    ![[(3, 10), (0, 4), (1, 6), (4, 2), (2, 6), (9, 6), (6, 10)],
      [(0, 3), (3, 1), (6, 7), (1, 5), (2, 5), (7, 5), (5, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_45 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 70, 230, 335, 599, 1087] ![1663, 495] ![2, 8]
    ![[(3, 10), (0, 4), (4, 2), (5, 10), (6, 9), (9, 6), (6, 7), (1, 5), (5, 2), (7, 2), (10, 2)],
      [(0, 3), (3, 1), (5, 7), (1, 6), (2, 6), (7, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_46 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 71, 175, 311, 591, 1143] ![1919, 175] ![10, 7]
    ![[(3, 9), (9, 6), (6, 10), (0, 4), (1, 5), (4, 2), (2, 5), (8, 5), (5, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_47 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 71, 175, 311, 615, 1119] ![1663, 447] ![10, 1]
    ![[(3, 10), (4, 10), (0, 6), (5, 9), (1, 6), (2, 6), (9, 6), (6, 10)],
      [(3, 7), (1, 5), (4, 8), (2, 5), (5, 1), (7, 3), (3, 10), (0, 4), (4, 2), (10, 6), (6, 9), (2, 5), (5, 1), (9, 1), (8, 1)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_48 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 71, 175, 343, 615, 1087] ![1663, 511] ![2, 2]
    ![[(3, 10), (4, 10), (6, 9), (1, 5), (2, 5), (5, 2), (9, 6), (6, 8), (0, 4), (4, 2), (8, 2), (10, 2)],
      [(3, 7), (4, 8), (5, 7), (6, 8), (8, 6), (6, 9), (1, 5), (5, 2), (9, 6), (6, 8), (8, 4), (4, 10), (0, 3), (3, 1), (1, 5), (5, 2), (7, 2), (10, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_49 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 95, 175, 311, 567, 1087] ![1855, 255] ![10, 2]
    ![[(3, 10), (0, 4), (1, 5), (4, 2), (2, 5), (8, 5), (9, 5), (5, 10)],
      [(4, 6), (0, 3), (3, 1), (5, 7), (7, 5), (5, 10), (1, 3), (3, 0), (0, 4), (4, 2), (6, 2), (10, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_50 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 103, 159, 311, 623, 1143] ![1919, 159] ![10, 7]
    ![[(3, 9), (1, 5), (5, 2), (8, 4), (4, 10), (0, 6), (2, 6), (9, 6), (6, 10)],
      [(1, 3), (2, 4), (3, 0), (0, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_51 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 103, 175, 311, 623, 1143] ![1919, 175] ![10, 7]
    ![[(3, 9), (1, 5), (5, 2), (8, 4), (4, 10), (0, 6), (2, 6), (9, 6), (6, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_52 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 175, 311, 567, 1087] ![1855, 239] ![10, 7]
    ![[(3, 10), (0, 4), (1, 5), (4, 2), (2, 5), (8, 5), (9, 5), (5, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (6, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_53 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 183, 311, 567, 1087] ![1983, 111] ![10, 6]
    ![[(3, 10), (0, 4), (1, 5), (4, 2), (2, 5), (7, 5), (8, 5), (9, 5), (5, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_54 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 183, 311, 951, 1471] ![1983, 111] ![10, 6]
    ![[(3, 10), (0, 4), (1, 5), (4, 2), (2, 5), (7, 5), (5, 8), (9, 8), (8, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_55 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 21, 38, 111, 183, 319, 959, 1471] ![1983, 111] ![10, 6]
    ![[(3, 8), (0, 4), (1, 5), (4, 2), (2, 5), (7, 5), (5, 8), (9, 8), (8, 10)],
      [(0, 3), (2, 5), (3, 1), (1, 5), (5, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_56 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 159, 359, 615, 1151] ![1919, 159] ![10, 7]
    ![[(3, 10), (0, 5), (4, 10), (1, 6), (5, 2), (2, 6), (8, 6), (9, 6), (6, 10)],
      [(0, 3), (2, 4), (3, 1), (1, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_57 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 159, 359, 623, 1143] ![1919, 159] ![10, 7]
    ![[(3, 9), (0, 5), (4, 10), (1, 6), (5, 2), (2, 6), (8, 6), (9, 6), (6, 10)],
      [(0, 3), (2, 4), (3, 1), (1, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_58 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 183, 335, 615, 1151] ![1407, 759] ![10, 2]
    ![[(4, 10), (5, 10), (0, 3), (2, 6), (3, 1), (1, 6), (8, 6), (6, 10)],
      [(0, 5), (4, 7), (5, 2), (6, 9), (7, 4), (4, 10), (1, 6), (6, 2), (10, 2), (9, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_59 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 183, 335, 623, 1143] ![1407, 767] ![1, 2]
    ![[(3, 8), (4, 10), (1, 6), (5, 10), (2, 6), (6, 1), (8, 3), (3, 9), (0, 5), (5, 2), (2, 6), (6, 1), (9, 1), (10, 1)],
      [(3, 9), (0, 5), (4, 7), (5, 2), (6, 9), (7, 4), (4, 10), (1, 6), (6, 2), (10, 2), (9, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_60 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 183, 359, 607, 1135] ![1663, 503] ![10, 2]
    ![[(4, 9), (5, 10), (0, 3), (2, 6), (3, 1), (1, 6), (9, 6), (6, 10)],
      [(0, 5), (4, 7), (5, 2), (6, 8), (7, 4), (4, 9), (1, 6), (6, 2), (9, 2), (8, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_61 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 207, 359, 575, 1143] ![1919, 207] ![10, 7]
    ![[(3, 9), (0, 5), (5, 2), (8, 6), (6, 10), (1, 4), (2, 4), (9, 4), (4, 10)],
      [(0, 3), (2, 6), (3, 1), (1, 6), (6, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_62 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 37, 70, 231, 359, 575, 1119] ![1663, 487] ![10, 8]
    ![[(5, 9), (0, 3), (3, 1), (6, 10), (1, 4), (2, 4), (9, 4), (4, 10)],
      [(0, 5), (1, 6), (5, 2), (2, 6), (7, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_63 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 38, 69, 182, 335, 599, 1135] ![1919, 182] ![1, 7]
    ![[(4, 9), (5, 10), (2, 6), (6, 0), (8, 3), (3, 10), (0, 6), (6, 2), (9, 4), (4, 7), (2, 5), (5, 1), (7, 1), (10, 1)],
      [(4, 7), (1, 5), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_64 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 38, 69, 207, 343, 615, 1151] ![1919, 207] ![10, 7]
    ![[(3, 10), (0, 6), (6, 2), (8, 4), (4, 10), (1, 5), (2, 5), (9, 5), (5, 10)],
      [(1, 3), (2, 6), (3, 0), (0, 6), (6, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_65 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 38, 69, 207, 343, 623, 1143] ![1919, 207] ![10, 7]
    ![[(3, 9), (0, 6), (6, 2), (8, 4), (4, 10), (1, 5), (2, 5), (9, 5), (5, 10)],
      [(1, 3), (2, 6), (3, 0), (0, 6), (6, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_66 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 11, 22, 38, 69, 215, 359, 607, 1135] ![1663, 503] ![10, 2]
    ![[(4, 9), (5, 10), (1, 3), (2, 6), (3, 0), (0, 6), (9, 6), (6, 10)],
      [(0, 6), (4, 7), (5, 8), (2, 6), (6, 2), (7, 4), (4, 9), (8, 5), (5, 10), (1, 3), (3, 0), (0, 6), (6, 2), (9, 2), (10, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_67 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 21, 38, 70, 157, 358, 559, 1111] ![1399, 703] ![10, 9]
    ![[(0, 4), (4, 2), (5, 8), (1, 6), (2, 6), (8, 6), (6, 10)],
      [(1, 5), (4, 7), (0, 3), (3, 2), (5, 2), (7, 2), (2, 9)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_68 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 21, 38, 70, 230, 303, 599, 1119] ![1631, 495] ![10, 8]
    ![[(1, 6), (3, 10), (0, 4), (4, 2), (2, 6), (9, 6), (6, 10)],
      [(0, 3), (3, 2), (6, 7), (1, 5), (2, 5), (7, 5), (5, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_69 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 21, 38, 70, 230, 335, 599, 1087] ![1663, 495] ![2, 8]
    ![[(3, 10), (0, 4), (4, 2), (5, 10), (6, 9), (9, 6), (6, 7), (1, 5), (5, 2), (7, 2), (10, 2)],
      [(0, 3), (3, 2), (5, 7), (1, 6), (2, 6), (7, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_70 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 159, 359, 615, 1151] ![1919, 159] ![10, 7]
    ![[(3, 10), (0, 5), (4, 10), (1, 6), (5, 2), (2, 6), (8, 6), (9, 6), (6, 10)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_71 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 159, 359, 623, 1143] ![1919, 159] ![10, 7]
    ![[(3, 9), (0, 5), (4, 10), (1, 6), (5, 2), (2, 6), (8, 6), (9, 6), (6, 10)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_72 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 183, 335, 615, 1151] ![1919, 183] ![10, 7]
    ![[(4, 10), (1, 6), (6, 2), (8, 3), (3, 10), (0, 5), (2, 5), (9, 5), (5, 10)],
      [(0, 5), (1, 4), (4, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_73 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 183, 335, 623, 1143] ![1919, 183] ![10, 7]
    ![[(4, 10), (1, 6), (6, 2), (8, 3), (3, 9), (0, 5), (2, 5), (9, 5), (5, 10)],
      [(0, 5), (1, 4), (4, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_74 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 183, 359, 607, 1135] ![1919, 183] ![10, 7]
    ![[(4, 9), (1, 6), (6, 2), (8, 5), (5, 10), (0, 3), (2, 3), (9, 3), (3, 10)],
      [(0, 5), (1, 4), (4, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_75 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 37, 70, 231, 359, 575, 1119] ![1663, 487] ![10, 8]
    ![[(5, 9), (0, 3), (3, 2), (6, 10), (1, 4), (2, 4), (9, 4), (4, 10)],
      [(0, 5), (1, 6), (5, 2), (2, 6), (7, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_76 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 38, 71, 182, 287, 591, 1127] ![1919, 182] ![2, 7]
    ![[(4, 8), (5, 10), (10, 6), (6, 9), (0, 3), (2, 3), (3, 2), (8, 4), (4, 7), (7, 5), (5, 10), (1, 6), (6, 2), (10, 2), (9, 2)],
      [(4, 7), (1, 5), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_77 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 38, 87, 182, 303, 759, 1279] ![1791, 303] ![10, 8]
    ![[(3, 10), (0, 6), (5, 7), (1, 4), (2, 4), (6, 4), (4, 7), (9, 7), (7, 10)],
      [(0, 3), (1, 5), (3, 2), (2, 5), (5, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_78 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 38, 118, 183, 383, 703, 1271] ![1791, 383] ![10, 8]
    ![[(3, 9), (0, 7), (6, 10), (4, 7), (1, 5), (2, 5), (5, 7), (9, 7), (7, 10)],
      [(0, 3), (3, 2), (4, 6), (1, 5), (2, 5), (5, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_79 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 39, 71, 159, 303, 599, 1127] ![1919, 159] ![10, 7]
    ![[(3, 8), (4, 9), (8, 5), (5, 10), (0, 6), (1, 6), (2, 6), (9, 6), (6, 10)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_80 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 39, 71, 175, 311, 591, 1111] ![1919, 175] ![2, 7]
    ![[(3, 9), (5, 8), (9, 6), (6, 10), (1, 4), (2, 4), (4, 2), (8, 5), (5, 7), (7, 3), (3, 9), (0, 6), (6, 2), (9, 2), (10, 2)],
      [(1, 5), (3, 7), (0, 5), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_81 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 39, 95, 159, 287, 559, 1079] ![1599, 479] ![10, 8]
    ![[(3, 9), (0, 5), (4, 10), (1, 5), (2, 5), (9, 5), (5, 10)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (6, 4), (7, 4), (4, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_82 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 13, 22, 39, 95, 175, 311, 959, 1471] ![1983, 95] ![10, 6]
    ![[(3, 7), (0, 5), (4, 8), (1, 5), (2, 5), (7, 5), (5, 8), (9, 8), (8, 10)],
      [(0, 3), (1, 4), (3, 2), (2, 4), (4, 6)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_83 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 21, 38, 103, 159, 311, 623, 1143] ![1919, 159] ![10, 7]
    ![[(3, 9), (1, 5), (5, 2), (8, 4), (4, 10), (0, 6), (2, 6), (9, 6), (6, 10)],
      [(0, 4), (1, 3), (3, 2), (2, 4), (4, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_84 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 35, 69, 175, 343, 615, 1151] ![1407, 751] ![10, 2]
    ![[(3, 10), (5, 10), (0, 6), (1, 4), (4, 2), (2, 6), (8, 6), (6, 10)],
      [(3, 7), (1, 5), (5, 0), (6, 9), (9, 6), (6, 10), (0, 5), (5, 1), (1, 3), (3, 2), (7, 2), (10, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_85 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 35, 69, 175, 343, 623, 1143] ![1399, 751] ![10, 9]
    ![[(5, 10), (0, 6), (1, 4), (4, 2), (2, 6), (8, 6), (6, 10)],
      [(6, 9), (0, 5), (2, 3), (3, 1), (1, 5), (7, 5), (5, 9)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_86 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 35, 69, 175, 359, 607, 1143] ![1663, 495] ![10, 2]
    ![[(3, 9), (5, 10), (0, 6), (1, 4), (4, 2), (2, 6), (9, 6), (6, 10)],
      [(3, 7), (1, 5), (5, 0), (6, 8), (8, 6), (6, 10), (0, 5), (5, 1), (7, 3), (3, 9), (1, 4), (4, 2), (9, 2), (10, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_87 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 37, 71, 175, 311, 591, 1143] ![1919, 175] ![10, 7]
    ![[(3, 9), (9, 6), (6, 10), (0, 5), (1, 4), (4, 2), (2, 5), (8, 5), (5, 10)],
      [(0, 5), (1, 3), (3, 2), (2, 5), (5, 7)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_88 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 37, 71, 175, 311, 615, 1119] ![1663, 447] ![10, 2]
    ![[(3, 10), (4, 10), (1, 6), (5, 9), (0, 6), (2, 6), (9, 6), (6, 10)],
      [(0, 5), (3, 7), (4, 8), (2, 5), (5, 2), (7, 3), (3, 10), (1, 4), (4, 2), (10, 2), (8, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_89 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 37, 71, 175, 343, 615, 1087] ![1663, 511] ![2, 2]
    ![[(3, 10), (4, 10), (6, 9), (0, 5), (2, 5), (5, 2), (9, 6), (6, 8), (1, 4), (4, 2), (8, 2), (10, 2)],
      [(3, 7), (4, 8), (5, 7), (6, 8), (8, 6), (6, 9), (0, 5), (5, 2), (7, 3), (3, 10), (10, 4), (4, 8), (1, 6), (6, 2), (8, 2), (9, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_90 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 47, 87, 158, 447, 735, 1279] ![1791, 447] ![10, 8]
    ![[(5, 10), (0, 6), (3, 7), (1, 4), (2, 4), (6, 4), (4, 7), (9, 7), (7, 10)],
      [(0, 5), (4, 7), (1, 3), (2, 3), (5, 3), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_91 : CertifiedOrder 11 :=
  certify ![1, 2, 4, 14, 22, 55, 94, 159, 383, 703, 1247] ![1791, 383] ![10, 8]
    ![[(5, 9), (0, 7), (6, 10), (3, 7), (1, 4), (2, 4), (4, 7), (9, 7), (7, 10)],
      [(0, 5), (3, 6), (1, 4), (2, 4), (5, 4), (4, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_92 : CertifiedOrder 11 :=
  certify ![1, 2, 7, 11, 19, 47, 87, 155, 447, 735, 1279] ![1791, 447] ![10, 8]
    ![[(5, 10), (2, 6), (3, 7), (0, 4), (1, 4), (6, 4), (4, 7), (9, 7), (7, 10)],
      [(2, 5), (4, 7), (0, 3), (1, 3), (5, 3), (3, 7), (7, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def order11_93 : CertifiedOrder 11 :=
  certify ![1, 2, 7, 11, 19, 55, 91, 159, 383, 703, 1247] ![1791, 383] ![10, 8]
    ![[(5, 9), (2, 7), (6, 10), (3, 7), (0, 4), (1, 4), (4, 7), (9, 7), (7, 10)],
      [(2, 5), (3, 6), (0, 4), (1, 4), (5, 4), (4, 6), (6, 8)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- All 2 relation tables at size 9, each carrying its verified two-cover. -/
def census9 : List (CertifiedOrder 9) :=
  [order9_1, order9_2]

/-- All 10 relation tables at size 10, each carrying its verified two-cover. -/
def census10 : List (CertifiedOrder 10) :=
  [order10_1, order10_2, order10_3, order10_4, order10_5,
   order10_6, order10_7, order10_8, order10_9, order10_10]

/-- All 93 relation tables at size 11, each carrying its verified two-cover. -/
def census11 : List (CertifiedOrder 11) :=
  [order11_1, order11_2, order11_3, order11_4, order11_5,
   order11_6, order11_7, order11_8, order11_9, order11_10,
   order11_11, order11_12, order11_13, order11_14, order11_15,
   order11_16, order11_17, order11_18, order11_19, order11_20,
   order11_21, order11_22, order11_23, order11_24, order11_25,
   order11_26, order11_27, order11_28, order11_29, order11_30,
   order11_31, order11_32, order11_33, order11_34, order11_35,
   order11_36, order11_37, order11_38, order11_39, order11_40,
   order11_41, order11_42, order11_43, order11_44, order11_45,
   order11_46, order11_47, order11_48, order11_49, order11_50,
   order11_51, order11_52, order11_53, order11_54, order11_55,
   order11_56, order11_57, order11_58, order11_59, order11_60,
   order11_61, order11_62, order11_63, order11_64, order11_65,
   order11_66, order11_67, order11_68, order11_69, order11_70,
   order11_71, order11_72, order11_73, order11_74, order11_75,
   order11_76, order11_77, order11_78, order11_79, order11_80,
   order11_81, order11_82, order11_83, order11_84, order11_85,
   order11_86, order11_87, order11_88, order11_89, order11_90,
   order11_91, order11_92, order11_93]

/-- The enumerated normal forms at each size. -/
def census : (n : ℕ) → List (CertifiedOrder n)
  | 9 => census9
  | 10 => census10
  | 11 => census11
  | _ => []

/-- The order represented by any enumerated normal form has a categorical
two-cover certified by its explicit contraction maps. -/
theorem categorical_cover_of_census_table {n : ℕ} (le : Fin n → Fin n → Bool)
    (hm : le ∈ (census n).map CertifiedOrder.le) :
    ∃ hv : ValidOrder le, @HasCategoricalCover (Fin n) (tableOrder le hv) 2 := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
  exact ⟨w.valid, w.cover⟩

end D5.S3.Topology.SmallAcyclicCategoricalCovers
