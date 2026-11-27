/- GID: D5/S3/Topology/ThirteenPointStructuralCategoricalCovers
   generality: I
   mirror-B: D5/B/S3/Topology/ThirteenPointStructuralCategoricalCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Topology/ThirteenPointStructuralCategoricalCovers.cover_of_structural_table; instance=D5/S3/Topology/ThirteenPointStructuralCategoricalCovers.structuralCensus; result=D5/S3/Topology/ThirteenPointStructuralCategoricalCovers.cover_of_structural_table
   digest: Separation of extrema preserves the categorical partitions of the structural order tables. -/

module

public import D5.S3.Topology.FiniteCategoricalCoverCertificate
public import D5.S3.Topology.SubdivisionCategoricalCover
public import Mathlib.Data.Fin.VecNotation
import OmegaBuild.Commands

/-! Categorical partitions of structural thirteen-point orders. -/

compile_only_with_mathlib

public section

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Topology.ThirteenPointStructuralCategoricalCovers

open D5.S3.Topology.ConnectedCategoryGraft
open D5.S3.Topology.FiniteCategoricalCoverCertificate
open D5.S3.Topology.SubdivisionCategoricalCover
open PartialOrder (NonemptyFiniteChains)

/-- Read the lower-neighbor mask of each point as a relation table. -/
@[expose] def orderFromMasks {n : ℕ} (masks : Fin n → ℕ) (x y : Fin n) : Bool :=
  (masks y).testBit x.val

/-- Read the two vertex-membership masks. -/
@[expose] def domainsFromMasks {n : ℕ} (masks : Fin 2 → ℕ) (i : Fin 2) (x : Fin n) : Bool :=
  (masks i).testBit x.val

/-- Each move changes the images of precisely the indicated source vertices. -/
@[expose] def applyMoves {n : ℕ} (f : Fin n → Fin n) :
    List (ℕ × Fin n) → List (Fin n → Fin n)
  | [] => []
  | (mask, new) :: moves =>
    let g := fun x => if mask.testBit x.val then new else f x
    g :: applyMoves g moves

/-- The two checked induced subposets partition the displayed order. -/
structure CertifiedOrder (n : ℕ) where
  le : Fin n → Fin n → Bool
  valid : ValidOrder le
  domains : Fin 2 → Fin n → Bool
  c : Fin 2 → Fin n
  steps : Fin 2 → List (Fin n → Fin n)
  partition : ∀ x, (domains 0 x = true ∨ domains 1 x = true) ∧
    ¬ (domains 0 x = true ∧ domains 1 x = true)
  fence : ∀ i, Contracts le (domains i) (c i) id (steps i)

/-- Assemble one order table from its checked data. -/
def certify {n : ℕ} (masks : Fin n → ℕ) (domains : Fin 2 → ℕ)
    (c : Fin 2 → Fin n) (moves : Fin 2 → List (ℕ × Fin n))
    (hv : ValidOrder (orderFromMasks masks))
    (hpart : ∀ x : Fin n, (domainsFromMasks domains 0 x = true ∨
      domainsFromMasks domains 1 x = true) ∧
      ¬ (domainsFromMasks domains 0 x = true ∧ domainsFromMasks domains 1 x = true))
    (hfence : ∀ i, Contracts (orderFromMasks masks) (domainsFromMasks domains i) (c i) id
      (applyMoves id (moves i))) : CertifiedOrder n :=
  ⟨orderFromMasks masks, hv, domainsFromMasks domains, c,
    fun i => applyMoves id (moves i), hpart, hfence⟩

/-- Each piece is categorical in the order defined by the exact table. -/
theorem CertifiedOrder.categorical {n : ℕ} (w : CertifiedOrder n) (i : Fin 2) :
    letI : PartialOrder (Fin n) := tableOrder w.le w.valid
    Categorical {x | w.domains i x = true} :=
  categorical_of_table w.valid (w.fence i)

/-- A categorical vertex partition gives a categorical lower two-cover of
its second ordinary subdivision. -/
theorem CertifiedOrder.doubleSubdivisionCover {n : ℕ} (w : CertifiedOrder n) :
    letI : PartialOrder (Fin n) := tableOrder w.le w.valid
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains (Fin n))) 2 := by
  let : PartialOrder (Fin n) := tableOrder w.le w.valid
  exact hasCategoricalCover_double_subdivision (w.categorical 0) (w.categorical 1)
    (fun x => (w.partition x).1)

/-- Enlarging the ambient order preserves a fence when the induced order on
its domain is unchanged. -/
private theorem contracts_of_extension {n : ℕ} {le le' : Fin n → Fin n → Bool}
    {U : Fin n → Bool} {c : Fin n} {f : Fin n → Fin n}
    {steps : List (Fin n → Fin n)}
    (hsub : ∀ x y, le x y = true → le' x y = true)
    (hdom : ∀ x y, U x = true → U y = true → le' x y = true → le x y = true)
    (h : Contracts le U c f steps) : Contracts le' U c f steps := by
  induction steps generalizing f with
  | nil => exact h
  | cons g steps ih =>
    obtain ⟨hg, hd, ht⟩ := h
    refine ⟨?_, ?_, ih ht⟩
    · intro x y hx hy hxy
      exact hsub _ _ (hg x y hx hy (hdom x y hx hy hxy))
    · rcases hd with hd | hd
      · exact Or.inl (fun x hx => hsub _ _ (hd x hx))
      · exact Or.inr (fun x hx => hsub _ _ (hd x hx))

/-- The same two induced domains are categorical in an enlarged ambient order. -/
theorem CertifiedOrder.doubleSubdivisionCover_of_extension {n : ℕ} (w : CertifiedOrder n)
    (le' : Fin n → Fin n → Bool) (hv : ValidOrder le')
    (hsub : ∀ x y, w.le x y = true → le' x y = true)
    (hdom : ∀ i x y, w.domains i x = true → w.domains i y = true →
      le' x y = true → w.le x y = true) :
    letI : PartialOrder (Fin n) := tableOrder le' hv
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains (Fin n))) 2 := by
  let : PartialOrder (Fin n) := tableOrder le' hv
  have hcat (i : Fin 2) : Categorical {x | w.domains i x = true} :=
    categorical_of_table hv (contracts_of_extension hsub (hdom i) (w.fence i))
  exact hasCategoricalCover_double_subdivision (hcat 0) (hcat 1) (fun x => (w.partition x).1)

/-- All minimal vertices are in piece zero and all maximal vertices in piece one. -/
@[expose] def SeparatesExtrema (le : Fin 13 → Fin 13 → Bool) (U : Fin 2 → Fin 13 → Bool) : Prop :=
  (∀ x, (∀ y, le y x = true → y = x) → U 0 x = true) ∧
  (∀ x, (∀ y, le x y = true → y = x) → U 1 x = true)

instance (le : Fin 13 → Fin 13 → Bool) (U : Fin 2 → Fin 13 → Bool) :
    Decidable (SeparatesExtrema le U) := by
  unfold SeparatesExtrema
  infer_instance

/-- The structural rows have an additional check on their extrema. -/
structure StructuralOrder where
  table : CertifiedOrder 13
  separates : SeparatesExtrema table.le table.domains

/-- Optional comparisons from old minimal to old maximal vertices may be added
freely, subject to the resulting relation being a partial order. Such a
comparison cannot occur inside either of the two induced domains. -/
theorem StructuralOrder.doubleSubdivisionCover_of_extremal_extension (w : StructuralOrder)
    (le' : Fin 13 → Fin 13 → Bool) (hv : ValidOrder le')
    (hsub : ∀ x y, w.table.le x y = true → le' x y = true)
    (hnew : ∀ x y, le' x y = true → w.table.le x y = true ∨
      ((∀ z, w.table.le z x = true → z = x) ∧
       (∀ z, w.table.le y z = true → z = y))) :
    letI : PartialOrder (Fin 13) := tableOrder le' hv
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains (Fin 13))) 2 := by
  let : PartialOrder (Fin 13) := tableOrder le' hv
  refine w.table.doubleSubdivisionCover_of_extension le' hv hsub ?_
  intro i x y hx hy hxy
  rcases hnew x y hxy with hold | ⟨hmin, hmax⟩
  · exact hold
  · have hi : i = 0 ∨ i = 1 := (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) i
    rcases hi with rfl | rfl
    · exact False.elim ((w.table.partition y).2 ⟨hy, w.separates.2 y hmax⟩)
    · exact False.elim ((w.table.partition x).2 ⟨w.separates.1 x hmin, hx⟩)

private def structural1 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 815, 1455, 2143, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 10), (35, 7), (64, 12), (64, 7), (256, 10), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural2 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 879, 1263, 2399, 4319]
    ![495, 7696] ![6, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 6), (128, 10), (128, 6), (256, 9), (4, 6), (8,
      6), (256, 6)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural3 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 879, 1391, 2271, 4319]
    ![495, 7696] ![6, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 6), (128, 11), (128, 6), (256, 9), (4, 6), (8,
      6), (256, 6)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural4 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1135, 2335, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural5 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1135, 2463, 4191]
    ![431, 7760] ![9, 12]
    ![[(1, 5), (2, 5), (35, 9), (128, 9), (256, 9), (4, 9), (8, 9)],
      [(1024, 6), (1088, 12), (2048, 4), (2064, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural6 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1263, 2463, 4191]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 10), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural7 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1391, 2067, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural8 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1391, 2143, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural9 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1391, 2207, 4191]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 8), (64, 10), (64, 8), (128, 9), (4, 8), (8,
      8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural10 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1391, 2335, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural11 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1391, 2399, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural12 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1455, 2143, 4191]
    ![415, 7776] ![9, 12]
    ![[(1, 4), (2, 4), (19, 0), (19, 9), (128, 9), (256, 9), (4, 9), (8, 9)],
      [(512, 5), (544, 10), (2048, 6), (2112, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural13 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1455, 2143, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural14 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 268, 943, 1455, 2399, 4319]
    ![495, 7696] ![7, 0]
    ![[(1, 5), (2, 5), (35, 9), (35, 7), (64, 12), (64, 7), (256, 9), (4, 7), (8,
      7), (256, 7)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural15 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 687, 1455, 2143, 4447]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 12), (64, 8), (128, 10), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural16 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1135, 2207, 4447]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 12), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural17 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1135, 2463, 4191]
    ![431, 7760] ![8, 12]
    ![[(2, 5), (34, 0), (35, 8), (128, 9), (4, 8), (8, 8), (128, 8)],
      [(1024, 6), (1088, 12), (2048, 4), (2064, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural18 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1391, 2207, 4191]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 10), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural19 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1391, 2463, 4191]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 10), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural20 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1391, 2463, 4447]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 10), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural21 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1455, 2143, 4191]
    ![415, 7776] ![8, 12]
    ![[(2, 4), (18, 0), (19, 8), (128, 9), (4, 8), (8, 8), (128, 8)],
      [(512, 5), (544, 10), (2048, 6), (2112, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural22 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1455, 2143, 4447]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 12), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural23 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 269, 943, 1455, 2399, 4447]
    ![495, 7696] ![8, 0]
    ![[(2, 5), (34, 0), (35, 8), (64, 11), (64, 8), (128, 9), (4, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural24 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 687, 1455, 2143, 4447]
    ![511, 7680] ![8, 0]
    ![[(16, 12), (16, 8), (32, 10), (1, 8), (2, 8), (32, 8), (64, 12), (64, 8),
      (128, 10), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural25 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1135, 2207, 4447]
    ![511, 7680] ![8, 0]
    ![[(16, 12), (16, 8), (32, 9), (1, 8), (2, 8), (32, 8), (64, 12), (64, 8), (128,
      9), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural26 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1391, 2207, 4191]
    ![495, 7696] ![8, 0]
    ![[(32, 9), (1, 8), (2, 8), (32, 8), (64, 10), (64, 8), (128, 9), (4, 8), (8,
      8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural27 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1391, 2463, 4191]
    ![511, 7680] ![8, 0]
    ![[(16, 11), (16, 8), (32, 9), (1, 8), (2, 8), (32, 8), (64, 10), (64, 8), (128,
      9), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural28 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1391, 2463, 4447]
    ![511, 7680] ![8, 0]
    ![[(16, 11), (16, 8), (32, 9), (1, 8), (2, 8), (32, 8), (64, 10), (64, 8), (128,
      9), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural29 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1455, 2143, 4191]
    ![159, 8032] ![7, 0]
    ![[(1, 4), (2, 4), (4, 7), (8, 7), (19, 0), (19, 9), (19, 7)],
      [(2048, 6), (2112, 12), (32, 0), (256, 0), (512, 0), (1024, 0), (6208, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural30 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1455, 2143, 4447]
    ![511, 7680] ![8, 0]
    ![[(16, 12), (16, 8), (32, 9), (1, 8), (2, 8), (32, 8), (64, 12), (64, 8), (128,
      9), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural31 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 35, 76, 140, 271, 943, 1455, 2399, 4447]
    ![511, 7680] ![8, 0]
    ![[(16, 11), (16, 8), (32, 9), (1, 8), (2, 8), (32, 8), (64, 11), (64, 8), (128,
      9), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural32 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 719, 1327, 2399, 4287]
    ![351, 7840] ![8, 12]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(512, 7), (640, 12), (1024, 5), (1056, 12), (2048, 0), (2048, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural33 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 847, 1199, 2399, 4287]
    ![319, 7872] ![8, 12]
    ![[(4, 5), (8, 8), (36, 0), (37, 4), (53, 1), (55, 8)],
      [(512, 6), (576, 11), (1024, 7), (1152, 12), (2624, 0), (2624, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural34 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 847, 1247, 2367, 4287]
    ![351, 7840] ![8, 12]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(1024, 7), (1152, 12), (2048, 5), (2080, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural35 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 847, 1327, 2271, 4287]
    ![351, 7840] ![8, 12]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(1024, 5), (1056, 12), (2048, 7), (2176, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural36 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 847, 1359, 2239, 4287]
    ![351, 7840] ![8, 1]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(32, 0), (32, 4), (32, 1), (128, 1), (512, 1), (1024, 1), (2048, 1), (4096,
      1)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural37 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 847, 1375, 2239, 4287]
    ![351, 7840] ![8, 1]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(32, 0), (32, 4), (32, 1), (128, 1), (512, 1), (1024, 1), (2048, 1), (4096,
      1)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural38 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 863, 1247, 2367, 4287]
    ![351, 7840] ![8, 12]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(1024, 7), (1152, 12), (2048, 5), (2080, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural39 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 69, 138, 266, 863, 1375, 2239, 4287]
    ![351, 7840] ![8, 1]
    ![[(4, 6), (8, 8), (68, 0), (69, 4), (85, 1), (87, 8)],
      [(32, 0), (32, 4), (32, 1), (128, 1), (512, 1), (1024, 1), (2048, 1), (4096,
      1)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural40 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 138, 268, 687, 1263, 2335, 4447]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural41 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 138, 268, 751, 1263, 2335, 4383]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural42 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 138, 268, 751, 1263, 2335, 4447]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural43 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 138, 268, 751, 1263, 2399, 4447]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural44 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 138, 268, 813, 1263, 2203, 4447]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural45 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 140, 268, 877, 1261, 2335, 4255]
    ![511, 7680] ![0, 0]
    ![[(2, 4), (18, 0), (128, 10), (256, 9), (4, 5), (4, 0), (8, 6), (8, 0), (32,
      0), (64, 0), (128, 0), (256, 0)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural46 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 73, 140, 268, 877, 1389, 2207, 4255]
    ![383, 7808] ![9, 0]
    ![[(2, 4), (18, 0), (32, 9), (64, 9), (19, 9), (256, 9), (4, 9), (8, 9)],
      [(2048, 7), (2176, 12), (512, 0), (1024, 0), (6272, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural47 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 623, 1135, 2463, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 11), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural48 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 623, 1263, 2463, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 11), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural49 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 623, 1391, 2207, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 12), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural50 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 751, 1263, 2463, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 11), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural51 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1263, 2067, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 12), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural52 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1263, 2207, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 12), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural53 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1263, 2335, 4255]
    ![367, 7824] ![8, 12]
    ![[(1, 5), (2, 6), (33, 2), (37, 8), (66, 3), (74, 8)],
      [(1024, 7), (1152, 12), (2048, 4), (2064, 12), (512, 0), (512, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural54 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1263, 2463, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 11), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural55 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1391, 2207, 4255]
    ![351, 7840] ![8, 12]
    ![[(1, 4), (4, 8), (17, 1), (19, 6), (83, 3), (91, 8)],
      [(512, 5), (544, 10), (2048, 7), (2176, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural56 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 268, 879, 1391, 2207, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (2, 6), (33, 2), (66, 3), (128, 12), (37, 8), (74, 8), (128, 8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural57 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 270, 623, 1391, 2207, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (33, 2), (64, 10), (2, 8), (64, 8), (128, 12), (37, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural58 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 270, 879, 1391, 2207, 4255]
    ![351, 7840] ![8, 12]
    ![[(1, 4), (4, 8), (17, 1), (64, 9), (19, 8), (8, 8), (64, 8)],
      [(512, 5), (544, 10), (2048, 7), (2176, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural59 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 270, 879, 1391, 2207, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (33, 2), (64, 9), (2, 8), (64, 8), (128, 12), (37, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural60 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 270, 879, 1391, 2463, 4511]
    ![495, 7696] ![8, 0]
    ![[(1, 5), (33, 2), (64, 9), (2, 8), (64, 8), (128, 11), (37, 8), (8, 8), (128,
      8)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural61 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 271, 623, 1391, 2207, 4511]
    ![511, 7680] ![8, 0]
    ![[(16, 12), (16, 8), (32, 10), (1, 8), (32, 8), (64, 10), (2, 8), (64, 8),
      (128, 12), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural62 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 271, 879, 1391, 2207, 4255]
    ![239, 7952] ![7, 12]
    ![[(1, 5), (2, 6), (33, 2), (37, 7), (66, 3), (74, 7)],
      [(512, 8), (768, 10), (2048, 4), (2064, 12), (1792, 0), (1792, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural63 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 271, 879, 1391, 2207, 4511]
    ![511, 7680] ![8, 0]
    ![[(16, 12), (16, 8), (32, 9), (1, 8), (32, 8), (64, 9), (2, 8), (64, 8), (128,
      12), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural64 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 37, 74, 140, 271, 879, 1391, 2463, 4511]
    ![511, 7680] ![8, 0]
    ![[(16, 11), (16, 8), (32, 9), (1, 8), (32, 8), (64, 9), (2, 8), (64, 8), (128,
      11), (4, 8), (8, 8), (128, 8)],
      [(512, 0), (1024, 0), (2048, 0), (4096, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural65 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 73, 138, 268, 751, 1263, 2335, 4383]
    ![463, 7728] ![8, 12]
    ![[(1, 6), (2, 7), (4, 8), (65, 3), (130, 3), (203, 8)],
      [(512, 5), (544, 10), (2048, 4), (2064, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural66 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 73, 140, 268, 879, 1263, 2335, 4255]
    ![495, 7696] ![0, 0]
    ![[(2, 5), (128, 10), (256, 9), (4, 5), (4, 0), (8, 6), (8, 0), (34, 0), (64,
      0), (128, 0), (256, 0)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural67 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 73, 140, 268, 879, 1391, 2207, 4255]
    ![351, 7840] ![8, 12]
    ![[(2, 4), (4, 8), (18, 0), (19, 6), (83, 3), (91, 8)],
      [(512, 5), (544, 10), (2048, 7), (2176, 12), (1568, 0), (1568, 12)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural68 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 73, 140, 270, 879, 1391, 2207, 4255]
    ![287, 7904] ![8, 0]
    ![[(1, 4), (4, 8), (8, 8), (17, 1), (19, 8)],
      [(2048, 7), (2176, 12), (32, 0), (64, 0), (512, 0), (1024, 0), (6272, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural69 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 75, 140, 268, 879, 1263, 2335, 4255]
    ![495, 7696] ![6, 0]
    ![[(32, 9), (1, 6), (2, 6), (128, 10), (256, 9), (4, 5), (4, 0), (4, 6), (8, 6),
      (32, 6), (128, 6), (256, 6)],
      [(2048, 4), (2064, 12), (512, 0), (1024, 0), (6160, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural70 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 8, 19, 39, 75, 140, 268, 879, 1391, 2207, 4255]
    ![287, 7904] ![8, 0]
    ![[(1, 4), (2, 4), (4, 8), (8, 8), (19, 0), (19, 9), (19, 8)],
      [(2048, 7), (2176, 12), (32, 0), (64, 0), (512, 0), (1024, 0), (6272, 0)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural71 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 855, 1335, 2255, 4271]
    ![375, 7816] ![1, 1]
    ![[(32, 10), (64, 9), (1, 4), (1, 1), (4, 8), (4, 1), (16, 1), (32, 1), (64, 1),
      (256, 1)],
      [(8, 1), (128, 1), (512, 1), (1024, 1), (2048, 1), (4096, 1)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

private def structural72 : StructuralOrder :=
  ⟨certify ![1, 2, 4, 11, 19, 37, 69, 134, 262, 855, 1367, 2223, 4271]
    ![343, 7848] ![9, 2]
    ![[(16, 9), (64, 9), (1, 9), (256, 9), (2, 9), (4, 9)],
      [(8, 0), (8, 5), (8, 2), (32, 2), (128, 2), (512, 2), (1024, 2), (2048, 2),
      (4096, 2)]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel), by decide +kernel⟩

def structuralCensus : List StructuralOrder :=
  [structural1, structural2, structural3, structural4, structural5, structural6,
   structural7, structural8, structural9, structural10, structural11, structural12,
   structural13, structural14, structural15, structural16, structural17, structural18,
   structural19, structural20, structural21, structural22, structural23, structural24,
   structural25, structural26, structural27, structural28, structural29, structural30,
   structural31, structural32, structural33, structural34, structural35, structural36,
   structural37, structural38, structural39, structural40, structural41, structural42,
   structural43, structural44, structural45, structural46, structural47, structural48,
   structural49, structural50, structural51, structural52, structural53, structural54,
   structural55, structural56, structural57, structural58, structural59, structural60,
   structural61, structural62, structural63, structural64, structural65, structural66,
   structural67, structural68, structural69, structural70, structural71, structural72]

/-- Adding only old minimum-to-maximum comparisons preserves the two-cover
certified by any one of the structural tables. -/
theorem cover_of_structural_table (le le' : Fin 13 → Fin 13 → Bool)
    (hm : le ∈ structuralCensus.map (fun w => w.table.le)) (hv : ValidOrder le')
    (hsub : ∀ x y, le x y = true → le' x y = true)
    (hnew : ∀ x y, le' x y = true → le x y = true ∨
      ((∀ z, le z x = true → z = x) ∧ (∀ z, le y z = true → z = y))) :
    letI : PartialOrder (Fin 13) := tableOrder le' hv
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains (Fin 13))) 2 := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
  exact w.doubleSubdivisionCover_of_extremal_extension le' hv hsub hnew

end D5.S3.Topology.ThirteenPointStructuralCategoricalCovers
