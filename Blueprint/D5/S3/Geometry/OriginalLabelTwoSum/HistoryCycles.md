# HistoryCycles

## Abstract

Actual fill0 and path lists construct every wheel cycle by the proved size-bounded attachment.

For EVERY m>=3, pathRootCertificate is extracted from the proved actual pathRowsOutput, then identified with the original all-m indexed path root. The existing Protected.fill0 executes in Delta(Z), fixing E. eta0_card and the actual path profile discharge both size hypotheses of the exact existing boundedAttachment. cycleCertificate supplies the all-residue strong output, including widths 3,4,5. Main order is fill0 then emitted path pairs; the separate C-ALONE order is the ORIGINAL skipped path subsequence followed by the path separate list. The frozen Protected source is under earlier independent review and is not presumed source-approved.

 No full universal history or broad-goal completion is asserted.

**Theorem 1.1 (eta0_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.eta0_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.eta0_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem eta0_card (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2) :

    (eta0 m hm).card = if m % 3 = 0 then 2*(m/3)-1 else 2*(m/3) := by

  have hsub : tailCritical m hm ⊆ tailGround m hm := by

    rw [tail_critical_chosen m hm hr]

    exact (chosen_supported _).trans (by

      intro x hx

      rw [tail_ground_interval, List.mem_toFinset, mem_labelInterval]

      have ht := (cyclePathTail_vertices m hm x).mp hx

      omega)

  have hc : (tailCritical m hm).card = ((m-4)+1)/3 := by

    rw [tail_critical_chosen m hm hr,

      chosen_card _ (cyclePathTail_nodup m hm), cyclePathTail_length]

  rw [eta0, Finset.card_sdiff_of_subset hsub, tail_ground_card m hm, hc]

  split_ifs <;> omega

**Theorem 1.2 (pathRows_pathRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRows_pathRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRows_pathRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem pathRows_pathRoot (m : Nat) (hm : 3 ≤ m) :

    (pathRows (pathRootPath m hm)).root = pathRoot m hm := by

  apply SetLike.ext

  intro s

  rw [pathRows_mem, pathRootPath_vertices, pathRootPath_row_edges]

  constructor

  · rintro ⟨hs, q, hq, hd⟩

    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq

    refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩

    intro x hx

    exact Finset.mem_sdiff.mpr ⟨hs hx, fun hq => Finset.disjoint_left.mp hd hq hx⟩

  · rintro ⟨i, hs⟩

    refine ⟨hs.trans Finset.sdiff_subset, rimEdge m (by omega) i.val,

      Finset.mem_image.mpr ⟨i.val,

        Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩, ?_⟩

    exact Finset.disjoint_left.mpr (fun x hxq hxs => (Finset.mem_sdiff.mp (hs hxs)).2 hxq)

**Definition 1.3 (pathRootCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

def pathRootCertificate (m : Nat) (hm : 3 ≤ m) :

    Certificate (ground m) (pathRoot m hm) :=

  castCertificate (pathRootPath_vertices m hm) (pathRows_pathRoot m hm)

    (pathRowsOutput_critical_profile (pathRootPath m hm) (pathRootPath_nodup m hm)

      (by simpa only [pathRootPath_length] using hm)).choose

**Theorem 1.4 (pathRootCertificate_profile).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem pathRootCertificate_profile (m : Nat) (hm : 3 ≤ m) :

    PathCriticalProfile m (pathRootCertificate m hm).critical := by

  rw [pathRootCertificate, castCertificate_critical]

  simpa only [pathRootPath_length] using

    (pathRowsOutput_critical_profile (pathRootPath m hm) (pathRootPath_nodup m hm)

      (by simpa only [pathRootPath_length] using hm)).choose_spec.2

**Definition 1.5 (attachmentSize).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.attachmentSize`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.attachmentSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

def attachmentSize (m : Nat) : Nat :=

  if m % 3 = 0 then 2*(m/3)-1 else 2*(m/3)

**Definition 1.6 (cycleStrip).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

def cycleStrip (m : Nat) (hm : 3 ≤ m) :

    Sequence (project (A1 m hm))

      (project (endpoint (pathRoot m hm) (fill0 m hm).critical)) := by

  let f := fill0 m hm

  let S := liftFibre (delta (tailGround m hm)) (endpoint (A0 m hm) f.critical)

    (pathRoot m hm) ∅ (tailGround m hm) (Finset.empty_subset _)

    (Or.inl f.empty_mem) f.main (by simp) (fun _ h => h)

    (by intro x hx; exact (Finset.not_ssubset_empty x hx).elim)

    (by intro t ht h; exact Or.inl ⟨by simpa using h, ht⟩)

  have hstart : pathRoot m hm ⊔ rawJoin (delta ∅) (delta (tailGround m hm)) = A1 m hm := by

    rw [(rawJoin_unit _).1]

    rfl

  have hend : pathRoot m hm ⊔ rawJoin (delta ∅) (endpoint (A0 m hm) f.critical) =

      endpoint (pathRoot m hm) f.critical := by

    rw [(rawJoin_unit _).1]

    change pathRoot m hm ⊔ (A0 m hm ⊔ facets f.critical) = pathRoot m hm ⊔ facets f.critical

    rw [← sup_assoc, sup_eq_left.mpr (show A0 m hm ≤ pathRoot m hm from inf_le_left)]

  exact S.cast (congrArg project hstart) (congrArg project hend)

**Theorem 1.7 (cycleStrip_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem cycleStrip_pairs (m : Nat) (hm : 3 ≤ m) :

    (cycleStrip m hm).pairs.map (fun P => (P.lower, P.upper)) =

      (fill0 m hm).main.pairs.map (fun P => (P.lower, P.upper)) := by

  simp only [cycleStrip, Sequence.pairs_cast, liftFibre_pairs, Finset.empty_union]

**Definition 1.8 (cycleCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

def cycleCertificate (m : Nat) (hm : 3 ≤ m) : Certificate (ground m) (A1 m hm) where

  supported := by

    intro s hs

    exact hs.elim

      (fun hs => (((rimRows m (by omega)).without (interfaceRow m hm)).root_supported s hs))

      (fun hs => hs.trans Finset.sdiff_subset)

  core := (afterStrip m hm).core

  critical := (afterStrip m hm).critical

  vertex := (afterStrip m hm).vertex

  vertex_mem := (afterStrip m hm).vertex_mem

  core_supported := (afterStrip m hm).core_supported

  critical_supported := (afterStrip m hm).critical_supported

  cells := (afterStrip m hm).cells

  main := (cycleStrip m hm).append (afterStrip m hm).main

  separate := (afterStrip m hm).separate

**Theorem 1.9 (cycleCertificate_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem cycleCertificate_critical (m : Nat) (hm : 3 ≤ m) :

    (cycleCertificate m hm).critical =

      (pathRootCertificate m hm).critical ∪ (fill0 m hm).critical := rfl

**Theorem 1.10 (cycleCertificate_main_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_main_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_main_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem cycleCertificate_main_pairs (m : Nat) (hm : 3 ≤ m) :

    (cycleCertificate m hm).main.pairs.map (fun P => (P.lower, P.upper)) =

      (fill0 m hm).main.pairs.map (fun P => (P.lower, P.upper)) ++

      (emitted (pathRootCertificate m hm).main.pairs (fill0 m hm).critical).map

        (fun P => (P.lower, P.upper)) := by

  simp only [cycleCertificate, Sequence.pairs_append, List.map_append, cycleStrip_pairs]

  rw [afterStrip, boundedAttachment_main_pairs]

**Theorem 1.11 (cycleCertificate_separate_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_separate_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_separate_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

theorem cycleCertificate_separate_pairs (m : Nat) (hm : 3 ≤ m) :

    (cycleCertificate m hm).separate.pairs.map (fun P => (P.lower, P.upper)) =

      (skipped (pathRootCertificate m hm).main.pairs (fill0 m hm).critical).map

        (fun P => (P.lower, P.upper)) ++

      (pathRootCertificate m hm).separate.pairs.map (fun P => (P.lower, P.upper)) := by

  change (afterStrip m hm).separate.pairs.map _ = _

  rw [afterStrip, boundedAttachment_separate_pairs]

**Definition 1.12 (wheelRowsOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.wheelRowsOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.wheelRowsOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths, D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected. Exact public declaration and proof/source body:

def wheelRowsOutput (m : Nat) (hm : 3 ≤ m) :

    Output (rimRows m (by omega)).ground (rimRows m (by omega)).root :=

  changeOutput (.strong (cycleCertificate m hm)) (wheelRoot_eq_A1 m hm).symm

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.attachmentSize`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_main_pairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleCertificate_separate_pairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.cycleStrip_pairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.eta0_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRootCertificate_profile`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.pathRows_pathRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles.wheelRowsOutput`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected](AllMWheel/Protected.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryAttachment](HistoryAttachment.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths](HistoryPaths.md)
