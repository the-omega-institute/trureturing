# PhysicalCertificate

## Abstract

Actual retained-edge W4 gluing consumes the native compiler on its derived raw graph root.

**Definition 1.1 (attachment).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.attachment

Exact lexical source telescope:

def attachment {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) : PhysicalGlue VL Wheel.Label V

Actual source body:

:=

  Wheel.ambientGlue left X e a b (Finset.insert_erase he).symm hedge f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: Wheel.ambientGlue; Finset.insert_erase; erase_subset

Real consumers: attachment_ground/root/rows/chords and certificate; atRetainedEdge

Proof-content trace: Uses G1 unchanged. he is only current retained membership; endpoint equality orients that actual edge. Four active labels are fresh relative to current ground. No finite VL.

**Theorem 1.2 (attachment_ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.attachment_ground

Exact lexical source telescope:

theorem attachment_ground {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) : (attachment left e he a b hedge f hf0 hFresh).data.ground = (left.ground.erase e) ∪ (Wheel.Y.image f)

Actual source body:

:= rfl

Dependencies: PhysicalGlue.data.ground definition

Real consumers: certificate_survives and atRetainedEdge_consumed

Proof-content trace: rfl identifies the constructed graph ground with erase-selected union four actual spokes.

**Theorem 1.3 (attachment_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.attachment_root

Exact lexical source telescope:

theorem attachment_root {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) : (attachment left e he a b hedge f hf0 hFresh).data.rows.root =

    parentOf (left.ground.erase e) (Wheel.Y.image f) (Wheel.Z.image f) e (renameFamily f Wheel.E) left.rows.root

Actual source body:

:= by

  exact Wheel.ambient_actual_root left X e a b (Finset.insert_erase he).symm

    hedge f hf0 (Finset.notMem_erase _ _)

    (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: Wheel.ambient_actual_root; PhysicalGlue.root_formula; actual unique paths; Wheel.ambient_E_edge

Real consumers: certificate.supported and certificate.main source cast

Proof-content trace: Derives exact RAW root = native parentOf before project. Unrestricted physical-fiber deletion is authoritative. W4 local U* only permits literal-index corollary.

**Theorem 1.4 (attachment_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.attachment_rows

Exact lexical source telescope:

theorem attachment_rows {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) :

    (∀ c : left.chords, (attachment left e he a b hedge f hf0 hFresh).data.rows.row (.inl c) =

      substitute e (Wheel.R.image f) (left.rows.row c)) ∧

    (∀ d : (Wheel.ambientGraph f).PhysicalSurvivor (0 : Fin 4),

      (attachment left e he a b hedge f hf0 hFresh).data.rows.row (.inr d) = (Wheel.ambientGraph f).rows.row d.1)

Actual source body:

:= by

  constructor

  · intro c

    have hr : (Wheel.ambientGraph f).rows.row (0 : Fin 4) = Wheel.R.image f :=

      (Wheel.ambient_row f 0).trans

        (congrArg (fun t : Finset Wheel.Label => t.image f) (Wheel.fundamental_rows 0))

    exact ((g).left_row c).trans (congrArg

      (fun t => substitute e t (left.rows.row c)) hr)

  · intro d

    exact (g).right_row d

Dependencies: PhysicalGlue.left_row/right_row; Wheel.ambient_row; Wheel.fundamental_rows

Real consumers: later G3 actual indexed path-row recursion (not implemented here)

Proof-content trace: Every original left index and physical right survivor is consumed; actual paths prove conditional substitution, not a row premise.

**Definition 1.5 (attachment_chords).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_chords`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_chords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.attachment_chords

Exact lexical source telescope:

def attachment_chords {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) : (attachment left e he a b hedge f hf0 hFresh).data.chords ≃

    left.chords ⊕ {d : Fin 4 // d ≠ 0}

Actual source body:

:=

  (g).uniqueChordEquiv (Wheel.ambient_uniqueInterface f)

Dependencies: PhysicalGlue.uniqueChordEquiv; Wheel.ambient_uniqueInterface

Real consumers: later G3 original right-index transport (not implemented here)

Proof-content trace: Local W4 U* gives identity on original survivor indices; no global injectivity is imposed.

**Definition 1.6 (certificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate

Exact lexical source telescope:

def certificate {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) :

    Certificate (attachment left e he a b hedge f hf0 hFresh).data.ground (attachment left e he a b hedge f hf0 hFresh).data.rows.root

Actual source body:

where

  supported := by

    rw [attachment_root left e he a b hedge f hf0 hFresh]

    exact (native left e he f hf0 hFresh c).supported

  core := (native left e he f hf0 hFresh c).core

  critical := (native left e he f hf0 hFresh c).critical

  vertex := (native left e he f hf0 hFresh c).vertex

  vertex_mem := (native left e he f hf0 hFresh c).vertex_mem

  core_supported := (native left e he f hf0 hFresh c).core_supported

  critical_supported := (native left e he f hf0 hFresh c).critical_supported

  cells := (native left e he f hf0 hFresh c).cells

  main := (native left e he f hf0 hFresh c).main.cast

    (congrArg project (attachment_root left e he a b hedge f hf0 hFresh)).symm rfl

  separate := (native left e he f hf0 hFresh c).separate

Dependencies: private child and native; WheelSupplier.oneStep; attachment_root; Sequence.cast

Real consumers: every certificate_* endpoint; atRetainedEdge

Proof-content trace: Runs native compiler on actual left row-root certificate. Transports the CONSTRUCTED main across derived raw root equality. Cout/separate/critical/vertex are exactly the constructed native fields.

**Theorem 1.7 (certificate_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_critical

Exact lexical source telescope:

theorem certificate_critical {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : (certificate left e he a b hedge f hf0 hFresh c).critical =

    c.critical.image (wheelCell e (f 1) (f 3) (f 4))

Actual source body:

:=

  WheelSupplier.oneStep_critical (child left e he c) f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: WheelSupplier.oneStep_critical; private child fields

Real consumers: certificate_cells; atRetainedEdge_consumed

Proof-content trace: Exact two-branch wheelCell image on original labels; uses native computed critical data.

**Theorem 1.8 (certificate_statistics).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_statistics`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_statistics

Exact lexical source telescope:

theorem certificate_statistics {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : (certificate left e he a b hedge f hf0 hFresh c).critical.card = c.critical.card ∧

    ∀ q ∈ c.critical, (wheelCell e (f 1) (f 3) (f 4) q).card = q.card + 2

Actual source body:

:=

  WheelSupplier.oneStep_statistics (child left e he c) f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: WheelSupplier.oneStep_statistics; wheelCell_count/recovery/card

Real consumers: later G3 count and size induction (open)

Proof-content trace: Injection follows original-ground recovery, not a cardinality premise. Each face gains two labels in both branches.

**Theorem 1.9 (certificate_cells).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_cells`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_cells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_cells

Exact lexical source telescope:

theorem certificate_cells {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : CriticalData (certificate left e he a b hedge f hf0 hFresh c).core

    (c.critical.image (wheelCell e (f 1) (f 3) (f 4)))

Actual source body:

:= by

  rw [← certificate_critical left e he a b hedge f hf0 hFresh c]

  exact (out).cells

Dependencies: certificate_critical; constructed Certificate.cells

Real consumers: certificate_boundary; downstream cell attachments

Proof-content trace: CriticalData provides nonempty, absent, every proper subface and antichain on computed Cout.

**Theorem 1.10 (certificate_boundary).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_boundary

Exact lexical source telescope:

theorem certificate_boundary {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) {s : Finset V} (hs : s ∈ (certificate left e he a b hedge f hf0 hFresh c).critical) :

    delta s ⊓ (certificate left e he a b hedge f hf0 hFresh c).core =

      (⟨{t | t ⊂ s}, by intro u t hut hts

                         exact lt_of_le_of_lt hut hts⟩ : Family V)

Actual source body:

:=

  critical_intersection (out).core (out).critical (out).cells hs

Dependencies: critical_intersection; constructed cells

Real consumers: literal critical-cell attachment consumers

Proof-content trace: Exact full raw boundary, including empty face, not a sphere or null attaching-map assumption.

**Theorem 1.11 (certificate_vertex).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_vertex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_vertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_vertex

Exact lexical source telescope:

theorem certificate_vertex {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : (certificate left e he a b hedge f hf0 hFresh c).vertex =

    finishVertex (left.ground.erase e) (Wheel.R.image f) e c.vertex

      (Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty))

Actual source body:

:=

  WheelSupplier.oneStep_vertex (child left e he c) f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: WheelSupplier.oneStep_vertex; finishVertex

Real consumers: certificate_at_core/away_from_core

Proof-content trace: The actual compiler choice is preserved; no identification with a preferred label is invented.

**Theorem 1.12 (certificate_survives).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_survives`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_survives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_survives

Exact lexical source telescope:

theorem certificate_survives {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : (certificate left e he a b hedge f hf0 hFresh c).vertex ∈ (attachment left e he a b hedge f hf0 hFresh).data.ground ∧ (certificate left e he a b hedge f hf0 hFresh c).vertex ≠ e

Actual source body:

:= by

  have hv : (out).vertex ∈ X ∪ Yf := (out).core_supported _ (out).vertex_mem (by simp)

  refine ⟨hv,?_⟩

  intro hvE

  rw [hvE] at hv

  rcases Finset.mem_union.mp hv with hx | hy

  · exact Finset.notMem_erase e left.ground hx

  · exact (Wheel.zero_outside_ground f) (hf0.symm ▸ hy)

Dependencies: computed core_supported and vertex_mem; erase exclusion; Wheel.zero_outside_ground

Real consumers: atRetainedEdge_consumed; later G3 next retained edge

Proof-content trace: Proves actual new endpoint lies in current parent tree ground and is different from removed e.

**Theorem 1.13 (certificate_at_core).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_at_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_at_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_at_core

Exact lexical source telescope:

theorem certificate_at_core {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) (hp : c.vertex = e) :

    (∀ hX : (left.ground.erase e).Nonempty, (certificate left e he a b hedge f hf0 hFresh c).vertex ∈ (left.ground.erase e)) ∧

    (¬ (left.ground.erase e).Nonempty → (certificate left e he a b hedge f hf0 hFresh c).vertex ∈ (Wheel.R.image f))

Actual source body:

:= by

  rw [certificate_vertex left e he a b hedge f hf0 hFresh c]

  constructor

  · intro hX

    simp only [finishVertex,if_pos hp,dif_pos hX]

    exact hX.choose_spec

  · intro hX

    simp only [finishVertex,if_pos hp,dif_neg hX]

    exact (show (Rf).Nonempty from

      Finset.image_nonempty.mpr (by decide : Wheel.R.Nonempty)).choose_spec

Dependencies: certificate_vertex; finishVertex cases; Finset.choose_spec

Real consumers: later G3 e=current endpoint branch

Proof-content trace: Nonempty X selects an actual X label; empty X selects an actual R spoke. Deleted e never survives.

**Theorem 1.14 (certificate_away_from_core).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_away_from_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_away_from_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_away_from_core

Exact lexical source telescope:

theorem certificate_away_from_core {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) (hp : c.vertex ≠ e) : (certificate left e he a b hedge f hf0 hFresh c).vertex = c.vertex

Actual source body:

:= by

  rw [certificate_vertex left e he a b hedge f hf0 hFresh c]

  simp only [finishVertex,if_neg hp]

Dependencies: certificate_vertex; finishVertex

Real consumers: later G3 branch away from selected endpoint

Proof-content trace: Preserves previous actual endpoint when it differs from selected e.

**Theorem 1.15 (certificate_main_order).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_main_order

Exact lexical source telescope:

theorem certificate_main_order {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : orderedPairs (certificate left e he a b hedge f hf0 hFresh c).main =

    WheelSupplier.oneStepMainFrom e f c.critical (orderedPairs c.main)

Actual source body:

:= by

  change orderedPairs ((native left e he f hf0 hFresh c).main.cast

    (congrArg project (attachment_root left e he a b hedge f hf0 hFresh)).symm rfl) = _

  rw [orderedPairs_cast]

  exact WheelSupplier.oneStep_main_orderedPairs (child left e he c) f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: orderedPairs_cast; WheelSupplier.oneStep_main_orderedPairs; oneStepMainFrom

Real consumers: atRetainedEdge_consumed; actual main native retraction

Proof-content trace: Exact lower/upper order: child-main flatMap replay, then critical filling flatMap. Gamma remains the compiler Classical.choice, not assumed equal to witness.

**Theorem 1.16 (certificate_separate_order).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_separate_order

Exact lexical source telescope:

theorem certificate_separate_order {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) : orderedPairs (certificate left e he a b hedge f hf0 hFresh c).separate =

    WheelSupplier.oneStepSeparateFrom (left.ground.erase e) e f c.critical c.vertex

      (orderedPairs c.separate)

Actual source body:

:=

  WheelSupplier.oneStep_separate_orderedPairs (child left e he c) f hf0

    (Finset.notMem_erase _ _) (hFresh.mono_left (Finset.erase_subset _ _))

Dependencies: WheelSupplier.oneStep_separate_orderedPairs; oneStepSeparateFrom; finishFacePairs

Real consumers: atRetainedEdge_consumed; actual Cout-alone native retraction

Proof-content trace: Collar blocks then child-core replay then FULL terminal. For p=e/nonempty X enumerate (X union Y).erase newApex; p!=e uses Delta(p)*Delta(Z) union Delta(X)*E. X-empty uses Delta(Y).

**Theorem 1.17 (certificate_current_cofaces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_current_cofaces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_current_cofaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_current_cofaces

Exact lexical source telescope:

theorem certificate_current_cofaces {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) :

    (∀ P ∈ (certificate left e he a b hedge f hf0 hFresh c).main.pairs, P.lower.Nonempty ∧

      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧

    (∀ P ∈ (certificate left e he a b hedge f hf0 hFresh c).separate.pairs, P.lower.Nonempty ∧

      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper)

Actual source body:

:= by

  have hc (P : CollapsePair V) : P.lower.Nonempty ∧

      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper := by

    refine ⟨P.lower_nonempty,?_⟩

    intro s hs hls

    by_cases h : s = P.lower

    · exact Or.inl h

    · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hls,Ne.symm h⟩))

  exact ⟨fun P _ => hc P,fun P _ => hc P⟩

Dependencies: constructed CollapsePair.lower_nonempty/free; proper-subset split

Real consumers: actual emitted-pair consumer for both lists

Proof-content trace: Obtains current cofaces from the actual native pairs. No all-pair-freeness premise or second pair type.

**Theorem 1.18 (certificate_retained_endpoints).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retained_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retained_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_retained_endpoints

Exact lexical source telescope:

theorem certificate_retained_endpoints {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) :

    (∀ P ∈ (certificate left e he a b hedge f hf0 hFresh c).main.pairs, project (endpoint (certificate left e he a b hedge f hf0 hFresh c).core (certificate left e he a b hedge f hf0 hFresh c).critical) ≤ P.retained) ∧

    (∀ P ∈ (certificate left e he a b hedge f hf0 hFresh c).separate.pairs, project (delta {(certificate left e he a b hedge f hf0 hFresh c).vertex}) ≤ P.retained)

Actual source body:

:=

  ⟨fun _ h => (out).main.final_le_each_retained h,

   fun _ h => (out).separate.final_le_each_retained h⟩

Dependencies: Sequence.final_le_each_retained for actual constructed sequences

Real consumers: actual endpoint fixedness at each native pair

Proof-content trace: Both exact lists retain their actual endpoint in every current pair; separate domain is Cout alone.

**Theorem 1.19 (certificate_main_fixed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_main_fixed

Exact lexical source telescope:

theorem certificate_main_fixed {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) (t : unitInterval)

    (x : Space (project (attachment left e he a b hedge f hf0 hFresh).data.rows.root))

    (hx : x.val ∈ realization (project (endpoint (certificate left e he a b hedge f hf0 hFresh c).core (certificate left e he a b hedge f hf0 hFresh c).critical))) (v : V) :

    ((certificate left e he a b hedge f hf0 hFresh c).main.collapseHomotopy (t,x)).val v = x.val v

Actual source body:

:=

  compiler_main_fixed out t x hx v

Dependencies: compiler_main_fixed; native Sequence.collapseHomotopy_fixed

Real consumers: original-coordinate fixed-set consumer

Proof-content trace: Entire actual main endpoint fixed in EVERY original coordinate, including ghosts.

**Theorem 1.20 (certificate_separate_fixed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_separate_fixed

Exact lexical source telescope:

theorem certificate_separate_fixed {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root) (t : unitInterval)

    (x : Space (project (certificate left e he a b hedge f hf0 hFresh c).core))

    (hx : x.val ∈ realization (project (delta {(certificate left e he a b hedge f hf0 hFresh c).vertex}))) (v : V) :

    ((certificate left e he a b hedge f hf0 hFresh c).separate.collapseHomotopy (t,x)).val v = x.val v

Actual source body:

:= by

  exact congrArg (fun z : Space (project (out).core) => z.val v)

    ((out).separate.collapseHomotopy_fixed t x hx)

Dependencies: native Sequence.collapseHomotopy_fixed; congrArg coordinate projection

Real consumers: original-coordinate separate fixed-set consumer

Proof-content trace: Domain is Cout alone; no assertion of collar action on main critical cells.

**Theorem 1.21 (certificate_retractions).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retractions`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retractions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.certificate_retractions

Exact lexical source telescope:

theorem certificate_retractions {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V) (e : V) (he : e ∈ left.ground) (a b : VL) (hedge : left.edge e = s(a,b)) (f : Wheel.Label ↪ V) (hf0 : f 0 = e) (hFresh : Disjoint left.ground (Wheel.Y.image f)) (c : Certificate left.ground left.rows.root)

    (y : Space (project (endpoint (certificate left e he a b hedge f hf0 hFresh c).core (certificate left e he a b hedge f hf0 hFresh c).critical)))

    (z : Space (project (delta {(certificate left e he a b hedge f hf0 hFresh c).vertex}))) :

    (certificate left e he a b hedge f hf0 hFresh c).main.sequenceRetraction ((certificate left e he a b hedge f hf0 hFresh c).main.inclusion y) = y ∧

    (certificate left e he a b hedge f hf0 hFresh c).separate.sequenceRetraction ((certificate left e he a b hedge f hf0 hFresh c).separate.inclusion z) = z

Actual source body:

:=

  ⟨(out).main.sequenceRetraction_inclusion y,

   (out).separate.sequenceRetraction_inclusion z⟩

Dependencies: native Sequence.sequenceRetraction_inclusion for both constructed lists

Real consumers: later geometry attachment consumer (not implemented here)

Proof-content trace: Real native retraction/inclusion endpoint equations; no replacement topology, retraction field or new authority.

**Definition 1.22 (atRetainedEdge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.atRetainedEdge

Exact lexical source telescope:

def atRetainedEdge {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V)

    (c : Certificate left.ground left.rows.root) (e : V) (he : e ∈ left.ground)

    (f : Wheel.Label ↪ V) (hf0 : f 0 = e)

    (hFresh : Disjoint left.ground (Wheel.Y.image f)) :

    Σ g : PhysicalGlue VL Wheel.Label V, Certificate g.data.ground g.data.rows.root

Actual source body:

:=

  let ab := selectedEnds left e

  ⟨attachment left e he ab.1.1 ab.1.2 ab.2 f hf0 hFresh,

   certificate left e he ab.1.1 ab.1.2 ab.2 f hf0 hFresh c⟩

Dependencies: private selectedEnds using SAME G1 Sym2.ind; attachment; certificate

Real consumers: atRetainedEdge_consumed; later G3 state recursion

Proof-content trace: Direct arbitrary-retained-edge handoff. Existing PhysicalGlue/native Certificate dependent pair; caller supplies no orientation or desired graph-root equation.

**Theorem 1.23 (atRetainedEdge_consumed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge_consumed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge_consumed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate.atRetainedEdge_consumed

Exact lexical source telescope:

theorem atRetainedEdge_consumed {VL V : Type*} [Fintype V] [DecidableEq V] (left : GraphData VL V)

    (c : Certificate left.ground left.rows.root) (e : V) (he : e ∈ left.ground)

    (f : Wheel.Label ↪ V) (hf0 : f 0 = e)

    (hFresh : Disjoint left.ground (Wheel.Y.image f)) :

    let S := atRetainedEdge left c e he f hf0 hFresh

    S.1.left = left ∧ S.1.right = Wheel.ambientGraph f ∧ S.1.e = e ∧

    S.1.data.ground = left.ground.erase e ∪ Wheel.Y.image f ∧

    S.2.critical = c.critical.image (wheelCell e (f 1) (f 3) (f 4)) ∧

    S.2.vertex ∈ S.1.data.ground ∧ S.2.vertex ≠ e ∧

    orderedPairs S.2.main =

      WheelSupplier.oneStepMainFrom e f c.critical (orderedPairs c.main) ∧

    orderedPairs S.2.separate =

      WheelSupplier.oneStepSeparateFrom (left.ground.erase e) e f c.critical c.vertex

        (orderedPairs c.separate)

Actual source body:

:= by

  dsimp only [atRetainedEdge]

  refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩

  · exact certificate_critical left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2

      (selectedEnds left e).2 f hf0 hFresh c

  · exact (certificate_survives left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2

      (selectedEnds left e).2 f hf0 hFresh c).1

  · exact (certificate_survives left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2

      (selectedEnds left e).2 f hf0 hFresh c).2

  · exact certificate_main_order left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2

      (selectedEnds left e).2 f hf0 hFresh c

  · exact certificate_separate_order left e he (selectedEnds left e).1.1 (selectedEnds left e).1.2

      (selectedEnds left e).2 f hf0 hFresh c

Dependencies: constructed atRetainedEdge; certificate_critical/survives/main_order/separate_order

Real consumers: later G3 recursion handoff (not implemented here)

Proof-content trace: Derived originating graph/ground, critical transform, surviving endpoint and BOTH exact L1 schedules. No history or list identity premise.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.atRetainedEdge_consumed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_chords`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_ground`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.attachment_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_at_core`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_away_from_core`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_boundary`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_cells`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_current_cofaces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_fixed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_main_order`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retained_endpoints`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_retractions`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_fixed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_separate_order`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_statistics`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_survives`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate.certificate_vertex`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel](PhysicalWheel.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier](WheelSupplier.md)
