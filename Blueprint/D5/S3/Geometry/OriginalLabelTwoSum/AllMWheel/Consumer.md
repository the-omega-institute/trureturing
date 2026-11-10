# ConsumerDocument

## Abstract

Constructed all-width local fillings and Gamma run the existing original-label parent compiler and literal indexed row transport.

Every new public API is quoted below with the full literal SOURCE context, telescope, body and qualified owner. There are no new structures, inductives, constructors or projections. The sole imported authorities remain FiniteProtectedDualWord.Symbol/Word/Contract, CollapsePair and Sequence; Filling/Certificate/Rows/compileParent remain the original consumer interfaces. All imported record fields are constructed in the source owner, including its private helpers. The quoted section-variable context is literal source, not an assertion that unused variables become elaborated binders.  The geometric constructions and physical-history correspondence belong to their respective modules; this local interface does not assert an unrestricted all-plane supplier.

**Definition 1.1 (rimRowCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rimRowCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rimRowCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def rimRowCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Certificate (rimRows m (by omega)).ground (rimRows m (by omega)).root

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.rimRowCertificate

def rimRowCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Certificate (rimRows m (by omega)).ground (rimRows m (by omega)).root := by

  change Certificate (ground m) (wheelRoot m (by omega))

  rw [wheelRoot_eq_A1 m hm]

  exact wheelCertificate m hm hg

Definitions and proofs are in the paired Lean module.

/-- Run the existing parent compiler. The left certificate is its ORIGINAL

    legitimate input; neither local filling, Gamma, Cout nor the desired

    parent certificate is a premise. The e=current-core-vertex case is allowed. -/

**Definition 1.2 (oneStep).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def oneStep (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    {X : Finset V} {e : V} {K : Family V}

    (c : Certificate (insert e X) K) (f : Label m ↪ V)

    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :

    Certificate (X ∪ (ground m).image f)

      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e

        (renameFamily f (pathRoot m hm)) K)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.oneStep

def oneStep (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    {X : Finset V} {e : V} {K : Family V}

    (c : Certificate (insert e X) K) (f : Label m ↪ V)

    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :

    Certificate (X ∪ (ground m).image f)

      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e

        (renameFamily f (pathRoot m hm)) K) := by

  let g0 := retarget (renameFilling f (fill0 m hm)) (interfaces m hm f).2.1

  let g1 := retarget (renameFilling f (fill1 m hm)) (interfaces m hm f).2.2

  let G := (renameSequence f (gammaGood m hm hg)).cast

    (by rw [← project_rename,

      (rename_operations f (ground m) (pathRoot m hm) (pathRoot m hm) ∅).1])

    (project_rename f (pathRoot m hm)).symm

  have heY : e ∉ (ground m).image f := hf0 ▸ fresh_zero m f

  have hR := Finset.image_subset_image (f := (f : Label m → V)) (rim_subset m hm)

  have hRne : ((rim m hm).image f).Nonempty :=

    Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩

  have hE : Supported ((ground m).image f) (renameFamily f (pathRoot m hm)) := by

    rintro s ⟨t, ht, rfl⟩

    exact Finset.image_subset_image

      (((rimRows m (by omega)).without (interfaceRow m hm)).root_supported t ht)

  exact compileParent c g0 g1 heX heY hXY hR hRne (interfaces m hm f).1 hE (Or.inl ⟨G⟩)

**Theorem 1.3 (oneStep_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem oneStep_critical (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    {X : Finset V} {e : V} {K : Family V}

    (c : Certificate (insert e X) K) (f : Label m ↪ V)

    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :

    (oneStep m hm hg c f hf0 heX hXY).critical = parentCritical e c.critical

      ((fill0 m hm).critical.image (fun s => s.image f))

      ((fill1 m hm).critical.image (fun s => s.image f))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.oneStep_critical

theorem oneStep_critical (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    {X : Finset V} {e : V} {K : Family V}

    (c : Certificate (insert e X) K) (f : Label m ↪ V)

    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :

    (oneStep m hm hg c f hf0 heX hXY).critical = parentCritical e c.critical

      ((fill0 m hm).critical.image (fun s => s.image f))

      ((fill1 m hm).critical.image (fun s => s.image f)) := by

  rfl

Definitions and proofs are in the paired Lean module.

/-- Actual indexed row substitution, with m=wheel width and no history-length

    parameter conflated with it. All retained original labels and ghosts stay. -/

**Definition 1.4 (appendRimRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.appendRimRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.appendRimRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def appendRimRows (r : Rows V) (e : V) (he : e ∈ r.ground)

    (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) (hf0 : f 0 = e) : Rows V

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.appendRimRows

def appendRimRows (r : Rows V) (e : V) (he : e ∈ r.ground)

    (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) (hf0 : f 0 = e) : Rows V :=

  transportedRows (r.ground.erase e) ((ground m).image f) e ((rim m hm).image f)

    r (renameRows f (rimRows m (by omega))) (interfaceRow m hm)

    (Finset.insert_erase he).symm rfl (by simp) (hf0 ▸ fresh_zero m f)

    (Finset.image_subset_image (rim_subset m hm))

**Definition 1.5 (rowStep).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rowStep`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rowStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def rowStep (r : Rows V) (c : Certificate r.ground r.root)

    (e : V) (he : e ∈ r.ground) (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    (f : Label m ↪ V) (hf0 : f 0 = e) (hnew : Disjoint r.ground ((ground m).image f)) :

    Certificate (appendRimRows r e he m hm f hf0).ground

      (appendRimRows r e he m hm f hf0).root

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.rowStep

def rowStep (r : Rows V) (c : Certificate r.ground r.root)

    (e : V) (he : e ∈ r.ground) (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)

    (f : Label m ↪ V) (hf0 : f 0 = e) (hnew : Disjoint r.ground ((ground m).image f)) :

    Certificate (appendRimRows r e he m hm f hf0).ground

      (appendRimRows r e he m hm f hf0).root := by

  let c' : Certificate (insert e (r.ground.erase e)) r.root := by

    rw [Finset.insert_erase he]

    exact c

  have hXY : Disjoint (r.ground.erase e) ((ground m).image f) :=

    Finset.disjoint_left.mpr (fun x hx hy => Finset.disjoint_left.mp hnew

      (Finset.mem_erase.mp hx).2 hy)

  let out := oneStep m hm hg c' f hf0 (by simp) hXY

  rw [append_root r e he m hm f hf0 hnew]

  exact out

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.appendRimRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.oneStep_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rimRowCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer.rowStep`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core](Core.md)
