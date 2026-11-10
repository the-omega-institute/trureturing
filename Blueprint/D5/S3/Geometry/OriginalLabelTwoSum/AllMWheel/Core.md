# CoreDocument

## Abstract

The separate good-path noncover collapse is constructed on the core alone; Gamma is never inverted to infer collapsibility.

Every new public API is quoted below with the full literal SOURCE context, telescope, body and qualified owner. There are no new structures, inductives, constructors or projections. The sole imported authorities remain FiniteProtectedDualWord.Symbol/Word/Contract, CollapsePair and Sequence; Filling/Certificate/Rows/compileParent remain the original consumer interfaces. All imported record fields are constructed in the source owner, including its private helpers. The quoted section-variable context is literal source, not an assertion that unused variables become elaborated binders.  The geometric constructions and physical-history correspondence belong to their respective modules; this local interface does not assert an unrestricted all-plane supplier.

**Definition 1.1 (pathGoodCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathGoodCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathGoodCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteProtectedDualWord

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathGoodCore (vs : List V) (hd : vs.Nodup) (h4 : 4 ≤ vs.length)

    (h1 : vs.length % 3 = 1) :

    Σ p : {p : V // p ∈ vs.toFinset},

      Sequence (project (rawDual vs.toFinset (pathFamily vs))) (project (delta {p.val}))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathGoodCore

def pathGoodCore (vs : List V) (hd : vs.Nodup) (h4 : 4 ≤ vs.length)

    (h1 : vs.length % 3 = 1) :

    Σ p : {p : V // p ∈ vs.toFinset},

      Sequence (project (rawDual vs.toFinset (pathFamily vs))) (project (delta {p.val})) := by

  cases vs with

  | nil => simp at h4

  | cons a vs =>

      cases vs with

      | nil => simp at h4

      | cons b vs =>

          cases vs with

          | nil => simp at h4

          | cons c vs =>

              have hne : 0 < vs.length := by simp only [List.length_cons] at h4; omega

              have hmod : vs.length % 3 = 1 := by simp only [List.length_cons] at h1; omega

              have hs : Supported (a::b::c::vs).toFinset

                  (rawDual (a::b::c::vs).toFinset (pathFamily (a::b::c::vs))) :=

                fun s h => ((noncover_mem _ _).mp h).1

              have hab : a ≠ b := fun h => (List.nodup_cons.mp hd).1 (by simp [h])

              let S := delete_cone_link _ _ a b hs (by simp) (by simp) hab

                (path_link_cone a b (c::vs) hd)

              let T := coreFinish a b c vs hd hne hmod

              exact ⟨T.1, (S.cast rfl (congrArg project (path_delete_formula a b c vs hd))).append T.2⟩

Definitions and proofs are in the paired Lean module.

/-- Separate collapse on E_m ALONE to a retained original label. -/

**Definition 1.2 (pathRootCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathRootCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathRootCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteProtectedDualWord

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathRootCore (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Σ p : {p : Label m // p ∈ ground m},

      Sequence (project (pathRoot m hm)) (project (delta {p.val}))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathRootCore

def pathRootCore (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Σ p : {p : Label m // p ∈ ground m},

      Sequence (project (pathRoot m hm)) (project (delta {p.val})) := by

  let k := Classical.choose hg

  have hk := Classical.choose_spec hg

  have h4 : 4 ≤ m := by omega

  have hmod : m % 3 = 1 := by omega

  let S := pathGoodCore (pathRootPath m hm) (pathRootPath_nodup m hm)

    (by simpa only [pathRootPath_length] using h4)

    (by simpa only [pathRootPath_length] using hmod)

  have hp : S.1.val ∈ ground m := by

    simpa only [pathRootPath_vertices] using S.1.property

  have hsrc : rawDual (pathRootPath m hm).toFinset (pathFamily (pathRootPath m hm)) =

      pathRoot m hm := by rw [pathRootPath_vertices, pathRoot_rawDual]

  exact ⟨⟨S.1.val, hp⟩, S.2.cast (congrArg project hsrc) rfl⟩

Definitions and proofs are in the paired Lean module.

/-- The right wheel's actual absolute certificate: fill0 runs in Delta(Z)

    while fixing E, then the separate list collapses E alone. -/

**Definition 1.3 (wheelCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.wheelCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.wheelCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteProtectedDualWord

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def wheelCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Certificate (ground m) (A1 m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.wheelCertificate

def wheelCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Certificate (ground m) (A1 m hm) := by

  let f := fill0 m hm

  let C := pathRootCore m hm hg

  have hEZ : A0 m hm ≤ pathRoot m hm := inf_le_left

  have hN0 : (∅ : Finset (Label m)) ∈ endpoint (A0 m hm) f.critical := Or.inl f.empty_mem

  let S := liftFibre (delta (tailGround m hm)) (endpoint (A0 m hm) f.critical)

    (pathRoot m hm) ∅ (tailGround m hm) (Finset.empty_subset _) hN0 f.main (by simp)

    (fun _ h => h)

    (by intro x hx; exact (Finset.not_ssubset_empty x hx).elim)

    (by intro t ht h; exact Or.inl ⟨by simpa using h, ht⟩)

  have hstart : pathRoot m hm ⊔ rawJoin (delta ∅) (delta (tailGround m hm)) = A1 m hm := by

    rw [(rawJoin_unit _).1]

    rfl

  have hend : pathRoot m hm ⊔ rawJoin (delta ∅) (endpoint (A0 m hm) f.critical) =

      endpoint (pathRoot m hm) f.critical := by

    rw [(rawJoin_unit _).1]

    change pathRoot m hm ⊔ (A0 m hm ⊔ facets f.critical) = pathRoot m hm ⊔ facets f.critical

    rw [← sup_assoc, sup_eq_left.mpr hEZ]

  have hcore : Supported (ground m) (pathRoot m hm) :=

    ((rimRows m (by omega)).without (interfaceRow m hm)).root_supported

  refine {

    supported := ?_

    core := pathRoot m hm

    critical := f.critical

    vertex := C.1.val

    vertex_mem := ?_

    core_supported := hcore

    critical_supported := by intro s hs; exact (f.critical_supported s hs).trans Finset.sdiff_subset

    cells := ?_

    main := S.cast (congrArg project hstart) (congrArg project hend)

    separate := C.2 }

  · intro s hs

    rcases hs with hs | hs

    · exact hcore s hs

    · exact hs.trans Finset.sdiff_subset

  · exact (C.2.monotone ⟨by simp, by simp⟩).2

  · constructor

    · exact f.cells.nonempty

    · intro s hs hE

      exact f.cells.absent s hs ⟨hE, f.critical_supported s hs⟩

    · intro s hs t hts

      exact hEZ (f.cells.boundary s hs t hts)

    · exact f.cells.antichain

**Definition 1.4 (zeroCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.zeroCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.zeroCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open OriginalLabelTwoSum FiniteProtectedDualWord

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroCore (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2) :

    Σ p : {p : Label m // p ∈ tailGround m hm},

      Sequence (project (A0 m hm)) (project (delta {p.val}))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.zeroCore

def zeroCore (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2) :

    Σ p : {p : Label m // p ∈ tailGround m hm},

      Sequence (project (A0 m hm)) (project (delta {p.val})) := by

  have h5 : 5 ≤ m := by omega

  let a : Label m := ⟨3, by omega⟩

  let b := firstLabel m hm

  let c := lastLabel m

  let vs := cyclePathTail m hm

  have ha : a ∉ vs := by

    rw [← List.mem_toFinset, cyclePathTail_vertices]

    dsimp [a]

    omega

  have hb : b ∉ c::vs := by

    simp only [List.mem_cons, b, c, firstLabel, lastLabel, Fin.ext_iff, not_or]

    constructor

    · omega

    · intro h

      have hx := (cyclePathTail_vertices m hm b).mp (List.mem_toFinset.mpr h)

      dsimp [b, firstLabel] at hx

      omega

  have hc : c ∉ vs := by

    rw [← List.mem_toFinset, cyclePathTail_vertices]

    dsimp [c, lastLabel]

    omega

  have hd : (a::b::c::vs).Nodup := by

    apply List.nodup_cons.mpr

    refine ⟨?_, List.nodup_cons.mpr ⟨hb, List.nodup_cons.mpr

      ⟨hc, cyclePathTail_nodup m hm⟩⟩⟩

    simp only [List.mem_cons, not_or]

    exact ⟨by intro h; have he := congrArg Fin.val h; dsimp [a,b,firstLabel] at he; omega,

      by intro h; have he := congrArg Fin.val h; dsimp [a,c,lastLabel] at he; omega, ha⟩

  have hw : tailGround m hm = insert a (insert c vs.toFinset) := by

    ext x

    simp only [tailGround, ground, rim, Finset.mem_sdiff, Finset.mem_erase,

      Finset.mem_univ, and_true, Finset.mem_insert, Finset.mem_singleton,

      cyclePathTail_vertices, Fin.ext_iff, a, c, firstLabel, secondLabel, lastLabel,

      vs, ne_eq, Fin.val_zero, Fin.val_mk]

    have := x.isLt

    omega

  have hK : Supported vs.toFinset (pathFamily vs) := by

    intro s hs

    exact ((mem_pathIndependentOn vs s).mp ((mem_pathFamily vs s).mp hs)).1

  have hformula := two_ghost_dual a c vs.toFinset (pathFamily vs)

    (by intro h; have he := congrArg Fin.val h; dsimp [a,c,lastLabel] at he; omega)

    (by simpa only [List.mem_toFinset] using ha) (by simpa only [List.mem_toFinset] using hc) hK

  have hD : ((delta (insert a vs.toFinset) ⊔ delta (insert c vs.toFinset)) ⊔

      rawJoin (delta {a,c}) (rawDual vs.toFinset (pathFamily vs))) = A0 m hm := by

    rw [← hformula, ← hw]

    exact A0_rawDual m hm

  let S := coreFinish a b c vs hd (by simp only [vs, cyclePathTail_length]; omega)

    (by simp only [vs, cyclePathTail_length]; omega)

  let G := S.2.cast (congrArg project hD) rfl

  have hp : S.1.val ∈ tailGround m hm := by

    have hpoint : ({S.1.val} : Finset (Label m)) ∈ project (delta {S.1.val}) :=

      ⟨by simp, Finset.Subset.refl _⟩

    have hs := (G.monotone hpoint).2

    exact hs.2 (by simp)

  exact ⟨⟨S.1.val, hp⟩, G⟩

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathGoodCore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.pathRootCore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.wheelCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core.zeroCore`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected](Protected.md)
