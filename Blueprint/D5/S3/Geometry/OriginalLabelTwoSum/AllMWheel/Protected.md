# ProtectedDocument

## Abstract

Actual maximal-critical protection, path Gamma and ghost-retaining zero fillings on the original wheel grounds.

Every new public API is quoted below with the full literal SOURCE context, telescope, body and qualified owner. There are no new structures, inductives, constructors or projections. The sole imported authorities remain FiniteProtectedDualWord.Symbol/Word/Contract, CollapsePair and Sequence; Filling/Certificate/Rows/compileParent remain the original consumer interfaces. All imported record fields are constructed in the source owner, including the helpers in its imported construction modules. The quoted section-variable context is literal source, not an assertion that unused variables become elaborated binders.  The geometric constructions and physical-history correspondence belong to their respective modules; this local interface does not assert an unrestricted all-plane supplier.

**Definition 1.1 (pathContract).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathContract`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathContract (m : Nat) (hm : 3 ≤ m) :

    Contract (ground m) (pathFamily (pathRootPath m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathContract

def pathContract (m : Nat) (hm : 3 ≤ m) :

    Contract (ground m) (pathFamily (pathRootPath m hm)) :=

  maximalContract (pathRootWordData m hm)

    (by

      intro S hS U hU hSU

      apply path_critical_maximal _ (pathRootPath_nodup m hm) S _ U hU hSU

      simpa only [root_word] using hS)

    (root_pair_proper m hm)

Definitions and proofs are in the paired Lean module.

/-- Exact original path-row root, retaining the fixed ambient labels. -/

**Theorem 1.2 (pathRoot_rawDual).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathRoot_rawDual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathRoot_rawDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathRoot_rawDual (m : Nat) (hm : 3 ≤ m) :

    rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathRoot_rawDual

theorem pathRoot_rawDual (m : Nat) (hm : 3 ≤ m) :

    rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm :=

  root_dual m hm

Definitions and proofs are in the paired Lean module.

/-- P04's partial filling is also present in both obstructed classes.

    The cells are fixed-ground complements, never raw path criticals. -/

**Definition 1.3 (pathFilling).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathFilling`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathFilling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathFilling (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (pathRoot m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathFilling

def pathFilling (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (pathRoot m hm) := by

  let d := pathContract m hm

  have hd : rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm :=

    root_dual m hm

  have hc := maximal_cells d.protected

    (by

      intro T hT

      have ht := d.protected_subset T hT

      refine ⟨ht, ?_⟩

      have hs := (root_independent m hm T).mp ht

      refine Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, ?_⟩

      intro he

      have h2 : secondLabel m hm ∈ T := by rw [he]; simp [ground, secondLabel]

      let z : Label m := ⟨3, by omega⟩

      have h3 : z ∈ T := by rw [he]; simp [ground, z]

      exact hs.2.1 _ h2 z h3 (by simp [secondLabel]) (by simp [z, secondLabel]))

    (by

      intro T hT U hU hTU

      apply path_critical_maximal _ (pathRootPath_nodup m hm) T _ U hU hTU

      have h := (criticalFaces_mem _ T).mp hT

      simpa only [d, pathContract, maximalContract, root_word] using h)

  refine {

    empty_mem := ?_

    collar := pathRoot m hm

    critical := d.protected.image (fun T => ground m \ T)

    contains := le_rfl

    supported := ((rimRows m (by omega)).without (interfaceRow m hm)).root_supported

    critical_supported := ?_

    cells := hd ▸ hc

    main := d.protectedDualWordSequence.cast rfl ?_

    separate := Sequence.refl _ }

  · rw [← hd, dual_mem]

    refine ⟨Finset.empty_subset _, ?_⟩

    intro h

    have hi := (root_independent m hm _).mp h

    simp only [Finset.sdiff_empty] at hi

    exact hi.2.1 (secondLabel m hm) (by simp [ground, secondLabel])

      (⟨3, by omega⟩ : Label m) (by simp [ground])

      (by simp [secondLabel]) (by simp [secondLabel])

  · intro s hs

    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs

    exact Finset.sdiff_subset

  · change project (rawEndpoint _ _ _ _) = _

    rw [contract_endpoint d, hd]

Definitions and proofs are in the paired Lean module.

/-- Genuine good-residue Gamma, with its no-critical premise derived from m.

    This is the sufficiency direction, not the Euler necessity theorem. -/

**Definition 1.4 (gammaGood).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.gammaGood`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.gammaGood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def gammaGood (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Sequence (project (delta (ground m))) (project (pathRoot m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.gammaGood

def gammaGood (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    Sequence (project (delta (ground m))) (project (pathRoot m hm)) := by

  have S := (pathRootWordData m hm).noCritical_unprotected

    (by simpa only [root_word] using pathRootPath_noCritical m hm hg)

    (root_pair_proper m hm)

  exact S.cast rfl (congrArg project (root_dual m hm))

Definitions and proofs are in the paired Lean module.

/-- Actual zero-filling Contract on Z, with the forbidden endpoints retained

    as ghosts. At m=3 and 4 H contains the raw EMPTY critical face. -/

**Definition 1.5 (zeroContract).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.zeroContract`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.zeroContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroContract (m : Nat) (hm : 3 ≤ m) :

    Contract (tailGround m hm) (pathFamily (cyclePathTail m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.zeroContract

def zeroContract (m : Nat) (hm : 3 ≤ m) :

    Contract (tailGround m hm) (pathFamily (cyclePathTail m hm)) := by

  let p := cycleTailWordData m hm

  let d : Word (tailGround m hm) (pathFamily (cyclePathTail m hm)) := {

    word := p.word

    supported := by

      intro s hs x hx

      apply (tail_mem m hm x).mpr

      have ht := p.supported s hs hx

      exact le_trans (by omega) ((cyclePathTail_vertices m hm x).mp ht).1

    pair_data := p.pair_data

    critical_data := p.critical_data

    partition := p.partition

    covers := p.covers

    pair_dependency := p.pair_dependency

    critical_dependency := p.critical_dependency }

  exact maximalContract d

    (by

      intro S hS U hU hSU

      apply path_critical_maximal _ (cyclePathTail_nodup m hm) S _ U hU hSU

      simpa only [d, p, cycleTailWordData, pathWordData_word] using hS)

    (by

      intro L v h

      have hU := d.pair_data L v h

      have hs := d.supported _ hU.2.1

      refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩

      intro he

      let z : Label m := ⟨3, by omega⟩

      have hz : z ∈ insert v L := by rw [he]; exact (tail_mem m hm z).mpr (by rfl)

      have ht := p.supported _ hU.2.1 hz

      have hn := (cyclePathTail_vertices m hm z).mp ht

      dsimp [z] at hn

      omega)

Definitions and proofs are in the paired Lean module.

/-- P05 for every m>=3: actual main list, identity standalone collar, and

    full proper boundaries/absence/antichain on the unchanged Z. -/

**Definition 1.6 (fill0).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def fill0 (m : Nat) (hm : 3 ≤ m) : Filling (tailGround m hm) (A0 m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill0

def fill0 (m : Nat) (hm : 3 ≤ m) : Filling (tailGround m hm) (A0 m hm) := by

  let d := zeroContract m hm

  have hd := zero_dual m hm

  have hp : ∀ T ∈ d.protected, T ⊂ tailGround m hm := by

    intro T hT

    have ht := d.protected_subset T hT

    have hs := d.supported T ht

    refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩

    intro he

    let z : Label m := ⟨3, by omega⟩

    have hz : z ∈ T := by rw [he]; exact (tail_mem m hm z).mpr (by rfl)

    have htail := (mem_pathIndependentOn _ T).mp ((mem_pathFamily _ T).mp ht)

    have hn := (cyclePathTail_vertices m hm z).mp (htail.1 hz)

    dsimp [z] at hn

    omega

  have hc := maximal_cells d.protected

    (by intro T hT; exact ⟨d.protected_subset T hT, hp T hT⟩)

    (by

      intro T hT U hU hTU

      apply path_critical_maximal _ (cyclePathTail_nodup m hm) T _ U hU hTU

      have h := (criticalFaces_mem _ T).mp hT

      simpa only [d, zeroContract, maximalContract, cycleTailWordData, pathWordData_word] using h)

  refine {

    empty_mem := ?_

    collar := A0 m hm

    critical := d.protected.image (fun T => tailGround m hm \ T)

    contains := le_rfl

    supported := by intro s hs; exact hs.2

    critical_supported := ?_

    cells := hd ▸ hc

    main := d.protectedDualWordSequence.cast rfl ?_

    separate := Sequence.refl _ }

  · rw [← hd, dual_mem]

    refine ⟨Finset.empty_subset _, ?_⟩

    intro h

    have ht := (mem_pathIndependentOn _ _).mp ((mem_pathFamily _ _).mp h)

    let z : Label m := ⟨3, by omega⟩

    have hz : z ∈ tailGround m hm := (tail_mem m hm z).mpr (by rfl)

    have hn := (cyclePathTail_vertices m hm z).mp

      (ht.1 (by simpa only [Finset.sdiff_empty] using hz))

    dsimp [z] at hn

    omega

  · intro s hs

    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs

    exact Finset.sdiff_subset

  · change project (rawEndpoint _ _ _ _) = _

    rw [contract_endpoint d, hd]

Definitions and proofs are in the paired Lean module.

/-- Exact zero critical tops, including singleton complements of empty tails. -/

**Theorem 1.7 (fill0_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fill0_critical (m : Nat) (hm : 3 ≤ m) :

    (fill0 m hm).critical = if m % 3 = 2 then ∅ else {eta0 m hm}

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill0_critical

theorem fill0_critical (m : Nat) (hm : 3 ≤ m) :

    (fill0 m hm).critical = if m % 3 = 2 then ∅ else {eta0 m hm} := by

  change (criticalFaces (tailWord m hm)).image (fun T => tailGround m hm \ T) = _

  rw [tailWord_critical_formula]

  split_ifs <;> simp [eta0]

Definitions and proofs are in the paired Lean module.

/-- P01's dual on Z keeps both forbidden endpoint ghosts. -/

**Theorem 1.8 (A0_rawDual).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.A0_rawDual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.A0_rawDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem A0_rawDual (m : Nat) (hm : 3 ≤ m) :

    rawDual (tailGround m hm) (pathFamily (cyclePathTail m hm)) = A0 m hm

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.A0_rawDual

theorem A0_rawDual (m : Nat) (hm : 3 ≤ m) :

    rawDual (tailGround m hm) (pathFamily (cyclePathTail m hm)) = A0 m hm :=

  zero_dual m hm

**Theorem 1.9 (wheelRoot_eq_A1).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.wheelRoot_eq_A1`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.wheelRoot_eq_A1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem wheelRoot_eq_A1 (m : Nat) (hm : 3 ≤ m) :

    wheelRoot m (by omega) = A1 m hm

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.wheelRoot_eq_A1

theorem wheelRoot_eq_A1 (m : Nat) (hm : 3 ≤ m) :

    wheelRoot m (by omega) = A1 m hm := by

  apply SetLike.ext

  intro s

  change (∃ i : Fin m, s ⊆ ground m \ rimEdge m (by omega) i) ↔

    (∃ i : {i : Fin m // i ≠ interfaceRow m hm},

      s ⊆ ground m \ rimEdge m (by omega) i.val) ∨ s ⊆ tailGround m hm

  constructor

  · rintro ⟨i, hi⟩

    by_cases he : i = interfaceRow m hm

    · right

      simpa only [he, interface_edge, tailGround] using hi

    · exact Or.inl ⟨⟨i, he⟩, hi⟩

  · rintro (⟨i, hi⟩ | hi)

    · exact ⟨i.val, hi⟩

    · exact ⟨interfaceRow m hm, by simpa only [interface_edge, tailGround] using hi⟩

**Definition 1.10 (excludedCycleContract).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.excludedCycleContract`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.excludedCycleContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def excludedCycleContract (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    Contract (ground m) (facets (cycleIndependentOn m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.excludedCycleContract

def excludedCycleContract (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    Contract (ground m) (facets (cycleIndependentOn m hm)) :=

  maximalContract (cycleWordData m hm) (by

    intro S hS U hU hSU

    exact cycle_critical_maximal m hm hr S hS U hU hSU)

    (by intro L v h; exact cycle_face_proper m hm _ ((cycleWordData m hm).pair_data L v h).2.1)

Definitions and proofs are in the paired Lean module.

/-- Genuine P06 filling in residues zero and two, with collar exactly A1,

    all proper critical boundaries, and the separate identity list. -/

**Definition 1.11 (fill1Excluded).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def fill1Excluded (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    Filling (ground m) (A1 m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill1Excluded

def fill1Excluded (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    Filling (ground m) (A1 m hm) := by

  let d := excludedCycleContract m hm hr

  have hd : rawDual (ground m) (facets (cycleIndependentOn m hm)) = A1 m hm :=

    (cycleWord_rawDual_eq_wheelRoot m hm).trans (wheelRoot_eq_A1 m hm)

  have hc := maximal_cells d.protected

    (by intro T hT; exact ⟨d.protected_subset T hT,

      cycle_face_proper m hm T (d.protected_subset T hT)⟩)

    (by intro T hT U hU hTU

        exact cycle_critical_maximal m hm hr T ((criticalFaces_mem _ T).mp hT) U hU hTU)

  refine {

    empty_mem := ?_

    collar := A1 m hm

    critical := d.protected.image (fun T => ground m \ T)

    contains := le_rfl

    supported := by intro s hs; rw [← wheelRoot_eq_A1 m hm] at hs

                    exact (rimRows m (by omega)).root_supported s hs

    critical_supported := ?_

    cells := hd ▸ hc

    main := d.protectedDualWordSequence.cast rfl ?_

    separate := Sequence.refl _ }

  · rw [← hd, dual_mem]

    refine ⟨Finset.empty_subset _, ?_⟩

    intro h

    have hp := cycle_face_proper m hm _ h

    simp only [Finset.sdiff_empty] at hp

    exact hp.ne rfl

  · intro s hs

    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs

    exact Finset.sdiff_subset

  · change project (rawEndpoint _ _ _ _) = _

    rw [contract_endpoint d, hd]

Definitions and proofs are in the paired Lean module.

/-- The exact two/one critical tops use fixed-ground cycle complements. -/

**Theorem 1.12 (fill1Excluded_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fill1Excluded_critical (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    (fill1Excluded m hm hr).critical = cycleCritical m hm

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill1Excluded_critical

theorem fill1Excluded_critical (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :

    (fill1Excluded m hm hr).critical = cycleCritical m hm := by

  exact (cycleCritical_eq_complements m hm).symm

Definitions and proofs are in the paired Lean module.

/- A pivot changes from the earlier residue lo+1 to the later residue lo.

   This finite set is only arithmetic notation used in the EXISTING Word. -/

**Definition 1.13 (collarA).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarA`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarA (m : Nat) (j : Fin (m/3)) : Finset (Label m)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarA

def collarA (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=

  insert (lastLabel m) (switchBase m 2 (m/3) j.val)

**Definition 1.14 (collarPivot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarPivot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarPivot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarPivot (m : Nat) (j : Fin (m/3)) : Label m

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarPivot

def collarPivot (m : Nat) (j : Fin (m/3)) : Label m :=

  ⟨3*j.val+2, by have := j.isLt; omega⟩

**Definition 1.15 (collarB).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarB`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarB (m : Nat) (j : Fin (m/3)) : Finset (Label m)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarB

def collarB (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=

  insert (collarPivot m j) (collarA m j)

**Definition 1.16 (collarUpper).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarUpper`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarUpper (m : Nat) (j : Fin (m/3)) : Finset (Label m)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarUpper

def collarUpper (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarA m j

**Definition 1.17 (collarLower).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarLower`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarLower (m : Nat) (j : Fin (m/3)) : Finset (Label m)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarLower

def collarLower (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarB m j

**Definition 1.18 (goodH).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodH`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def goodH (m : Nat) : Finset (Finset (Label m))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.goodH

def goodH (m : Nat) : Finset (Finset (Label m)) :=

  insert (labelsCongruent m 2 2)

    ((Finset.univ : Finset (Fin (m/3))).biUnion (fun j => {collarA m j, collarB m j}))

**Definition 1.19 (goodCycleContract).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodCycleContract`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodCycleContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def goodCycleContract (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Contract (ground m) (facets (cycleIndependentOn m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.goodCycleContract

def goodCycleContract (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Contract (ground m) (facets (cycleIndependentOn m hm)) where

  toWord := cycleWordData m hm

  «protected» := goodH m

  protected_subset := by

    intro T hT

    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩

    · exact (cycleWordData m hm).critical_data _ (good_critical m hm h1)

    · exact (collar_pair_data m hm h1 j).1

    · exact (collar_pair_data m hm h1 j).2.1

  protected_upward := by

    intro T U hT hU hTU

    apply (mem_goodH m U).mpr

    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩

    · rcases critical_supersets m hm h1 U hU hTU with he | he

      · exact Or.inl he

      · exact Or.inr ⟨⟨0, good_k m hm h1⟩, Or.inr he⟩

    all_goals

      have haU : collarA m j ⊆ U := by

        first | exact hTU | exact (Finset.subset_insert _ _).trans hTU

      rcases collar_supersets m hm h1 j U hU haU with he | he | ⟨hj, he⟩

      · exact Or.inr ⟨j, Or.inl he⟩

      · exact Or.inr ⟨j, Or.inr he⟩

      · exact Or.inr ⟨⟨j.val+1, hj⟩, Or.inr he⟩

  protected_pair := by

    intro L v hp

    have whole : ∀ T ∈ (Symbol.pair L v).faces, T ∈ goodH m →

        ∀ U ∈ (Symbol.pair L v).faces, U ∈ goodH m := by

      intro T hT hH U hU

      rcases (mem_goodH m T).mp hH with he | ⟨j, he | he⟩

      · have ho := word_owner (cycleWordData m hm).partition hp (good_critical m hm h1)

          hT (by simpa only [he, Symbol.faces, Finset.mem_singleton])

        cases ho

      all_goals

        have ht : T ∈ (Symbol.pair (collarA m j) (collarPivot m j)).faces := by

          simp [Symbol.faces, he, collarB]

        have ho := word_owner (cycleWordData m hm).partition hp

          (collar_pair_in_word m hm h1 j) hT ht

        rw [ho] at hU

        rcases (show U = collarA m j ∨ U = collarB m j by

          simpa only [Symbol.faces, Finset.mem_insert, Finset.mem_singleton, collarB] using hU)

          with he | he

        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inl he⟩)

        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inr he⟩)

    exact ⟨fun h => whole L (by simp [Symbol.faces]) h _ (by simp [Symbol.faces]),

      fun h => whole (insert v L) (by simp [Symbol.faces]) h _ (by simp [Symbol.faces])⟩

  critical_protected := by

    intro S hS

    have hc := (criticalFaces_mem _ S).mpr hS

    rw [cycleWordData_word, cycleWord_critical_formula, if_neg (by omega : m % 3 ≠ 0), if_pos h1] at hc

    exact (mem_goodH m S).mpr (Or.inl (Finset.mem_singleton.mp hc))

  emitted_proper := by

    intro L v hp _

    exact cycle_face_proper m hm _ ((cycleWordData m hm).pair_data L v hp).2.1

Definitions and proofs are in the paired Lean module.

/-- Standalone B1, without the retained eta1 simplex. -/

**Definition 1.20 (collarCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarCore (m : Nat) (hm : 3 ≤ m) : Family (Label m)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarCore

def collarCore (m : Nat) (hm : 3 ≤ m) : Family (Label m) :=

  A1 m hm ⊔ facets ((Finset.univ : Finset (Fin (m/3))).image (collarUpper m))

**Definition 1.21 (collarSequence).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarSequence`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def collarSequence (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Sequence (project (collarCore m hm)) (project (A1 m hm))

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.collarSequence

def collarSequence (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Sequence (project (collarCore m hm)) (project (A1 m hm)) :=

  (collarFrom m hm h1 0 (Nat.zero_le _)).cast

    (congrArg project (collarState_start m hm h1)) rfl

Definitions and proofs are in the paired Lean module.

/-- Good-class fill1 with actual main list, exact critical eta1 and the

    SEPARATE collar just constructed. -/

**Definition 1.22 (fill1Good).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1Good`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def fill1Good (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Filling (ground m) (A1 m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill1Good

def fill1Good (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :

    Filling (ground m) (A1 m hm) where

  empty_mem := by

    rw [← good_dual m hm, dual_mem]

    refine ⟨Finset.empty_subset _, ?_⟩

    intro h

    have hp := cycle_face_proper m hm _ h

    simp only [Finset.sdiff_empty] at hp

    exact hp.ne rfl

  collar := collarCore m hm

  critical := {eta1 m hm}

  contains := le_sup_left

  supported := by

    intro s hs

    rcases hs with hs | ⟨t, ht, hst⟩

    · rw [← wheelRoot_eq_A1 m hm] at hs

      exact (rimRows m (by omega)).root_supported s hs

    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht

      exact hst.trans Finset.sdiff_subset

  critical_supported := by intro s hs; rw [Finset.mem_singleton.mp hs]; exact Finset.sdiff_subset

  cells := eta_good_cells m hm h1

  main := (goodCycleContract m hm h1).protectedDualWordSequence.cast rfl

    (congrArg project (good_endpoint m hm h1))

  separate := collarSequence m hm h1

Definitions and proofs are in the paired Lean module.

/-- Both residues and the collar residue share the original Filling API;

    none of the desired outputs is an input to this all-m function. -/

**Definition 1.23 (fill1).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def fill1 (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (A1 m hm)

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill1

def fill1 (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (A1 m hm) :=

  if h1 : m % 3 = 1 then fill1Good m hm h1 else fill1Excluded m hm h1

**Theorem 1.24 (fill1_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fill1_critical (m : Nat) (hm : 3 ≤ m) :

    (fill1 m hm).critical = cycleCritical m hm

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.fill1_critical

theorem fill1_critical (m : Nat) (hm : 3 ≤ m) :

    (fill1 m hm).critical = cycleCritical m hm := by

  unfold fill1

  split_ifs with h1

  · simp only [fill1Good, cycleCritical, if_neg (by omega : m % 3 ≠ 0), if_pos h1, eta1]

  · exact fill1Excluded_critical m hm h1

**Theorem 1.25 (pathFilling_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.pathFilling_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.pathFilling_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathFilling_critical (m : Nat) (hm : 3 ≤ m) :

    (pathFilling m hm).critical =

      if m % 3 = 1 then ∅ else

        {ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)}

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.pathFilling_critical

theorem pathFilling_critical (m : Nat) (hm : 3 ≤ m) :

    (pathFilling m hm).critical =

      if m % 3 = 1 then ∅ else

        {ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)} := by

  change (criticalFaces (pathRootWordData m hm).word).image (fun T => ground m \ T) = _

  rw [root_word, pathWord_critical_formula _ (pathRootPath_nodup m hm), pathRootPath_length]

  split_ifs <;> simp

Definitions and proofs are in the paired Lean module.

/-- Necessity includes BOTH excluded residues. It uses ordinary finite Euler

    invariance and the actual one-critical partial filling; no homology or

    inferred collapse from a contractible target is used. -/

**Theorem 1.26 (gamma_iff).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.gamma_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.gamma_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

noncomputable section

open Set Finset

namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

open FiniteProtectedDualWord OriginalLabelTwoSum

open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gamma_iff (m : Nat) (hm : 3 ≤ m) :

    Nonempty (Sequence (project (delta (ground m))) (project (pathRoot m hm))) ↔

      goodResidue m

### Source text

Exact SOURCE declaration and body from D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.lean; D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.gamma_iff

theorem gamma_iff (m : Nat) (hm : 3 ≤ m) :

    Nonempty (Sequence (project (delta (ground m))) (project (pathRoot m hm))) ↔

      goodResidue m := by

  constructor

  · rintro ⟨G⟩

    by_contra hn

    have hr : m % 3 ≠ 1 := by

      intro h1

      exact hn ⟨m/3, good_width m h1⟩

    let d := ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)

    have hc : (pathFilling m hm).critical = {d} := by

      rw [pathFilling_critical, if_neg hr]

    have hmain := sequence_euler (pathFilling m hm).main

    have hgamma := sequence_euler G

    have hcells : CriticalData (pathRoot m hm) {d} := by

      rw [← hc]

      exact (pathFilling m hm).cells

    have hcell := cell_euler (pathRoot m hm) d hcells

    change nativeEuler (project (delta (ground m))) =

      nativeEuler (project (endpoint (pathRoot m hm) (pathFilling m hm).critical)) at hmain

    rw [hc] at hmain

    have hzero : (-1 : Int)^d.card = 0 := by omega

    exact (pow_ne_zero d.card (by decide : (-1 : Int) ≠ 0)) hzero

  · intro hg

    exact ⟨gammaGood m hm hg⟩

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarA`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarB`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarCore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarLower`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarPivot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarSequence`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.collarUpper`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1Good`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.fill1_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.gamma_iff`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodCycleContract`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.goodH`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected.pathFilling_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.A0_rawDual`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.excludedCycleContract`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill0_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.fill1Excluded_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.gammaGood`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathContract`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathFilling`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.pathRoot_rawDual`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.wheelRoot_eq_A1`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings.zeroContract`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord](CycleWord.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings](ProtectedFillings.md)
