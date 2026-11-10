# CycleWordDocument

## Abstract

The literal three-block cycle list is a P02 Word on every original rim.

The selected AllMWheel, PathWord and sole FiniteProtectedDualWord authorities are immutable imports. This file adds no structure and generates no constructor/projection APIs. The full source-stated imported Word contract, including all eight field clauses, is quoted below with its source owner; no emitted telescope is asserted. Kernel/native/Scribe/Reg/gates/remote PR/dev acceptance remain due.

## Source text

Immutable imported owner D5/S3/Geometry/FiniteProtectedDualWord; namespace D5.S3.Geometry.FiniteProtectedDualWord; variable {V : Type*} [Fintype V] [DecidableEq V]

structure Word (W : Finset V) (K : Family V) where

  word : List (Symbol V)

  supported : OriginalLabelTwoSum.Supported W K

  pair_data : ∀ L v, Symbol.pair L v ∈ word →

    L ∈ K ∧ insert v L ∈ K ∧ v ∉ L

  critical_data : ∀ S, Symbol.critical S ∈ word → S ∈ K

  partition : word.Pairwise (fun σ τ => Disjoint σ.faces τ.faces)

  covers : ∀ s, s ∈ K ↔ ∃ i : Fin word.length, s ∈ (word.get i).faces

  pair_dependency : ∀ («prefix» suffix : List (Symbol V)) L v,

    word = «prefix» ++ Symbol.pair L v :: suffix →

    ∀ T, T ⊂ insert v L → T ≠ L → ∃ σ ∈ «prefix», T ∈ σ.faces

  critical_dependency : ∀ («prefix» suffix : List (Symbol V)) S,

    word = «prefix» ++ Symbol.critical S :: suffix →

    ∀ T, T ⊂ S → ∃ σ ∈ «prefix», T ∈ σ.faces

The construction distinguishes the following obligations: protected upward and whole-symbol H with every unexecuted critical; fill0 retaining ghosts, fill1 in every residue; Gamma iff and both obstruction residues; standalone B1/Q1; parent compiler; arbitrary history length distinct from width, markings, physical realizations and all-plane supplier; the arbitrary-plane supplier. In particular m=4 does not justify empty protection. No native selectors, green Reg result or local-fill success is claimed.

**Theorem 1.1 (mem_cycleIndependentOn).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleIndependentOn`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleIndependentOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem mem_cycleIndependentOn (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :

    s ∈ cycleIndependentOn m hm ↔ s ⊆ ground m ∧

      ∀ e ∈ cycleEdges m hm, ¬ e ⊆ s

**Theorem 1.2 (cycleIndependentOn_lower).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem cycleIndependentOn_lower (m : Nat) (hm : 3 ≤ m)

    {s t : Finset (Label m)} (hs : s ∈ cycleIndependentOn m hm) (ht : t ⊆ s) :

    t ∈ cycleIndependentOn m hm

**Theorem 1.3 (mem_cycleFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

@[simp] theorem mem_cycleFamily (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :

    s ∈ facets (cycleIndependentOn m hm) ↔ s ∈ cycleIndependentOn m hm

**Theorem 1.4 (cycleIndependentOn_decomposition).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem cycleIndependentOn_decomposition (m : Nat) (hm : 3 ≤ m) :

    cycleIndependentOn m hm =

      ((pathIndependentOn (cyclePath m hm) ∪

        (pathIndependentOn (cyclePath m hm)).image (insert (firstLabel m hm))) ∪

        (pathIndependentOn (cyclePathTail m hm)).image (insert (secondLabel m hm))) ∪

        (pathIndependentOn (cyclePathLast m hm)).image (insert (lastLabel m))

**Definition 1.5 (cycleWordData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner.  Its literal word is cycleWord m hm. All eight fields are proved by the sorted first block and two actual immutable path Words, with base inclusions derived from cyclic endpoints. No new structure, constructor or projection authority is introduced.

### Source text

def cycleWordData (m : Nat) (hm : 3 ≤ m) :

    Word (ground m) (facets (cycleIndependentOn m hm))

**Theorem 1.6 (cycleWordData_word).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData_word`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

@[simp] theorem cycleWordData_word (m : Nat) (hm : 3 ≤ m) :

    (cycleWordData m hm).word = cycleWord m hm

**Theorem 1.7 (cycleWord_covers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_covers`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem cycleWord_covers (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :

    s ∈ cycleIndependentOn m hm ↔

      ∃ i : Fin (cycleWord m hm).length, s ∈ ((cycleWord m hm).get i).faces

**Theorem 1.8 (cycleWord_critical_blocks).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem cycleWord_critical_blocks (m : Nat) (hm : 3 ≤ m) :

    criticalFaces (cycleWord m hm) =

      (pathCritical (cyclePathTail m hm)).image (insert (secondLabel m hm)) ∪

      (pathCritical (cyclePathLast m hm)).image (insert (lastLabel m))

**Theorem 1.9 (pathChosen_labelInterval).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.pathChosen_labelInterval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.pathChosen_labelInterval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem pathChosen_labelInterval (m lo n : Nat) (h : lo + n ≤ m + 1) (x : Label m) :

    x ∈ FiniteIndependentPathGreedy.pathChosen (labelInterval m lo n h) ↔

      lo + 1 ≤ x.val ∧ x.val < lo + n ∧ x.val % 3 = (lo + 1) % 3

**Theorem 1.10 (tailWord_critical_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.tailWord_critical_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.tailWord_critical_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem tailWord_critical_formula (m : Nat) (hm : 3 ≤ m) :

    criticalFaces (tailWord m hm) =

      if m % 3 = 2 then ∅ else {tailCritical m hm}

**Theorem 1.11 (cycleWord_critical_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem cycleWord_critical_formula (m : Nat) (hm : 3 ≤ m) :

    criticalFaces (cycleWord m hm) =

      if m % 3 = 0 then {labelsCongruent m 2 2, labelsCongruent m 0 3}

      else if m % 3 = 1 then {labelsCongruent m 2 2}

      else {insert (lastLabel m) (labelsCongruent m 0 3)}

**Theorem 1.12 (cycleCritical_eq_complements).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleCritical_eq_complements`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleCritical_eq_complements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner.  cycleCritical is a dual target: every face on the right is complemented in the original fixed ground. Raw symbol criticals are given by cycleWord_critical_formula.

### Source text

theorem cycleCritical_eq_complements (m : Nat) (hm : 3 ≤ m) :

    cycleCritical m hm =

      (criticalFaces (cycleWord m hm)).image (fun s => ground m \ s)

At m=5, cycleWord_critical_formula specializes to the exact raw-critical equation below. The residues 5 % 3 = 2, together with insert (lastLabel 5) (labelsCongruent 5 0 3) = {3,5} on Label 5, give this application of the general theorem. This is mathematical exposition, with no separate exported declaration or canonical Describe. The positive raw critical equation and its negative control excluding the raw face {1,3} follow from the same general formula. These applications introduce no exported theorem.

## Source text

criticalFaces (cycleWord 5 (by omega)) =

      {({(⟨3, by omega⟩ : Label 5), (⟨5, by omega⟩ : Label 5)} : Finset (Label 5))}

**Theorem 1.13 (wheelRoot_mem_cycleDual).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.wheelRoot_mem_cycleDual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.wheelRoot_mem_cycleDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner. 

### Source text

theorem wheelRoot_mem_cycleDual (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :

    s ∈ wheelRoot m (by omega) ↔

      s ⊆ ground m ∧ ground m \ s ∉ cycleIndependentOn m hm

**Theorem 1.14 (cycleWord_wheelRoot_identity).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_wheelRoot_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_wheelRoot_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner.  This is an actual fixed-ground dual identity consumer. It does not construct a protected Contract, Sequence, Filling or Gamma endpoint.

### Source text

theorem cycleWord_wheelRoot_identity (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :

    s ∈ wheelRoot m (by omega) ↔ s ⊆ ground m ∧

      ¬ ∃ i : Fin (cycleWord m hm).length,

        ground m \ s ∈ ((cycleWord m hm).get i).faces

**Theorem 1.15 (cycleWord_rawDual_eq_wheelRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_rawDual_eq_wheelRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_rawDual_eq_wheelRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal SOURCE statement in namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel; proof body is in the source owner.  This is an actual fixed-ground dual identity consumer. It does not construct a protected Contract, Sequence, Filling or Gamma endpoint.

### Source text

theorem cycleWord_rawDual_eq_wheelRoot (m : Nat) (hm : 3 ≤ m) :

    rawDual (ground m) (facets (cycleIndependentOn m hm)) =

      wheelRoot m (by omega)

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleCritical_eq_complements`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_decomposition`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleIndependentOn_lower`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWordData_word`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_covers`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_blocks`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_critical_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_rawDual_eq_wheelRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.cycleWord_wheelRoot_identity`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.mem_cycleIndependentOn`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.pathChosen_labelInterval`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.tailWord_critical_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord.wheelRoot_mem_cycleDual`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel](../AllMWheel.md)
