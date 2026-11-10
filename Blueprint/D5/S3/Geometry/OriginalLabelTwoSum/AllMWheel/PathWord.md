# PathWordDocument

## Abstract

Ordered distinct paths give exhaustive raw P02 words with global dependencies.

The sole Symbol/Word/Contract/native Sequence authority is the selected repaired P02 owner. All eight Word fields, constructors and projections are inherited there unchanged. This document describes only concrete declarations present in this source owner. The cycle word, ghost-retaining fill0, every-residue fill1, Gamma criterion, B1/Q1, parent and physical constructions have separate contracts; an unrestricted arbitrary-plane supplier is not assumed. The source scopes below specify the lexical parameters.

**Definition 1.1 (Symbol).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Symbol`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Symbol := FiniteProtectedDualWord.Symbol

**Definition 1.2 (Word).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Word`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Word (W : Finset V) (K : Family V) := FiniteProtectedDualWord.Word W K

**Definition 1.3 (Contract).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Contract`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Contract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Contract (W : Finset V) (K : Family V) := FiniteProtectedDualWord.Contract W K

**Definition 1.4 (pathEdges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathEdges`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathEdges : List V → Finset (Finset V)

**Definition 1.5 (pathIndependent).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependent`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathIndependent (vertices : Finset V) (edges : Finset (Finset V)) :

    Finset (Finset V)

**Definition 1.6 (pathIndependentOn).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathIndependentOn (vertices : List V) : Finset (Finset V)

**Definition 1.7 (pathFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathFamily (vertices : List V) : Family V

**Theorem 1.8 (mem_pathIndependentOn).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathIndependentOn`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathIndependentOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_pathIndependentOn (vertices : List V) (s : Finset V) :

    s ∈ pathIndependentOn vertices ↔ s ⊆ vertices.toFinset ∧

      ∀ e ∈ pathEdges vertices, ¬ e ⊆ s

**Theorem 1.9 (pathIndependentOn_lower).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathIndependentOn_lower {vertices : List V} {s t : Finset V}

    (hs : s ∈ pathIndependentOn vertices) (hts : t ⊆ s) :

    t ∈ pathIndependentOn vertices

**Theorem 1.10 (mem_pathFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_pathFamily (vertices : List V) (s : Finset V) :

    s ∈ pathFamily vertices ↔ s ∈ pathIndependentOn vertices

**Theorem 1.11 (pathIndependentOn_eq_paths).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_eq_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_eq_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathIndependentOn_eq_paths (vertices : List V) (hd : vertices.Nodup) :

    pathIndependentOn vertices = FiniteIndependentPathGreedy.paths vertices

**Theorem 1.12 (pathIndependentOn_step).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_step`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathIndependentOn_step (a b : V) (rest : List V)

    (hd : (a :: b :: rest).Nodup) :

    pathIndependentOn (a :: b :: rest) =

      (pathIndependentOn rest ∪ (pathIndependentOn rest).image (insert a)) ∪

        (pathIndependentOn rest.tail).image (insert b)

**Definition 1.13 (faceBefore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.faceBefore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.faceBefore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def faceBefore (a b : Finset V) : Prop

**Definition 1.14 (orderedFaces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def orderedFaces (F : Finset (Finset V)) : List (Finset V)

**Theorem 1.15 (orderedFaces_spec).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem orderedFaces_spec (F : Finset (Finset V)) :

    (orderedFaces F).Nodup ∧ (orderedFaces F).toFinset = F ∧

      (orderedFaces F).Pairwise (fun a b => a.card ≤ b.card)

**Theorem 1.16 (mem_orderedFaces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_orderedFaces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_orderedFaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_orderedFaces (F : Finset (Finset V)) (s : Finset V) :

    s ∈ orderedFaces F ↔ s ∈ F

**Definition 1.17 (adjoinSymbol).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def adjoinSymbol (v : V) : Symbol V → Symbol V

**Theorem 1.18 (adjoinSymbol_pair).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem adjoinSymbol_pair (v a : V) (L : Finset V) :

    adjoinSymbol v (.pair L a) = .pair (insert v L) a

**Theorem 1.19 (adjoinSymbol_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem adjoinSymbol_critical (v : V) (S : Finset V) :

    adjoinSymbol v (.critical S) = .critical (insert v S)

**Theorem 1.20 (adjoinSymbol_faces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem adjoinSymbol_faces (v : V) (q : Symbol V) :

    (adjoinSymbol v q).faces = q.faces.image (insert v)

**Theorem 1.21 (mem_adjoinSymbol_faces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_adjoinSymbol_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_adjoinSymbol_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_adjoinSymbol_faces (v : V) (q : Symbol V) (s : Finset V) :

    s ∈ (adjoinSymbol v q).faces ↔ ∃ t ∈ q.faces, insert v t = s

**Definition 1.22 (pathWord).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathWord : List V → List (Symbol V)

**Definition 1.23 (pathCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathCritical`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathCritical (vertices : List V) : Finset (Finset V)

**Theorem 1.24 (pathWord_nil).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_nil`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_nil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pathWord_nil : pathWord ([] : List V) = [.critical ∅]

**Theorem 1.25 (pathWord_single).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_single`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pathWord_single (v : V) : pathWord [v] = [.pair ∅ v]

**Theorem 1.26 (pathWord_cons_cons).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_cons_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_cons_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pathWord_cons_cons (a b : V) (rest : List V) :

    pathWord (a :: b :: rest) =

      (orderedFaces (pathIndependentOn rest)).map (fun T => .pair T a) ++

        (pathWord rest.tail).map (adjoinSymbol b)

**Theorem 1.27 (pathWord_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pathWord_critical (vertices : List V) :

    criticalFaces (pathWord vertices) = pathCritical vertices

**Definition 1.28 (pathWordData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs all eight P02 Word fields from a distinct ordered path; the exact fourth-vertex suffix supplies the recursive Word. No desired output is a public input.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def pathWordData : (vertices : List V) → vertices.Nodup →

    Word vertices.toFinset (pathFamily vertices)

**Theorem 1.29 (pathWordData_word).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData_word`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pathWordData_word (vertices : List V) (hd : vertices.Nodup) :

    (pathWordData vertices hd).word = pathWord vertices

**Theorem 1.30 (duplicate_path_counterexample).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.duplicate_path_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.duplicate_path_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem duplicate_path_counterexample (v : V) :

    Symbol.pair ∅ v ∈ pathWord [v, v] ∧

      insert v (∅ : Finset V) ∉ pathFamily [v, v]

**Theorem 1.31 (criticalFaces_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.criticalFaces_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.criticalFaces_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem criticalFaces_mem (xs : List (Symbol V)) (S : Finset V) :

    S ∈ criticalFaces xs ↔ Symbol.critical S ∈ xs

**Theorem 1.32 (pathWord_critical_eq_selected).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_eq_selected`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_eq_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathWord_critical_eq_selected (vertices : List V) :

    criticalFaces (pathWord vertices) = FiniteIndependentPathGreedy.pathCritical vertices

**Theorem 1.33 (pathWord_critical_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathWord_critical_formula (vertices : List V) (hd : vertices.Nodup) :

    criticalFaces (pathWord vertices) =

      if vertices.length % 3 = 1 then ∅ else {FiniteIndependentPathGreedy.pathChosen vertices}

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Contract`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Symbol`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.Word`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_faces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.adjoinSymbol_pair`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.criticalFaces_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.duplicate_path_counterexample`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.faceBefore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_adjoinSymbol_faces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_orderedFaces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.mem_pathIndependentOn`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.orderedFaces_spec`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathCritical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathEdges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependent`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_eq_paths`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_lower`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathIndependentOn_step`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWordData_word`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_cons_cons`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_eq_selected`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_critical_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_nil`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord.pathWord_single`
- Dependency: [D5/S3/Geometry/FiniteIndependentPathGreedy](../../FiniteIndependentPathGreedy.md)
- Dependency: [D5/S3/Geometry/FiniteProtectedDualWord](../../FiniteProtectedDualWord.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Certificates](../Certificates.md)
