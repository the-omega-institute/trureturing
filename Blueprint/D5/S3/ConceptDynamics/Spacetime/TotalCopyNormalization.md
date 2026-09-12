# Total Native Copy Normalization

## Abstract

Strict total copy trees normalize exactly and yield total native one-hole zero slices.

**Definition 1.1 (Position, sign, source and time).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.sourceAttributeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.sourceAttributeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source timed attributes are in literal bijection with native attributes. The source sign is the integer one or minus one; the native sign is Boolean. Position is an integer triple, the source is a finite source tree, and time is any integer.

**Definition 1.2 (All fixed native operations).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.nativeSignature`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.nativeSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the complete balanced rich history in dimension three. Complement, every spatial set, every source-tree set, every timed-attribute set and every integer shift are unary operations. Ordered parallel, generated product and full-archive guarded temporal composition are binary operations. Every balanced parameter and both binary slots are available. A timed causal filter retains a selected event exactly when it is equal to or precedes a current target whose timed attribute lies in the fixed set. The target need not be selected. Filters preserve the entire Context.

**Definition 1.3 (Finite syntax counts ordered input occurrences).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.CopyTerm`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.CopyTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural-number index counts every input occurrence in left-to-right order. Closed subtrees have index zero. Unary nodes preserve the index and binary nodes add the two indices. All occurrences of the original tree receive the same history. Constants, sets, shifts and syntax are fixed before that history is chosen.

**Definition 1.4 (Totality requires strict success on every shared input).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.DiagonalTotal`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.DiagonalTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation returns an optional complete native value. A parent succeeds only when every child succeeds, including beneath complement, empty filters and either zero-factor slot. Diagonal totality quantifies over every balanced native history, with no depth or positive occurrence-count bound.

**Definition 1.5 (Fold complete closed values and remove surviving temporal nodes).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.Normalizes`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.Normalizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A closed subtree folds to its successful complete value. A positive-count unary node retains its operation. A positive-count binary node preserves both ordered children and changes temporal to parallel. Exact correctness uses old-event injections with the fixed integer shift of each occurrence path. Two input-bearing temporal children are obstructed by one shared inactive history with distinct events at minus L and plus L. A fixed nonempty opposite archive is obstructed by arbitrarily early or late inactive events. Each surviving temporal node therefore has a closed empty-archive side. Its temporal and parallel values are literally equal, retaining the same tags, attributes, causal relation, current region and selection.

**Definition 1.6 (Every Def16 word has exactly one input occurrence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.wordToCopy`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.wordToCopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite word uses the frozen one-hole Generator and strictStep interpreter. Reification folds the generators in execution order, wrapping the previous tree in the selected slot and placing the fixed parameter in the other slot. Its type is CopyTerm 1, including for the empty word. Its exact Option denotation is the frozen contextDenote.

**Definition 1.7 (Compile each independent occurrence into a fixed word).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.foldedSlice`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.foldedSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The occurrence path retains one input. Every sibling subtree folds to its successful complete value at the actual empty history balancedSection 3 0. The slice is a fixed temporal-free word whose reification is this exact folded tree. Independent evaluation assigns an arbitrary history to the chosen occurrence and the empty history to every other occurrence.

**Theorem 1.8 (Full exact normalization and all zero slices).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.total_copy_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.total_copy_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite positive-count diagonally total copy tree admits a temporal-free normal tree with the same ordered occurrences and exactly the same diagonal Option denotation. The normal tree succeeds for every independent assignment. Every occurrence has a fixed temporal-free Def16 word, exact folded-tree reification, exact independent slice denotation and total evaluation on every input. The common zero has empty archive, current region and selection. There is one complete value Z of the original tree at zero, and every slice at zero is literally that same Z. Z itself may have a nonempty archive. Applying the theorem to wordToCopy of any total Def16 word gives a total temporal-free word with exactly the same denotation on every input, including the common zero value.

Exact anonymous Def16 derivation using the private bridge in this owner:

```lean

example (w : List (Generator nativeSignature))

    (ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :

    ∃ w' : List (Generator nativeSignature), WordTemporalFree w' ∧

      (∀ X, contextDenote nativeSignature w X = contextDenote nativeSignature w' X) ∧

      (∀ X, ∃ Y, contextDenote nativeSignature w' X = some Y) ∧

      (∃ Z, contextDenote nativeSignature w zero = some Z ∧

        contextDenote nativeSignature w' zero = some Z) := by

  have hc : DiagonalTotal (wordToCopy w) := by

    intro X

    simpa only [word_to_copy_denote] using ht X

  obtain ⟨_, _, _, N, _, _, he, _, ws, hw, hd, hs, Z, hz, hz'⟩ :=

    total_copy_normalization (wordToCopy w) (by decide) hc

  refine ⟨ws 0, (hw 0).1, fun X => ?_, hs 0, Z, ?_, hz' 0⟩

  · have hv : sliceAssignment (0 : Fin 1) X = fun _ => X := by

      funext j; have hj : j = 0 := Subsingleton.elim _ _; subst j; rfl

    rw [hd, hv]

    exact (word_to_copy_denote w X).symm.trans (he X)

  · simpa only [word_to_copy_denote] using hz

```

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.CopyTerm`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.DiagonalTotal`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.Normalizes`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.foldedSlice`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.nativeSignature`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.sourceAttributeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.total_copy_normalization`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.wordToCopy`
- Dependency: [D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts](../Observation/StrictOneHoleContexts.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementFibers](ComplementFibers.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout](LeafSquareReadout.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TemporalComposition](TemporalComposition.md)
