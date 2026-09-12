using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class TotalCopyNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict total copy trees normalize exactly and yield total native one-hole zero slices.",
        H("Total Native Copy Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-attributes"), DeclarationHandle.Create(Prefix + "sourceAttributeEquiv"),
                H("Position, sign, source and time"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Source timed attributes are in literal bijection with native attributes. The source sign is the integer one or minus one; the native sign is Boolean. Position is an integer triple, the source is a finite source tree, and time is any integer."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-signature"), DeclarationHandle.Create(Prefix + "nativeSignature"),
                H("All fixed native operations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The carrier is the complete balanced rich history in dimension three. Complement, every spatial set, every source-tree set, every timed-attribute set and every integer shift are unary operations. Ordered parallel, generated product and full-archive guarded temporal composition are binary operations. Every balanced parameter and both binary slots are available. A timed causal filter retains a selected event exactly when it is equal to or precedes a current target whose timed attribute lies in the fixed set. The target need not be selected. Filters preserve the entire Context."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("copy-syntax"), DeclarationHandle.Create(Prefix + "CopyTerm"),
                H("Finite syntax counts ordered input occurrences"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural-number index counts every input occurrence in left-to-right order. Closed subtrees have index zero. Unary nodes preserve the index and binary nodes add the two indices. All occurrences of the original tree receive the same history. Constants, sets, shifts and syntax are fixed before that history is chosen."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strict-totality"), DeclarationHandle.Create(Prefix + "DiagonalTotal"),
                H("Totality requires strict success on every shared input"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation returns an optional complete native value. A parent succeeds only when every child succeeds, including beneath complement, empty filters and either zero-factor slot. Diagonal totality quantifies over every balanced native history, with no depth or positive occurrence-count bound."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normal-form"), DeclarationHandle.Create(Prefix + "Normalizes"),
                H("Fold complete closed values and remove surviving temporal nodes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A closed subtree folds to its successful complete value. A positive-count unary node retains its operation. A positive-count binary node preserves both ordered children and changes temporal to parallel. Exact correctness uses old-event injections with the fixed integer shift of each occurrence path. Two input-bearing temporal children are obstructed by one shared inactive history with distinct events at minus L and plus L. A fixed nonempty opposite archive is obstructed by arbitrarily early or late inactive events. Each surviving temporal node therefore has a closed empty-archive side. Its temporal and parallel values are literally equal, retaining the same tags, attributes, causal relation, current region and selection."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word-reification"), DeclarationHandle.Create(Prefix + "wordToCopy"),
                H("Every Def16 word has exactly one input occurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite word uses the frozen one-hole Generator and strictStep interpreter. Reification folds the generators in execution order, wrapping the previous tree in the selected slot and placing the fixed parameter in the other slot. Its type is CopyTerm 1, including for the empty word. Its exact Option denotation is the frozen contextDenote."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("folded-slices"), DeclarationHandle.Create(Prefix + "foldedSlice"),
                H("Compile each independent occurrence into a fixed word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occurrence path retains one input. Every sibling subtree folds to its successful complete value at the actual empty history balancedSection 3 0. The slice is a fixed temporal-free word whose reification is this exact folded tree. Independent evaluation assigns an arbitrary history to the chosen occurrence and the empty history to every other occurrence."))), DescribeRole.Definition),
            /* The adjacent anonymous Lean derivation has no public declaration anchor.
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
            */
            Describe.Lean(
                DescribeId.Create("normalization"), DeclarationHandle.Create(Prefix + "total_copy_normalization"),
                H("Full exact normalization and all zero slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite positive-count diagonally total copy tree admits a temporal-free normal tree with the same ordered occurrences and exactly the same diagonal Option denotation. The normal tree succeeds for every independent assignment. Every occurrence has a fixed temporal-free Def16 word, exact folded-tree reification, exact independent slice denotation and total evaluation on every input. The common zero has empty archive, current region and selection. There is one complete value Z of the original tree at zero, and every slice at zero is literally that same Z. Z itself may have a nonempty archive. Applying the theorem to wordToCopy of any total Def16 word gives a total temporal-free word with exactly the same denotation on every input, including the common zero value.")),
                    Paragraph(Text("Exact anonymous Def16 derivation using the private bridge in this owner:")),
                    Paragraph(Text("```lean")),
                    Paragraph(Text("example (w : List (Generator nativeSignature))")),
                    Paragraph(Text("    (ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :")),
                    Paragraph(Text("    ∃ w' : List (Generator nativeSignature), WordTemporalFree w' ∧")),
                    Paragraph(Text("      (∀ X, contextDenote nativeSignature w X = contextDenote nativeSignature w' X) ∧")),
                    Paragraph(Text("      (∀ X, ∃ Y, contextDenote nativeSignature w' X = some Y) ∧")),
                    Paragraph(Text("      (∃ Z, contextDenote nativeSignature w zero = some Z ∧")),
                    Paragraph(Text("        contextDenote nativeSignature w' zero = some Z) := by")),
                    Paragraph(Text("  have hc : DiagonalTotal (wordToCopy w) := by")),
                    Paragraph(Text("    intro X")),
                    Paragraph(Text("    simpa only [word_to_copy_denote] using ht X")),
                    Paragraph(Text("  obtain ⟨_, _, _, N, _, _, he, _, ws, hw, hd, hs, Z, hz, hz'⟩ :=")),
                    Paragraph(Text("    total_copy_normalization (wordToCopy w) (by decide) hc")),
                    Paragraph(Text("  refine ⟨ws 0, (hw 0).1, fun X => ?_, hs 0, Z, ?_, hz' 0⟩")),
                    Paragraph(Text("  · have hv : sliceAssignment (0 : Fin 1) X = fun _ => X := by")),
                    Paragraph(Text("      funext j; have hj : j = 0 := Subsingleton.elim _ _; subst j; rfl")),
                    Paragraph(Text("    rw [hd, hv]")),
                    Paragraph(Text("    exact (word_to_copy_denote w X).symm.trans (he X)")),
                    Paragraph(Text("  · simpa only [word_to_copy_denote] using hz")),
                    Paragraph(Text("```"))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComposition")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementFibers")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts"))
        ]));
}
