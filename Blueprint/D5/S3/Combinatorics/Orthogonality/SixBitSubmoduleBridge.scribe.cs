using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitSubmoduleBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional source representation and certificate.",
        H("Complete source objects and retained trust boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("exact-low-bits"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.bits"),
                H("exact low bits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Coordinate i is precisely the ith low bit of the integer mask. All six coordinates are retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-vector-space-equivalence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vectorLinearEquiv"),
                H("actual vector space equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The mask wrapper carries the binary vector-space operations transported by the actual low-bit bijection. Its addition agrees with source XOR, as checked separately; it is not arithmetic modulo 64."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-space-lattice-equivalence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.spaceEquiv"),
                H("complete space lattice equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Every zero-containing XOR-closed finite mask set corresponds to exactly its image Submodule, and every actual coordinate submodule is obtained. Scalar closure is proved for both binary scalars."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonzero-space-equivalence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vertexEquiv"),
                H("nonzero space equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The source zero space {0} corresponds exactly to bottom. Thus all nonzero spaces, including top, correspond in both directions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-orthogonality-graph-isomorphism"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.graphIso"),
                H("full orthogonality graph isomorphism"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact low-bit dot-zero equivalence proves the source and actual Submodule graphs are isomorphic, preserving distinctness and every cross pairing. Transferring the supplied chromatic theorem remains a transient exact application, not a duplicated public theorem."))), DescribeRole.Definition)),
        []));
}
