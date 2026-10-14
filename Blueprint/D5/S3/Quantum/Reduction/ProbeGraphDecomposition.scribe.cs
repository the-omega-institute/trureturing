using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class ProbeGraphDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dimension bounds the number of orthogonal nonorthogonality components of an arbitrary unit probe family.",
        H("ProbeGraphDecomposition"),
        Blocks(
            Paragraph(Text("The family index type may be infinite. Taking the equivalence closure of nonzero overlaps defines its actual components. One representative from each component is an orthonormal family, hence a linearly independent family in the same finite Hilbert space. Finite dimensionality therefore proves that the component quotient is finite. Distinct component spans are orthogonal because an overlap between their generators would merge the classes. If the original family spans the space, their orthogonal spans exhaust it.")),
            Describe.Lean(
                DescribeId.Create("components-finite"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_finite"),
                H("components finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/mayerknill2018unitary")),
                Blocks(Paragraph(Text("The quotient of any family of unit probes by the nonorthogonality component relation is finite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("components-orthogonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_orthogonal"),
                H("components orthogonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/mayerknill2018unitary")),
                Blocks(Paragraph(Text("The actual Hilbert spans of distinct components are orthogonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("components-span"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_span"),
                H("components span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/mayerknill2018unitary")),
                Blocks(Paragraph(Text("When the original arbitrary probe family has full complex span, the supremum of its component Hilbert subspaces is the full space."))),
                DescribeRole.Theorem))));
}
