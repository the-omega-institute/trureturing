using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SixBitData;

internal sealed class ExtensionGroups00To06Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact extension data for the six-bit orthogonality catalogue.",
        H("Supplied adjoining-vector dispatch groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("extension-group-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup0"),
                H("Extension dispatch group 0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 0. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup1"),
                H("Extension dispatch group 1"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 1. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup2"),
                H("Extension dispatch group 2"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 2. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup3"),
                H("Extension dispatch group 3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 3. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup4"),
                H("Extension dispatch group 4"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 4. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup5"),
                H("Extension dispatch group 5"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 5. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-6"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups00To06.extensionsGroup6"),
                H("Extension dispatch group 6"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 6. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogue"))]));
}
