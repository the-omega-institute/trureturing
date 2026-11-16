using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SixBitData;

internal sealed class ExtensionGroups84To88Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact extension data for the six-bit orthogonality catalogue.",
        H("Supplied adjoining-vector dispatch groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("extension-group-84"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups84To88.extensionsGroup84"),
                H("Extension dispatch group 84"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 84. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-85"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups84To88.extensionsGroup85"),
                H("Extension dispatch group 85"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 85. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-86"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups84To88.extensionsGroup86"),
                H("Extension dispatch group 86"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 86. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-87"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups84To88.extensionsGroup87"),
                H("Extension dispatch group 87"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 87. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-88"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups84To88.extensionsGroup88"),
                H("Extension dispatch group 88"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 88. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogue"))]));
}
