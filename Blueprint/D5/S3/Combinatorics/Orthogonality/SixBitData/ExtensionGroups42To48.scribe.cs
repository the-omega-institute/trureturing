using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SixBitData;

internal sealed class ExtensionGroups42To48Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact extension data for the six-bit orthogonality catalogue.",
        H("Supplied adjoining-vector dispatch groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("extension-group-42"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup42"),
                H("Extension dispatch group 42"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 42. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-43"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup43"),
                H("Extension dispatch group 43"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 43. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-44"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup44"),
                H("Extension dispatch group 44"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 44. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-45"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup45"),
                H("Extension dispatch group 45"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 45. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-46"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup46"),
                H("Extension dispatch group 46"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 46. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-47"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup47"),
                H("Extension dispatch group 47"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 47. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-48"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups42To48.extensionsGroup48"),
                H("Extension dispatch group 48"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 48. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogue"))]));
}
