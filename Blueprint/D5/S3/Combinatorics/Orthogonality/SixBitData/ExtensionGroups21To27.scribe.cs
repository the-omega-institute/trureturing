using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SixBitData;

internal sealed class ExtensionGroups21To27Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact extension data for the six-bit orthogonality catalogue.",
        H("Supplied adjoining-vector dispatch groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("extension-group-21"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup21"),
                H("Extension dispatch group 21"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 21. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-22"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup22"),
                H("Extension dispatch group 22"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 22. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-23"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup23"),
                H("Extension dispatch group 23"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 23. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-24"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup24"),
                H("Extension dispatch group 24"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 24. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-25"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup25"),
                H("Extension dispatch group 25"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 25. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-26"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup26"),
                H("Extension dispatch group 26"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 26. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-27"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups21To27.extensionsGroup27"),
                H("Extension dispatch group 27"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 27. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogue"))]));
}
