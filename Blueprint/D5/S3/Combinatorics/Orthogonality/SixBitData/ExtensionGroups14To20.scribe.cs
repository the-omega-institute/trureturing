using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SixBitData;

internal sealed class ExtensionGroups14To20Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact extension data for the six-bit orthogonality catalogue.",
        H("Supplied adjoining-vector dispatch groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("extension-group-14"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup14"),
                H("Extension dispatch group 14"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 14. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-15"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup15"),
                H("Extension dispatch group 15"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 15. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-16"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup16"),
                H("Extension dispatch group 16"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 16. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-17"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup17"),
                H("Extension dispatch group 17"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 17. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-18"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup18"),
                H("Extension dispatch group 18"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 18. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-19"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup19"),
                H("Extension dispatch group 19"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 19. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extension-group-20"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitData/ExtensionGroups14To20.extensionsGroup20"),
                H("Extension dispatch group 20"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact supplied adjoining-vector table on catalogue dispatch group 20. This definition supplies the original extensions function used by dimensionSix; it does not assert correctness of the table."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogue"))]));
}
