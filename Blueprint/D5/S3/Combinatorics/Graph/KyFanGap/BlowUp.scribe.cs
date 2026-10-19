using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class BlowUpDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blow-up matrices and normalized graph maxima.",
        H("Blow-up interface"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blow-up-matrix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.blowUpMatrix"),
                H("Independent-class blow-up matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The Kronecker product with an all-one block records the independent-class blow-up."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-supremum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.normalizedSupremum"),
                H("Normalized supremum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The supremum records the normalized finite graph maxima."))),
                DescribeRole.Definition))));
}
