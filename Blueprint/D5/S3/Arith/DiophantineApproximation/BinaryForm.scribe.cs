using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class BinaryFormDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An irrational complex root of a suitable integer polynomial has multiplicity below half its degree.",
        H("Binary Form"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-form"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/BinaryForm.two_mul_count_roots_lt_natDegree"),
            H("Binary Form"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("An irrational complex root of a suitable integer polynomial has multiplicity below half its degree."))),
            DescribeRole.Theorem))));
}
