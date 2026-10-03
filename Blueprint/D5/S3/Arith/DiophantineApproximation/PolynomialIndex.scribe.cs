using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class PolynomialIndexDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hasse derivative lowers a polynomial's weighted index by at most its derivative weight.",
        H("Polynomial Index"),
        Blocks(Describe.Lean(
            DescribeId.Create("polynomial-index"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/PolynomialIndex.index_le_hasseDeriv_add"),
            H("Polynomial Index"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A Hasse derivative lowers a polynomial's weighted index by at most its derivative weight."))),
            DescribeRole.Theorem))));
}
