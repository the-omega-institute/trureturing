using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class BoxMonomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A multivariate polynomial's coefficient box controls its absolute multiplicative height.",
        H("Box Monomial"),
        Blocks(Describe.Lean(
            DescribeId.Create("box-monomial"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/BoxMonomial.absMulHeight_coeff_box"),
            H("Box Monomial"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A multivariate polynomial's coefficient box controls its absolute multiplicative height."))),
            DescribeRole.Theorem))));
}
