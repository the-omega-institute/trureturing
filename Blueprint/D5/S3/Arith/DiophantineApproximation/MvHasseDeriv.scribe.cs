using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class MvHasseDerivDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multivariate Hasse derivative acts on monomials by binomial coefficients.",
        H("Mv Hasse Deriv"),
        Blocks(Describe.Lean(
            DescribeId.Create("mv-hasse-deriv"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/MvHasseDeriv.hasseDeriv"),
            H("Mv Hasse Deriv"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The multivariate Hasse derivative acts on monomials by binomial coefficients."))),
            DescribeRole.Definition))));
}
