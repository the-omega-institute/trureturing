using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Coefficients;

internal sealed class PositivePairsCoefficientsMagnusWordCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Magnus coefficients equal scattered-subword multiplicities.",
        H("MagnusWordCoefficients"),
        Blocks(
            Paragraph(Text(
                "Magnus expansions and shuffle or infiltration identities are classical context, "
                + "but the complete recursively indexed positive-pair construction below is a "
                + "repository route. Indices are retained even when two evaluated pairs coincide.")),
            D("magnus-polynomial", "magnusPolynomial", "Actual positive-word Magnus polynomial",
                "magnusPolynomial []=1 and magnusPolynomial (a::w)=(1+X_a)*magnusPolynomial w, preserving source order.", DescribeRole.Definition, true),
            D("magnus-coeff-scattered-count", "magnusPolynomial_coeff_scatteredCount", "Magnus coefficients are scattered counts",
                "With decidable equality on A, the coefficient at pattern in magnusPolynomial source is exactly the natural scatteredCount pattern source, cast to Z.", literature: true),
            D("word-abelianization", "wordAbelianization", "Degree-one letter sum",
                "wordAbelianization recursively sums the singleton wordMonomial for each source letter and maps the empty word to zero.", DescribeRole.Definition),
            D("word-abelianization-singleton", "wordAbelianization_coeff_singleton", "Singleton coefficients count letters",
                "With decidable equality, the coefficient of [b] in wordAbelianization source is scatteredCount [b] source, cast to Z."),
            D("word-abelianization-empty", "wordAbelianization_coeff_empty", "No empty coefficient",
                "For every source, wordAbelianization source has coefficient zero at the empty free word."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "magnusPolynomial" => Seq(Forall, Sp, F.Id("w"), Comma, Sp,
            Equal(Call("magnusPolynomial", F.Id("w")),
                Call("orderedProd", F.Id("w"), Call("lambda", F.Id("a"),
                    Add(Num(1), Call("wordMonomial",
                        Call("singleton", F.Id("a")))))))),
        "magnusPolynomial_coeff_scatteredCount" => Seq(Forall, Sp,
            F.Id("source"), Comma, Sp, F.Id("pattern"), Comma, Sp,
            Equal(Call("coeff", Call("magnusPolynomial", F.Id("source")),
                    Call("ofList", F.Id("pattern"))),
                Call("scatteredCount", F.Id("pattern"), F.Id("source")))),
        "wordAbelianization" => Seq(Forall, Sp, F.Id("w"), Comma, Sp,
            Equal(Call("wordAbelianization", F.Id("w")),
                Call("sum", F.Id("w"), Call("lambda", F.Id("a"),
                    Call("wordMonomial", Call("singleton", F.Id("a"))))))),
        "wordAbelianization_coeff_singleton" => Seq(Forall, Sp,
            F.Id("source"), Comma, Sp, F.Id("b"), Comma, Sp,
            Equal(Call("coeff", Call("wordAbelianization", F.Id("source")),
                    Call("ofList", Call("singleton", F.Id("b")))),
                Call("scatteredCount", Call("singleton", F.Id("b")),
                    F.Id("source")))),
        "wordAbelianization_coeff_empty" => Seq(Forall, Sp, F.Id("source"),
            Comma, Sp, Equal(Call("coeff", Call("wordAbelianization", F.Id("source")),
                Num(1)), Num(0))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
