using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class CayleyScaleChangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Budget/CayleyScaleChange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Cayley scales are related by an explicit real-parameter disk automorphism.",
        H("Cayley Scale Change"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scaled-cayley-coordinate"),
                DeclarationHandle.Create(Prefix + "cayleyCoordinate"),
                H("Scaled Cayley coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Cayley(F.Id("a")), Open, Xi, Close, Sp, Eq, Sp,
                    Fraction(
                        Seq(Xi, Sp, Plus, Sp, F.Id("i"), F.Id("a")),
                        Seq(Xi, Sp, Minus, Sp, F.Id("i"), F.Id("a"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate is constructed directly from a real spectral point and "
                        + "a real scale, with values in the complex plane."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-scale-parameter"),
                DeclarationHandle.Create(Prefix + "scaleChangeParameter"),
                H("Hyperbolic scale parameter"),
                StatementSource.FromAuthor(Disp(Seq(
                    ScaleParameter(), Sp, Eq, Sp,
                    Fraction(
                        Seq(F.Id("a"), Sp, Minus, Sp, F.Id("b")),
                        Seq(F.Id("a"), Sp, Plus, Sp, F.Id("b"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive-scale hypotheses make the denominator nonzero and place "
                        + "this parameter between minus one and one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-disk-automorphism"),
                DeclarationHandle.Create(Prefix + "realDiskAutomorphism"),
                H("Real disk automorphism"),
                StatementSource.FromAuthor(Disp(Seq(
                    Phi(Open, F.Id("r"), Close, Open, F.Id("z"), Close), Sp, Eq, Sp,
                    Fraction(
                        Seq(F.Id("z"), Sp, Plus, Sp, F.Id("r")),
                        Seq(D(1), Sp, Plus, Sp, F.Id("r"), F.Id("z"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the source's Mobius action with a real parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-cayley-scale-change"),
                DeclarationHandle.Create(Prefix + "cayley_scale_change"),
                H("Cayley scale-change law"),
                StatementSource.FromAuthor(ScaleChangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof clears only denominators forced nonzero by the two positive "
                        + "scales and then verifies the source's rational identity."))),
                DescribeRole.Theorem))));

    private static Formula ScaleChangeFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, Xi, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, a, Sp, Land, Sp, D(0), Sp, Lt, Sp, b,
            Sp, Rightarrow, RowBreak, Grp(),
            Cayley(b), Open, Xi, Close, Sp, Eq, Sp,
            Phi(Open, ScaleParameter(), Close,
                Open, Cayley(a), Open, Xi, Close, Close), Dot));
    }

    private static Formula Cayley(Formula scale) =>
        new Formula.Subscript(F.Id("c"), scale);

    private static Formula ScaleParameter() =>
        new Formula.Subscript(F.Id("r"), Seq(F.Id("a"), Comma, F.Id("b")));

    private static Formula Phi(params Formula[] arguments)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(F.Id("Phi"))) };
        items.AddRange(arguments);
        return Seq(items.ToArray());
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
}
