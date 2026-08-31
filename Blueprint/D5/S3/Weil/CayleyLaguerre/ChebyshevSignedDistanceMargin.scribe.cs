using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class ChebyshevSignedDistanceMarginDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceMargin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first off-line Chebyshev slack has an exact positive separation margin.",
        H("Chebyshev Signed-Distance Margin"),
        Blocks(Describe.Lean(
            DescribeId.Create("first-chebyshev-off-line-exact-margin"),
            DeclarationHandle.Create(
                Prefix + "first_chebyshev_off_line_exact_margin"),
            H("First Chebyshev Off-Line Exact Margin"),
            StatementSource.FromAuthor(MarginFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For positive delta with delta squared below the scale a, evaluating "
                        + "the first Chebyshev slack at the negative signed squared "
                        + "distance gives the negative of the displayed explicit margin.")),
                Paragraph(Text(
                    "The same hypotheses make that margin strictly positive. This is only "
                        + "a finite algebraic separation result; it makes no converse claim "
                        + "and asserts no connection to a xi spectrum."))),
            DescribeRole.Theorem))));

    private static Formula MarginFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("a");
        Formula delta = DeltaLower;
        Formula offLineCoordinate = new Formula.Subscript(F.Id("u"), F.Id("off"));
        Formula offLineSlack = new Formula.Subscript(F.Id("s"), F.Id("off"));
        Formula margin = F.Id("m");
        Formula deltaSquared = Seq(delta, Caret, Grp(D(2)));
        Formula coordinateValue = new Formula.Fraction(
            Seq(Minus, deltaSquared, Sp, Minus, Sp, a),
            Seq(Minus, deltaSquared, Sp, Plus, Sp, a));
        Formula chebyshevValue = Seq(
            F.Id("T"), Underscore, Grp(D(1)), Open, offLineCoordinate, Close);
        Formula slackValue = Seq(
            D(1), Sp, Minus, Sp, chebyshevValue, Caret, Grp(D(2)));
        Formula marginValue = new Formula.Fraction(
            Seq(D(4), Sp, Times, Sp, a, Sp, Times, Sp, deltaSquared),
            Seq(Open, a, Sp, Minus, Sp, deltaSquared, Close, Caret, Grp(D(2))));
        Formula premises = Seq(
            Open, D(0), Sp, Lt, Sp, delta, Close,
            Sp, Land, Sp,
            Open, deltaSquared, Sp, Lt, Sp, a, Close);
        Formula conclusion = Seq(
            Open,
            offLineSlack, Sp, Eq, Sp, Minus, margin,
            Sp, Land, Sp,
            D(0), Sp, Lt, Sp, margin,
            Close);

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, delta, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            premises, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            offLineCoordinate, Sp, Eq, Sp, coordinateValue, Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            offLineSlack, Sp, Eq, Sp, slackValue, Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            margin, Sp, Eq, Sp, marginValue, Comma,
            RowBreak, Grp(),
            conclusion, Dot));
    }
}
