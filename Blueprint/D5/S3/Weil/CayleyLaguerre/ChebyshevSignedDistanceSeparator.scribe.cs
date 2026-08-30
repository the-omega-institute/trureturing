using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class ChebyshevSignedDistanceSeparatorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First Chebyshev slack separates nonnegative and negative squared distances.",
        H("Chebyshev Signed-Distance Separator"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "first-chebyshev-slack-separates-signed-squared-distance"),
            DeclarationHandle.Create(
                Prefix + "first_chebyshev_slack_separates_signed_squared_distance"),
            H("First Chebyshev Slack Separates Signed Squared Distance"),
            StatementSource.FromAuthor(SeparatorFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Above the stated scale thresholds, a nonnegative squared-distance "
                        + "input has compact coordinate in the closed unit interval and "
                        + "first Chebyshev slack in the interval from zero to one. The "
                        + "negative signed value has coordinate below negative one and "
                        + "strictly negative slack.")),
                Paragraph(Text(
                    "This is only a finite algebraic separator under the four explicit "
                        + "hypotheses. It makes no converse claim and does not claim that "
                        + "a xi spectrum supplies the signed-distance observation."))),
            DescribeRole.Theorem))));

    private static Formula SeparatorFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula delta = DeltaLower;
        Formula onLineCoordinate = new Formula.Subscript(F.Id("u"), F.Id("on"));
        Formula onLineSlack = new Formula.Subscript(F.Id("s"), F.Id("on"));
        Formula offLineCoordinate = new Formula.Subscript(F.Id("u"), F.Id("off"));
        Formula offLineSlack = new Formula.Subscript(F.Id("s"), F.Id("off"));
        Formula deltaSquared = Seq(delta, Caret, Grp(D(2)));
        Formula onLineCoordinateValue = Fraction(
            Seq(x, Sp, Minus, Sp, a),
            Seq(x, Sp, Plus, Sp, a));
        Formula offLineCoordinateValue = Fraction(
            Seq(Minus, deltaSquared, Sp, Minus, Sp, a),
            Seq(Minus, deltaSquared, Sp, Plus, Sp, a));
        Formula onLineSlackValue = Seq(
            D(1), Sp, Minus, Sp,
            ChebyshevOne(onLineCoordinate), Caret, Grp(D(2)));
        Formula offLineSlackValue = Seq(
            D(1), Sp, Minus, Sp,
            ChebyshevOne(offLineCoordinate), Caret, Grp(D(2)));
        Formula premises = Seq(
            Open, Fraction(D(1), D(4)), Sp, Lt, Sp, a, Close,
            Sp, Land, Sp,
            Open, D(0), Sp, Leq, Sp, x, Close,
            Sp, Land, Sp,
            Open, D(0), Sp, Lt, Sp, delta, Close,
            Sp, Land, Sp,
            Open, deltaSquared, Sp, Lt, Sp, a, Close);
        Formula conclusions = Seq(
            Open,
            Open, onLineCoordinate, Sp, InMacro, Sp, Interval(
                Seq(Minus, D(1)), D(1)), Close,
            Sp, Land, RowBreak, Grp(),
            Open, onLineSlack, Sp, InMacro, Sp, Interval(D(0), D(1)), Close,
            Sp, Land, RowBreak, Grp(),
            Open, offLineCoordinate, Sp, Lt, Sp, Minus, D(1), Close,
            Sp, Land, RowBreak, Grp(),
            Open, offLineSlack, Sp, Lt, Sp, D(0), Close,
            Close);

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, x, Comma, Sp, delta,
            Colon, Sp, real, Comma, RowBreak, Grp(),
            premises, Sp, Rightarrow, RowBreak, Grp(),
            Let(onLineCoordinate, onLineCoordinateValue), RowBreak, Grp(),
            Let(onLineSlack, onLineSlackValue), RowBreak, Grp(),
            Let(offLineCoordinate, offLineCoordinateValue), RowBreak, Grp(),
            Let(offLineSlack, offLineSlackValue), RowBreak, Grp(),
            conclusions, Dot));
    }

    private static Formula ChebyshevOne(Formula value) =>
        Seq(F.Id("T"), Underscore, Grp(D(1)), Open, value, Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Interval(Formula lower, Formula upper) =>
        Seq(OpenBracket, lower, Comma, Sp, upper, CloseBracket);

    private static Formula Let(Formula name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp,
            name, Sp, Eq, Sp, value, Comma);
}
