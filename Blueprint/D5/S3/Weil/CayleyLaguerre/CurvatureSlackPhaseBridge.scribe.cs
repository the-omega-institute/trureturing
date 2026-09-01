using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class CurvatureSlackPhaseBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/CayleyLaguerre/CurvatureSlackPhaseBridge."
            + "curvature_slack_phase_bridge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized curvature is the compact coordinate; degree-one slack is its "
            + "complementary square and reciprocal inputs reverse its phase.",
        H("Curvature-Slack Phase Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("curvature-slack-phase-bridge"),
            DeclarationHandle.Create(Declaration),
            H("Curvature, slack, and reciprocal phase"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The coordinate, curvature scalar, and degree-one Chebyshev slack "
                        + "are constructed from a positive scale and nonnegative input.")),
                Paragraph(Text(
                    "Normalization recovers the coordinate and gives a unit sum with "
                        + "slack. For a strictly positive input below the scale, the "
                        + "reciprocal coordinate is its negative, so slack is unchanged "
                        + "while the two coordinate signs are opposite."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula kappa = Kappa;
        Formula slack = F.Id("s");
        Formula y = F.Id("y");
        Formula coordinate = Fraction(
            Seq(x, Sp, Minus, Sp, a),
            Seq(x, Sp, Plus, Sp, a));
        Formula kappaValue = Fraction(
            Seq(D(2), Sp, Cdot, Sp, Open, x, Sp, Minus, Sp, a, Close),
            Seq(Open, x, Sp, Plus, Sp, a, Close, Caret, Grp(D(2))));
        Formula slackValue = Seq(
            D(1), Sp, Minus, Sp,
            ChebyshevOne(z), Caret, Grp(D(2)));
        Formula normalized = Fraction(
            Seq(Open, x, Sp, Plus, Sp, a, Close, Sp, Cdot, Sp, kappa),
            D(2));
        Formula reciprocalValue = Fraction(
            Seq(a, Caret, Grp(D(2))), x);
        Formula reciprocalCoordinate = Fraction(
            Seq(y, Sp, Minus, Sp, a),
            Seq(y, Sp, Plus, Sp, a));
        Formula mainConclusions = Seq(
            Open, normalized, Caret, Grp(D(2)), Sp, Plus, Sp, slack,
            Sp, Eq, Sp, D(1), Close,
            Sp, Land, RowBreak, Grp(),
            Open, normalized, Sp, Eq, Sp, z, Close);
        Formula phaseConclusions = Seq(
            Open, reciprocalCoordinate, Sp, Eq, Sp, Minus, z, Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            D(1), Sp, Minus, Sp,
            ChebyshevOne(reciprocalCoordinate), Caret, Grp(D(2)),
            Sp, Eq, Sp, slack, Close,
            Sp, Land, RowBreak, Grp(),
            Open, z, Sp, Lt, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Open, D(0), Sp, Lt, Sp, reciprocalCoordinate, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Comma, Sp, x, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            Open, D(0), Sp, Lt, Sp, a, Close,
            Sp, Land, Sp,
            Open, D(0), Sp, Leq, Sp, x, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Let(z, coordinate),
            Let(kappa, kappaValue),
            Let(slack, slackValue),
            mainConclusions,
            Sp, Land, RowBreak, Grp(),
            Open,
            Open, D(0), Sp, Lt, Sp, x, Sp, Lt, Sp, a, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Let(y, reciprocalValue),
            phaseConclusions,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ChebyshevOne(Formula value) =>
        Seq(F.Id("T"), Underscore, Grp(D(1)), Open, value, Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Let(Formula name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp,
            name, Sp, Eq, Sp, value, Semi, Sp);
}
