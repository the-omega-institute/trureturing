using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenHorizonMatchingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenHorizonMatching.golden_horizon_matching";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-one horizon channel laws make seven golden matching conditions equivalent.",
        H("Golden Horizon Matching"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-horizon-matching"),
            DeclarationHandle.Create(Declaration),
            H("Seven golden horizon conditions are equivalent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The external channel laws identify the horizon index with the inverse "
                        + "complement of the sampling square, the sampling ratio with omega "
                        + "over delta, the two squared amplitudes with successive index "
                        + "values, and the entropy cost with the logarithm of the index.")),
                Paragraph(Text(
                    "Strict positivity of delta, nonnegativity of omega, and strict "
                        + "contractivity exclude division by zero, the negative square-root "
                        + "branch, and the singular horizon boundary.")),
                Paragraph(Text(
                    "Under those laws, the golden horizon index, complementary transmission, "
                        + "sampling square, squared amplitudes, logarithmic cost, and positive "
                        + "sampling ratio are seven equivalent descriptions of one channel."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula horizon = F.Id("H");
        Formula sigma = F.Id("sigma");
        Formula alphaSq = F.Id("alphaSq");
        Formula betaSq = F.Id("betaSq");
        Formula entropy = F.Id("K");
        Formula omega = F.Id("omega");
        Formula delta = F.Id("delta");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula phi = Varphi;

        Formula sigmaSq = Pow(sigma, D(2));
        Formula phiSq = Pow(phi, D(2));
        Formula phiInv = Pow(phi, Seq(Minus, D(1)));
        Formula horizonLaw = Equal(
            horizon,
            Pow(Grp(D(1), Sp, Minus, Sp, sigmaSq), Seq(Minus, D(1))));
        Formula samplingLaw = Equal(sigma, Divide(omega, delta));
        Formula assumptions = All(
            Seq(D(0), Sp, Lt, Sp, delta),
            Seq(D(0), Sp, Leq, Sp, omega),
            Seq(omega, Sp, Lt, Sp, delta),
            horizonLaw,
            samplingLaw,
            Equal(alphaSq, horizon),
            Equal(betaSq, Seq(alphaSq, Sp, Minus, Sp, D(1))),
            Equal(entropy, Call("log", horizon)));
        Formula clauses = Grp(
            OpenBracket,
            Equal(horizon, phiSq), Comma, Sp,
            Equal(
                Seq(D(1), Sp, Minus, Sp, sigmaSq),
                Pow(Grp(phiSq), Seq(Minus, D(1)))),
            Comma, Sp,
            Equal(sigmaSq, phiInv), Comma, Sp,
            Equal(alphaSq, phiSq), Comma, Sp,
            Equal(betaSq, phi), Comma, Sp,
            Equal(entropy, Seq(D(2), Sp, Call("log", phi))), Comma, Sp,
            Equal(Divide(omega, delta), Call("sqrt", phiInv)),
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            horizon, Comma, Sp, sigma, Comma, Sp, alphaSq, Comma, Sp,
            betaSq, Comma, Sp, entropy, Comma, Sp, omega, Comma, Sp, delta,
            Sp, InMacro, Sp, real, Comma, RowBreak, Grp(),
            assumptions, Sp, Rightarrow, RowBreak, Grp(),
            Call("ListTFAE", clauses), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);

    private static Formula Pow(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Divide(Formula numerator, Formula denominator) =>
        Seq(numerator, Sp, Slash, Sp, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
