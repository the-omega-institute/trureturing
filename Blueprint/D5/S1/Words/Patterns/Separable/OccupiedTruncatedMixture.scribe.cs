using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedTruncatedMixtureDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Parens(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula C => F.Id("c");
    private static Formula N => F.Id("n");
    private static Formula X => F.Id("X");
    private static Formula Z => F.Id("z");
    private static Formula IntDomain => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(Ratio(D(1), D(4))));
    private static Formula Log(Formula x) => Seq(F.Log, Sp, x);
    private static Formula Profile => Seq(F.Id("p"), Underscore, Grp(Ratio(D(1), D(2)), Plus, F.Id("s")));
    private static Formula Generator(Formula u, Formula z) => Seq(
        Mathcal, Grp(F.Id("D")), Underscore, Grp(Kappa), Parens(Seq(u, Comma, z)));
    private static Formula Gain => Seq(
        Ratio(C, Seq(N, Cdot, Sp, Pow(Parens(Log(N)), D(2)))), Le, Sp, Generator(Tau, N));

    private static Formula Analysis() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Open, Forall, Sp, Z, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, RowBreak, Grp(),
        Generator(Tau, Z), Eq, IntDomain, Generator(Profile, Z), Thin, F.Id("ds"), Sp, Land, RowBreak, Grp(),
        Tau, Open, Z, Close, Eq,
        Ratio(Seq(D(1), Minus, Pow(X, Seq(Minus, Ratio(D(1), D(4))))),
            Seq(Sqrt, Grp(X), Cdot, Log(X))), Close, Sp, Land, RowBreak, Grp(),
        Open, Exists, Sp, C, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, D(0), Lt, C, Sp, Land, Sp,
        Operatorname, Grp(F.Id("Eventually")), Underscore, Grp(N, To, Infty), Parens(Gain), Close,
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrating the actual generator over a truncated interval of exponents preserves a positive tail contribution.",
        H("Truncated inverse-power mixture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truncated-power-profile"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncatedProfile"),
                H("Finite exponent mixture"),
                StatementSource.FromAuthor(Disp(Seq(Tau, Open, Z, Close, Eq, IntDomain,
                    Profile, Open, Z, Close, Thin, F.Id("ds")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The position z is an integer. The integrand is the shifted inverse-power profile at exponent one half plus s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("truncated-mixture-interchange-and-gain"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture.truncated_profile_analysis"),
                H("Interchange, closed form, and eventual gain"),
                StatementSource.FromAuthor(Analysis()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the closed form, X is two plus the absolute value of the real cast of z. "
                        + "The generator uses the actual occupation kernel weights. "
                        + "The eventual assertion is as n tends to infinity through the natural numbers, "
                        + "with the generator evaluated at n as an integer.")),
                    Paragraph(Text(
                        "The exponent integral commutes with the generator because the sum of the integrals of the absolute terms is finite. "
                        + "For the lower estimate, the positive Kelvin gap supplies a first moment weighted by the exponent "
                        + "of minus s times log n. Integrating from zero to the reciprocal of log n gives an inverse-log-square gain; "
                        + "the algebraic error is smaller for sufficiently large n."))),
                DescribeRole.Theorem))));
}
