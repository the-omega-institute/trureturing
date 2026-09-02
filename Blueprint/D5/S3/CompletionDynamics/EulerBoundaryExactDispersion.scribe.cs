using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics;

internal sealed class EulerBoundaryExactDispersionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler-boundary log-cosh dispersion realizes the exact hyperbolic rapidity identities.",
        H("Euler-Boundary Exact Dispersion"),
        Blocks(
            Node(
                "limiting-speed-scale",
                "cInfinity",
                "Limiting speed scale",
                Disp(Seq(
                    F.Id("c"), Underscore, Grp(Infty), Colon, Eq,
                    Frac, Grp(Pi), Grp(D(2)))),
                "The source normalization fixes the limiting speed scale at pi over two.",
                DescribeRole.Definition),
            Node(
                "rapidity-coordinate",
                "rapidity",
                "Rapidity coordinate",
                Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Theta, Open, F.Id("k"), Close, Colon, Eq,
                    F.Id("c"), Underscore, Grp(Infty), F.Id("k"))),
                "Rapidity is the limiting speed scale multiplied by the wave number.",
                DescribeRole.Definition),
            Node(
                "euler-boundary-energy",
                "eulerBoundaryEnergy",
                "Euler-boundary energy",
                Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("E"), Underscore, Grp(D(1)), Open, F.Id("k"), Close,
                    Colon, Eq, Log, Sp, Operatorname, Grp(F.Id("cosh")),
                    Open, Theta, Open, F.Id("k"), Close, Close)),
                "The dispersion is the logarithm of the hyperbolic cosine of rapidity.",
                DescribeRole.Definition),
            Node(
                "euler-boundary-velocity",
                "eulerBoundaryVelocity",
                "Euler-boundary group velocity",
                Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("v"), Underscore, Grp(D(1)), Open, F.Id("k"), Close,
                    Colon, Eq,
                    Frac,
                    Grp(F.Id("d"), F.Id("E"), Underscore, Grp(D(1))),
                    Grp(F.Id("d"), F.Id("k")), Open, F.Id("k"), Close)),
                "Group velocity is the ordinary real derivative of the dispersion.",
                DescribeRole.Definition),
            Node(
                "euler-boundary-exact-dispersion",
                "euler_boundary_exact_dispersion",
                "Euler-boundary exact dispersion",
                ExactDispersionFormula(),
                "For every real wave number, the derivative witness computes the group "
                    + "velocity as c-infinity times tanh of rapidity. Positivity of cosh "
                    + "justifies exponentiating the logarithm, and positivity of pi keeps "
                    + "the normalized velocity away from totalized division by zero.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(
        string id,
        string declaration,
        string title,
        Formula statement,
        string paragraph,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);

    private static Formula ExactDispersionFormula() => Disp(Seq(
        Begin, Grp(F.Id("aligned")),
        Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
        F.Id("E"), Underscore, Grp(D(1)), Open, F.Id("k"), Close,
        Sp, Eq, Sp, Log, Sp, Operatorname, Grp(F.Id("cosh")),
        Open, Frac, Grp(Pi, F.Id("k")), Grp(D(2)), Close,
        Sp, Land, RowBreak,
        F.Id("v"), Underscore, Grp(D(1)), Open, F.Id("k"), Close,
        Sp, Eq, Sp, Frac, Grp(Pi), Grp(D(2)),
        Operatorname, Grp(F.Id("tanh")),
        Open, Frac, Grp(Pi, F.Id("k")), Grp(D(2)), Close,
        Sp, Land, RowBreak,
        F.Id("e"), Caret, Grp(F.Id("E"), Underscore, Grp(D(1)), Open,
        F.Id("k"), Close), Sp, Eq, Sp,
        Operatorname, Grp(F.Id("cosh")), Open, Theta, Open, F.Id("k"), Close, Close,
        Sp, Land, RowBreak,
        Frac,
        Grp(F.Id("v"), Underscore, Grp(D(1)), Open, F.Id("k"), Close),
        Grp(F.Id("c"), Underscore, Grp(Infty)),
        Sp, Eq, Sp, Operatorname, Grp(F.Id("tanh")),
        Open, Theta, Open, F.Id("k"), Close, Close, Dot,
        End, Grp(F.Id("aligned"))));
}
