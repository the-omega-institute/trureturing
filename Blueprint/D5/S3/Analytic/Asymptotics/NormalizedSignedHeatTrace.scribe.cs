using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class NormalizedSignedHeatTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed mass prefixes control the normalization of a finite heat trace.",
        H("Monotonicity of the normalized signed heat trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-signed-heat-trace-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/NormalizedSignedHeatTrace."
                        + "normalized_cutoff_heat_strictMono"),
                H("Strict increase under the signed prefix and denominator conditions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The active spectrum consists of the first n masses of a nonnegative "
                        + "nondecreasing sequence. The signed weight sum over every prefix is "
                        + "nonpositive, and the total is negative. On (0,b] the denominator "
                        + "B is negative, has derivative dB, and satisfies B(x) < x*dB(x).")),
                    Paragraph(Text(
                        "Finite Abel summation applies to the positive decreasing exponential "
                        + "weights and to the positive decreasing weights (1+u)*exp(-u) "
                        + "that result from differentiating the heat trace multiplied by x. "
                        + "This makes that factor negative and strictly decreasing. The "
                        + "denominator inequality makes x/B(x) a second negative strictly "
                        + "decreasing factor. Their product increases strictly.")),
                    Paragraph(Text(
                        "For the proper-time cutoff model, the denominator is K-1 and the "
                        + "strict derivative condition follows from the bound on the "
                        + "mass-weighted logarithmic term. This analytic implication "
                        + "requires the model-specific mass and denominator bounds as inputs."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var i = F.Id("i");
        var x = F.Id("x");
        var b = F.Id("b");
        var g = F.Id("g");
        var z = F.Id("z");
        var denominator = F.Id("B");
        var derivative = new Formula.Subscript(denominator, F.Id("d"));
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var interval = Seq(Open, D(0), Comma, b, CloseBracket);
        var prefix = Seq(Forall, Sp, k, Leq, Sp, n, Comma, Sp, WeightSum(i, k, At(g, i)), Leq, Sp, D(0));
        var total = Seq(WeightSum(i, n, At(g, i)), Lt, D(0));
        var spectrum = Seq(Forall, Sp, i, Comma, D(0), Leq, Sp, At(z, i));
        var denominatorLaw = Seq(Forall, Sp, x, InMacro, Sp, interval, Comma, Sp,
            At(denominator, x), Lt, D(0), Land, Sp,
            Apply(F.Id("HasDerivAt"), denominator, At(derivative, x), x), Land, Sp,
            At(denominator, x), Lt, x, At(derivative, x));
        var exponent = Seq(Minus, Frac, Grp(At(z, i)), Grp(x));
        var heat = Seq(Frac,
            Grp(Seq(Seq(x, Caret, Grp(D(2))), WeightSum(i, n,
                Seq(At(g, i), Apply(F.Id("exp"), exponent))))),
            Grp(At(denominator, x)));
        var strict = Apply(F.Id("StrictMonoOn"), Seq(x, Mapsto, heat), interval);
        return Disp(Seq(Forall, Sp, n, Colon, naturals, Comma, Sp, g, Comma, z, Colon,
            naturals, To, reals, Comma, Sp, denominator, Comma, derivative, Colon, reals,
            To, reals, Comma, Sp, b, Colon, reals, Comma, Sp, Parenthesize(prefix), Land, Sp, total, Land,
            Sp, Parenthesize(spectrum), Land, Sp, Apply(F.Id("Monotone"), z), Land, Sp,
            Parenthesize(denominatorLaw), To, Sp, strict));
    }

    private static Formula Parenthesize(Formula body) => Seq(Open, body, Close);

    private static Formula At(Formula f, Formula x) => Apply(f, x);

    private static Formula Apply(Formula f, params Formula[] arguments)
    {
        var parts = new List<Formula> { f, Open };
        foreach (var argument in arguments)
        {
            if (parts.Count > 2)
                parts.Add(Comma);
            parts.Add(argument);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }

    private static Formula WeightSum(Formula index, Formula bound, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Lt, bound)), term);
}
