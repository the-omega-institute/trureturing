using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class LinearDensityHeatTraceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear counting density gives the reciprocal leading term of the spectral heat trace.",
        H("Linear Density Heat Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-density-heat-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace."
                    + "linear_density_heat_trace"),
                H("Linear density determines the leading heat-trace term"),
                StatementSource.FromAuthor(LinearDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let lambda be a positive strictly increasing real spectrum. For every "
                        + "real cutoff u, its sublevel set is required to be finite, so "
                        + "N_lambda(u) "
                        + "is the genuine cardinality of the set of indices with lambda(n) at most "
                        + "u. If N_lambda(u)-c u is bounded at infinity, then the residual of the "
                        + "exponential heat trace after subtracting c/t is bounded as t approaches "
                        + "zero through positive values.")),
                    Paragraph(Text(
                        "The proof first upgrades the eventual counting residual bound to a "
                        + "uniform bound on the positive half-line by monotonicity of finite "
                        + "sublevel cardinalities. The linear exponential moment and the bounded "
                        + "residual against the exponential kernel are therefore integrable.")),
                    Paragraph(Text(
                        "For each spectral value, its exponential term is written as the integral "
                        + "of t exp(-t u) over u at least lambda(n). Mathlib's nonnegative Tonelli "
                        + "theorem exchanges the integral and infinite sum. Pointwise, finiteness "
                        + "of the counting set identifies the sum of indicators with N_lambda(u). "
                        + "This proves both summability of the heat trace and the "
                        + "counting-integral "
                        + "identity rather than assuming that bridge.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Gamma integral evaluates the linear moment as 1/t^2. "
                        + "The residual integral has norm at most K/t, so multiplication by t "
                        + "leaves the uniform bound K. The result uses no Riemann hypothesis or "
                        + "other conjectural input and makes no lower-order limit claim."))),
                DescribeRole.Theorem))));

    private static Formula LinearDensityFormula()
    {
        Formula lambda = F.LambdaLower;
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula t = F.Id("t");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula nLambda = Apply(Sub(F.Id("N"), lambda), u);
        Formula thetaLambda = Apply(Sub(F.Id("Theta"), lambda), t);
        Formula positive = F.Seq(
            F.Open, F.Forall, F.Sp, n, F.Sp, F.InMacro, F.Sp, naturals,
            F.Comma, F.Sp, F.D(0), F.Sp, F.Lt, F.Sp, Apply(lambda, n), F.Close);
        Formula locallyFinite = F.Seq(
            F.Open, F.Forall, F.Sp, u, F.Sp, F.InMacro, F.Sp, reals,
            F.Comma, F.Sp, Call("Finite", SpectrumBelow(lambda, u)), F.Close);
        Formula density = F.Seq(
            nLambda, F.Sp, F.Minus, F.Sp, c, u, F.Sp, F.Eq, F.Sp,
            BigOAt(u, F.Infty));
        Formula zeroFromRight = F.Seq(F.D(0), F.Caret, F.Grp(F.Plus));
        Formula conclusion = F.Seq(
            thetaLambda, F.Sp, F.Minus, F.Sp, c, F.Slash, t,
            F.Sp, F.Eq, F.Sp, BigOAt(t, zeroFromRight));
        Formula countingDefinition = F.Seq(
            nLambda, F.Sp, F.Colon, F.Eq, F.Sp, Call("card", SpectrumBelow(lambda, u)));
        Formula heatDefinition = F.Seq(
            thetaLambda, F.Sp, F.Colon, F.Eq, F.Sp,
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)), F.Caret, F.Grp(F.Infty), F.Sp,
            F.Exp, F.Grp(F.Minus, t, Apply(lambda, n)));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, lambda, F.Colon, F.Sp, naturals, F.Sp, F.To, F.Sp, reals,
            F.Comma, F.Sp, c, F.Sp, F.InMacro, F.Sp, reals, F.Comma, F.RowBreak,
            positive, F.Sp, F.Land, F.Sp, Call("StrictMono", lambda), F.Sp, F.Land,
            F.RowBreak, locallyFinite, F.Sp, F.Land, F.Sp, density,
            F.Sp, F.Rightarrow, F.RowBreak, conclusion, F.Comma, F.RowBreak,
            F.Text, F.Grp(F.Id("where")), F.Quad, countingDefinition,
            F.Comma, F.Quad, heatDefinition, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    private static Formula SpectrumBelow(Formula lambda, Formula u)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.OpenBrace, n, F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("N")), F.Sp, F.Mid, F.Sp,
            Apply(lambda, n), F.Sp, F.Leq, F.Sp, u, F.CloseBrace);
    }

    private static Formula BigOAt(Formula variable, Formula target) =>
        new Formula.Subscript(Call("O", F.D(1)), F.Seq(variable, F.To, target));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
