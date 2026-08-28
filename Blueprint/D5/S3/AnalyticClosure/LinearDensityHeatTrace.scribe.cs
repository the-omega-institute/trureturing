using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class LinearDensityHeatTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear spectral counting density gives a reciprocal-time heat trace up to bounded error.",
        H("Linear-Density Heat Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-density-heat-trace"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/LinearDensityHeatTrace.linear_density_heat_trace"),
                H("Linear density controls the heat trace"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let spectrum be a positive, strictly increasing real sequence tending "
                            + "to infinity, and let c be positive. Assume its sublevel counting "
                            + "function differs from c times u by a fixed bound for all large u.")),
                    Paragraph(Text(
                        "Then there are constants B and delta, with delta positive, such that for "
                            + "every 0 < t <= delta the exponential spectral series is summable "
                            + "and its difference from c/t has absolute value at most B.")),
                    Paragraph(Text(
                        "The proof first converts the counting estimate at spectrum(n) into a "
                            + "uniform displacement from the arithmetic lattice (n+1)/c. It then "
                            + "compares the heat series to the corresponding geometric series, "
                            + "bounding the finite head and the summable tail separately.")),
                    Paragraph(Text(
                        "Repository searches for heat-trace, counting-density, Stieltjes, and "
                            + "Laplace bridge statements found no complete match. The local proof "
                            + "uses Mathlib's geometric-series sums, exponential remainder bounds, "
                            + "and infinite-sum comparison lemmas."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula spectrum = F.Id("spectrum");
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula t = F.Id("t");
        Formula countBound = F.Id("C");
        Formula threshold = F.Id("U");
        Formula heatBound = F.Id("B");
        Formula delta = DeltaLower;
        Formula spectrumN = Call("spectrum", n);
        Formula atTop = Seq(Operatorname, Grp(F.Id("atTop")));
        Formula sublevel = Seq(
            OpenBrace, n, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            Call("spectrum", n), Sp, Leq, Sp, u, CloseBrace);
        Formula countError = new Formula.Absolute(Seq(
            Call("ncard", sublevel), Sp, Minus, Sp, c, Sp, Times, Sp, u));
        Formula heatTerm = Call("exp", Seq(
            Minus, t, Sp, Times, Sp, spectrumN));
        Formula heatSeries = Call("tsum", Seq(
            n, Sp, Mapsto, Sp, heatTerm));
        Formula heatError = new Formula.Absolute(Seq(
            heatSeries, Sp, Minus, Sp, new Formula.Fraction(c, t)));
        Formula positiveSpectrum = Seq(
            Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, spectrumN);
        Formula countingDensity = Seq(
            Exists, Sp, countBound, Comma, Sp, threshold, Colon, Sp, reals, Comma, Sp,
            D(0), Sp, Leq, Sp, countBound, Sp, Land, Sp,
            Forall, Sp, u, Colon, Sp, reals, Comma, Sp,
            threshold, Sp, Leq, Sp, u, Sp, Rightarrow, Sp,
            countError, Sp, Leq, Sp, countBound);
        Formula heatConclusion = Seq(
            Exists, Sp, heatBound, Comma, Sp, delta, Colon, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp,
            Forall, Sp, t, Colon, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Land, Sp, t, Sp, Leq, Sp, delta,
            Sp, Rightarrow, Sp,
            Call("Summable", Seq(n, Sp, Mapsto, Sp, heatTerm)), Sp, Land, Sp,
            heatError, Sp, Leq, Sp, heatBound);

        return Disp(Seq(
            Forall, Sp, spectrum, Colon, Sp,
            new Formula.TypeArrow(naturals, reals), Comma, Sp,
            c, Colon, Sp, reals, Comma, Sp,
            Open, positiveSpectrum, Close, Sp, Land, Sp,
            Call("StrictMono", spectrum), Sp, Land, Sp,
            Call("Tendsto", spectrum, atTop, atTop), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, c, Sp, Land, Sp,
            Open, countingDensity, Close, Sp, Rightarrow, Sp,
            Open, heatConclusion, Close, Dot));
    }
}
