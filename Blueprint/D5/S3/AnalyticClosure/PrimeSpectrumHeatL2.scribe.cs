using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class PrimeSpectrumHeatL2Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear prime-spectrum growth gives an explicit geometric heat-trace bound and a quantitative L2 norm estimate.",
        H("Quantitative Prime-Spectrum Heat Bounds"),
        Blocks(
            Entry("spectrum", "primeSpectrum", "The logarithmic prime spectrum", DefinitionFormula(),
                "The length indexed by a prime p and a natural layer k is beta(k+1) log p.",
                DescribeRole.Definition),
            Entry("heat-bound", "prime_spectrum_heat_trace_geometric_bound", "An explicit geometric heat-trace bound",
                HeatBoundFormula(),
                "Assume b0>0 and beta(k+1)>=b0+k. For sigma>1/b0, every prime p>=2 gives a geometric majorant in k. Summing that majorant bounds the real heat trace by the convergent prime series divided by 1-2^(-sigma); beta(1) need not equal b0.",
                DescribeRole.Theorem),
            Entry("l2-domain", "prime_spectrum_heat_l2_iff", "The exact square-summability domain", L2Formula(),
                "The existing boundary-divergent heat abscissa gives the exact L2 half-plane. This auxiliary result supplies the coefficient vector used in the norm bound.",
                DescribeRole.Theorem),
            Entry("l2-bound", "prime_spectrum_heat_l2_norm_bound", "A quantitative coefficient norm bound", NormBoundFormula(),
                "For sigma>1/(2 b0), square summability defines the lp coefficient vector. Its coordinate norm squares are the real heat terms at 2 sigma, so the geometric trace estimate bounds its squared norm uniformly over every imaginary coordinate t.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string heading,
        Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("prime-heat-" + id), DeclarationHandle.Create(Module + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula PrimeType => Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id("Primes")));
    private static Formula SpectrumType => Parenthesized(Seq(PrimeType, Times, Sp, NatType));
    private static Formula Beta => F.Id("beta");
    private static Formula B0 => F.Id("b0");
    private static Formula Spectrum => Call("primeSpectrum", Beta);
    private static Formula At(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Threshold => Seq(Frac, Grp(D(1)), Grp(Seq(D(2), Times, Sp, B0)));
    private static Formula GrowthHypotheses => Seq(D(0), Lt, B0, Rightarrow, Sp, Parenthesized(All("k", NatType, Seq(B0, Plus, F.Id("k"), Leq, Sp, At(Beta, Seq(F.Id("k"), Plus, D(1)))))), Rightarrow);
    private static Formula Hypotheses => Seq(At(Beta, D(1)), Eq, B0, Rightarrow, Sp, GrowthHypotheses);
    private static Formula UnderHypotheses(Formula conclusion) =>
        All("beta", Seq(NatType, To, RealType), All("b0", RealType, Seq(Hypotheses, conclusion)));
    private static Formula Bound(Formula parameter)
    {
        Formula p = F.Id("p");
        Formula numerator = Seq(Sum, Underscore, Grp(p, InMacro, PrimeType),
            new Formula.Power(p, Seq(Minus, parameter, Times, Sp, B0)));
        Formula denominator = Seq(D(1), Minus,
            new Formula.Power(D(2), Seq(Minus, parameter)));
        return Seq(Frac, Grp(numerator), Grp(denominator));
    }

    private static Formula DefinitionFormula()
    {
        Formula pk = F.Id("pk");
        Formula p = new Formula.Subscript(pk, D(1));
        Formula k = new Formula.Subscript(pk, D(2));
        return Disp(All("beta", Seq(NatType, To, RealType), All("pk", SpectrumType,
            Seq(At(Spectrum, pk), Eq, At(Beta, Seq(k, Plus, D(1))), Times, Sp, Log, Open, p, Close))));
    }

    private static Formula HeatBoundFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula pk = F.Id("pk");
        Formula heatSum = Seq(Sum, Underscore, Grp(pk, InMacro, SpectrumType),
            Call("exp", Seq(Minus, sigma, Times, Sp, At(Spectrum, pk))));
        Formula conclusion = All("sigma", RealType,
            Seq(Frac, Grp(D(1)), Grp(B0), Lt, sigma, Rightarrow, Sp, heatSum, Leq, Sp, Bound(sigma)));
        return Disp(All("beta", Seq(NatType, To, RealType), All("b0", RealType,
            Seq(GrowthHypotheses, conclusion))));
    }

    private static Formula L2Formula()
    {
        Formula s = F.Id("s");
        return Disp(UnderHypotheses(All("s", ComplexType,
            Seq(Call("MemLp", Call("heatCoefficient", Spectrum, s), D(2)),
                Leftrightarrow, Sp, Threshold, Lt, Call("Re", s)))));
    }

    private static Formula NormBoundFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula t = F.Id("t");
        Formula vector = Call("heatCoefficient", Spectrum, Seq(sigma, Plus, F.Id("i"), Times, Sp, t));
        Formula conclusion = Seq(Threshold, Lt, sigma, Rightarrow, Sp, Operatorname, Grp(F.Id("let")), Sp, F.Id("x"), Colon,
            Call("lp", SpectrumType, ComplexType, D(2)), Eq, vector, Semi, Sp,
            new Formula.Power(new Formula.Norm(F.Id("x")), D(2)), Leq, Sp, Bound(Parenthesized(Seq(D(2), Times, Sp, sigma))));
        return Disp(UnderHypotheses(All("sigma", RealType, All("t", RealType, conclusion))));
    }
}
