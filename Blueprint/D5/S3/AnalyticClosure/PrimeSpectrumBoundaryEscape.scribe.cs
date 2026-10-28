using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class PrimeSpectrumBoundaryEscapeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual prime heat trace diverges at its critical endpoint, and normalization gives an infinite-variation Hilbert curve.",
        H("Critical Endpoint of the Prime Heat Curve"),
        Blocks(
            Entry("vector", "primeHeatVector", "The actual square-summable prime heat vector", VectorFormula(),
                "Under the prime-spectrum hypotheses, x(sigma) has coordinates exp(-(sigma/2) beta(k+1) log p) for sigma>alpha=1/b0. It is an element of the actual lp space over Nat.Primes times Nat; its value outside that open domain is the zero vector. No artificial zero spectral index is added.",
                DescribeRole.Definition),
            Entry("trace", "prime_spectrum_heat_trace_tendsto_atTop", "Heat-trace divergence from the right", TraceFormula(),
                "The boundary prime-reciprocal layer is not summable. Consequently its nonnegative finite partial sums are unbounded. Each such finite heat sum is continuous in sigma, and right-side summability bounds it by the actual heat trace. Thus the real heat trace tends to positive infinity from the right. The total tsum at the divergent endpoint is not interpreted as an infinite real value.",
                DescribeRole.Theorem),
            Entry("norm", "prime_spectrum_heat_norm_tendsto_atTop", "Divergence of the actual Hilbert norm", NormFormula(),
                "The squared lp norm equals the real heat trace at sigma. The norm therefore tends to positive infinity at alpha from the right.",
                DescribeRole.Theorem),
            Entry("escape", "prime_spectrum_normalized_heat_not_tendsto", "No strong endpoint limit", EscapeFormula(),
                "Every fixed coordinate of the normalized vector tends to zero, since its unnormalized coefficient has a finite endpoint value and its norm diverges. The actual vector is nonzero, so normalization has norm one. Any strong lp limit would have every coordinate zero, contradicting convergence of norms to one.",
                DescribeRole.Theorem),
            Entry("variation", "prime_spectrum_normalized_heat_eVariationOn_eq_top", "Infinite metric variation at the critical endpoint", VariationFormula(),
                "For every c>alpha the normalized Hilbert curve has infinite total metric variation on (alpha,c). Finite variation would give a strong right limit in the complete lp space, contradicting the preceding theorem. This establishes metric length of the actual curve; no Fisher-information derivative identity, Riemannian metric identification, global manifold completeness, or RH conclusion is asserted.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string heading,
        Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("prime-boundary-" + id), DeclarationHandle.Create(Module + declaration),
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
    private static Formula IndexType => Seq(Open, PrimeType, Times, Sp, NatType, Close);
    private static Formula HilbertType => Call("lp", IndexType, ComplexType, D(2));
    private static Formula Beta => F.Id("beta");
    private static Formula B0 => F.Id("b0");
    private static Formula Sigma => F.Id("sigma");
    private static Formula Alpha => Seq(Frac, Grp(D(1)), Grp(B0));
    private static Formula Vector => Call("primeHeatVector", Beta, B0, Sigma);
    private static Formula Normalized => Call("normalize", Vector);
    private static Formula RightFilter => Call("nhdsRight", Alpha);
    private static Formula Map(Formula body) => Seq(Open, Sigma, Sp, Mapsto, Sp, body, Close);
    private static Formula UnderHypotheses(Formula conclusion) =>
        All("beta", Seq(NatType, To, Sp, RealType), All("b0", RealType,
            Seq(D(0), Lt, B0, Rightarrow, Sp, Call("beta", D(1)), Eq, B0, Rightarrow, Sp,
                Open, All("k", NatType, Seq(B0, Plus, F.Id("k"), Leq, Sp,
                    Call("beta", Seq(F.Id("k"), Plus, D(1))))), Close, Rightarrow, Sp, conclusion)));

    private static Formula VectorFormula() => Disp(UnderHypotheses(All("sigma", RealType,
        Seq(Vector, Eq, Call("if", Seq(Alpha, Lt, Sigma),
            Call("heatCoefficient", Call("primeSpectrum", Beta), Seq(Frac, Grp(Sigma), Grp(D(2)))), D(0))))));

    private static Formula TraceFormula()
    {
        Formula a = F.Id("a");
        Formula trace = Seq(Sum, Underscore, Grp(a, InMacro, IndexType),
            Call("exp", Seq(Minus, Sigma, Times, Sp, Call("primeSpectrum", Beta, a))));
        return Disp(UnderHypotheses(Call("Tendsto", Map(trace), RightFilter, Call("atTop"))));
    }

    private static Formula NormFormula() => Disp(UnderHypotheses(Call("Tendsto",
        Map(new Formula.Norm(Vector)), RightFilter, Call("atTop"))));

    private static Formula EscapeFormula() => Disp(UnderHypotheses(All("x", HilbertType,
        Seq(Neg, Sp, Call("Tendsto", Map(Normalized), RightFilter, Call("nhds", F.Id("x")))))));

    private static Formula VariationFormula() => Disp(UnderHypotheses(All("c", RealType,
        Seq(Alpha, Lt, F.Id("c"), Rightarrow, Sp,
            Call("eVariationOn", Map(Normalized), Call("Ioo", Alpha, F.Id("c"))), Eq, Infty))));
}
