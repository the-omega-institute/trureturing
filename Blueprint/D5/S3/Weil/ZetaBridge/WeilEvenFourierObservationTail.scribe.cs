using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilEvenFourierObservationTailDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula L = F.Id("L"), N = F.Id("N"), z = F.Id("z"), v = F.Id("v");
        Formula response = Call("evenExteriorResponse", L, N, v, z);
        Formula coefficient = Call("div", Call("mul", D(8), Call("cube", L)),
            Call("mul", D(2, 7), Call("fourthPower", F.Id("pi")), Call("cube", N)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The full even Fourier tail admits an absolutely convergent complex-frequency "
                + "response with cubic squared cutoff decay. The estimate controls the "
                + "observable needed by the Weil-to-Xi route.",
            H("Even Fourier Observation Tail"),
            Blocks(
                Paragraph(Text(
                    "The actual window is [-L/2,L/2]. For n>0 use the existing "
                    + "phase-adjusted cosine basis (-1)^n*sqrt(2/L)*cos(2*pi*n*x/L), "
                    + "zero extended outside that interval, with Fourier kernel exp(i*z*x). "
                    + "The coefficient sequence v_j refers to n=N+j+1. The Fourier "
                    + "identification is a paper bridge in the existing RH source analysis.")),
                Describe.Lean(
                    DescribeId.Create("even-exterior-response"),
                    DeclarationHandle.Create(Owner + "evenExteriorResponse"),
                    H("The complete exterior response"),
                    StatementSource.FromAuthor(Disp(Seq(response, Eq,
                        Call("CanonicalCosineTail", L, N, v, z)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Write w=z*L/(2*pi) and n_j=N+j+1. The response is "
                        + "[-L*sqrt(2*L)/(2*pi^2)]*z*sin(L*z/2) "
                        + "*sum_j v_j/(n_j^2-w^2). This is an infinite coefficient "
                        + "series, not an upper-truncated matrix. The theorem uses only "
                        + "L>0, N>0 and L*norm(z)<=pi*N, which exclude every denominator "
                        + "zero. No identity at a totalized removable pole is claimed."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("even-exterior-fourier-observation-bound"),
                    DeclarationHandle.Create(Owner + "even_exterior_fourier_observation_bound"),
                    H("Absolute convergence and cubic squared tail bound"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("And", Call("Positive", L), Call("Positive", N),
                            Call("SquareSummable", v),
                            Call("LessEqual", Call("mul", L, Call("norm", z)),
                                Call("mul", F.Id("pi"), N))),
                        Rightarrow, Sp,
                        Call("And", Call("AbsolutelySummable", Call("CauchyTerms", L, N, v, z)),
                            Call("LessEqual", Call("normSq", response),
                                Call("mul", coefficient,
                                    Call("normSq", Call("mul", z,
                                        Call("sin", Call("mul", Call("div", L, D(2)), z)))),
                                    Call("sumNormSq", v))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The norm restriction gives norm(n_j^2-w^2)>=3*n_j^2/4. "
                            + "A positive telescoping identity proves "
                            + "sum_{n>N} n^(-4)<=1/(3*N^3), including convergence. "
                            + "Young's inequality gives absolute summability of the "
                            + "coefficient products. Finite Cauchy-Schwarz followed by "
                            + "the sum limit gives the full infinite-series estimate. "
                            + "The physical Fourier factor is retained exactly.")),
                        Paragraph(Text(
                            "For norm(z)<=R and abs(Im(z))<=b the paper consequence is "
                            + "norm(response)<=sqrt(8/(27*pi^4))*L^(3/2)*R*exp(b*L/2) "
                            + "*N^(-3/2)*norm(v). This applies to an arbitrary even L2 "
                            + "tail after the same-source Fourier/Parseval identification. "
                            + "If its arithmetic energy dominates beta*norm(v)^2, "
                            + "the squared observation budget is divided by beta.")),
                        Paragraph(Text(
                            "The existing source analysis applies this estimate to the "
                            + "explicit, suitably normalized prolate model of "
                            + "Connes-Consani-Moscovici. It constructs an evenized, "
                            + "finite dyadic candidate family with the same Xi limit. "
                            + "That model-limit proof, the factor-four Mellin "
                            + "normalization calculation, and the observable Schur "
                            + "energy certificate are paper results. None is silently "
                            + "asserted by this Lean theorem. The fixed 129-entry "
                            + "numerical candidate has not been identified with that "
                            + "new family. No unbounded-scale ground approximation "
                            + "or RH conclusion is claimed. Lean and Scribe compilation "
                            + "were not run in this session."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("inverse-fourth-partial-le"),
                    DeclarationHandle.Create(Owner + "inverse_fourth_partial_le"),
                    H("The consumed exact inverse-fourth partial tail"),
                    StatementSource.FromAuthor(Disp(Seq(Call("Positive", N), Rightarrow, Call("LessEqual", Call("InverseFourthPartial", N, F.Id("k")), Call("sub", Call("div", D(1), Call("mul", D(3), Call("cube", N))), Call("div", D(1), Call("mul", D(3), Call("cube", Call("add", N, F.Id("k")))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For every natural N>0 and every natural k, including k=0, sum_{j<k} 1/(N+j+1)^4<=1/(3*N^3)-1/(3*(N+k)^3). This minimally exposes the already present private fourth_partial proof, leaving all original definitions and proof bodies intact. It is reuse, not a novelty claim. Its live consumer is ActualColumnRemainder.paired_first_jet_remainder_tail and thereby the full paired actual column. All compiler, axiom, Reg source reconstruction/enrollment, Scribe and CI checks remain pending."))),
                    DescribeRole.Theorem))));
    }
}
