using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilInfiniteComplementLeakageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.";
    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }
    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(D(2)));

    public DocumentDefinition Create()
    {
        Formula L = F.Id("L"), N = F.Id("N"), s = F.Id("s");
        Formula u = F.Id("u"), v = F.Id("v"), pi = F.Id("pi");
        Formula density = Call("D", L, N, u, v, s);
        Formula mass = Seq(Call("SquareMass", u), Plus, Call("SquareMass", v));
        Formula right = Seq(Call("div", D(4), Seq(D(3), Sp, Sq(pi))), Sp, mass);
        Formula statement = Seq(
            Call("Positive", N), Land, Call("Positive", L), Land,
            Call("SquareSummable", u), Land, Call("SquareSummable", v),
            Rightarrow,
            Call("IntervalIntegrableOnQuarterBand", L, N, u, v), Land,
            Call("NormalizedQuarterBandIntegral", L, N, u, v), Leq, right);
        return DocumentDefinition.Create(ScribeNode.Create(
            "A convergent infinite exterior Fourier tail has quantitatively little "
                + "mass in the low-frequency quarter band, without an upper mode cutoff.",
            H("Weil Infinite Complement Leakage"),
            Blocks(
                Paragraph(Text(
                    "L is a positive real window length and N is a positive natural number. "
                    + "The sequences u,v : N -> C are square summable, with no finite upper "
                    + "support constraint. SquareMass(u) is sum_j |u_j|^2. "
                    + "The private Cauchy sum C(d,u)=sum_j u_j/(d+j+1) is absolutely "
                    + "convergent for d>0. The phase-adjusted orthonormal Fourier basis "
                    + "on [-L/2,L/2] is (-1)^n/sqrt(L)*exp(2*pi*i*n*x/L). "
                    + "u_j and v_j index modes N+j+1 and -(N+j+1).")),
                Describe.Lean(
                    DescribeId.Create("exterior-fourier-density"),
                    DeclarationHandle.Create(Owner + "exteriorFourierDensity"),
                    H("An explicit infinite-tail Cauchy density"),
                    StatementSource.FromAuthor(Disp(Seq(density, Eq,
                        Call("div", L, Sq(pi)), Sp,
                        Sq(Call("sin", Seq(pi, Sp, s))), Sp,
                        Sq(Call("norm", Seq(
                            Call("C", Seq(N, Plus, s), u), Minus,
                            Call("C", Seq(N, Minus, s), v))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The formula is evaluated on |s|<=N/4, away from every denominator "
                        + "zero. Physical frequency is t=2*pi*s/L. The identification with "
                        + "the Fourier transform of a general L2 exterior mode expansion "
                        + "is proved on paper in the existing theory volume; it has not "
                        + "been imported as an extra Lean theorem or axiom."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("infinite-complement-low-frequency-mass"),
                    DeclarationHandle.Create(Owner + "infinite_complement_low_frequency_mass"),
                    H("Infinite tails cannot concentrate in the low-frequency quarter band"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Positive(x) means 0<x. SquareSummable means Summable of the "
                        + "squared complex norms. IntervalIntegrableOnQuarterBand means "
                        + "Lebesgue interval integrability of D between -N/4 and N/4. "
                        + "NormalizedQuarterBandIntegral is (1/L)*integral_{-N/4}^{N/4}D(s) ds. "
                        + "The proof first bounds the inverse-square partial sums by a "
                        + "telescoping reciprocal difference. It then proves absolute "
                        + "convergence, Cauchy-Schwarz for the infinite response, uniform "
                        + "series continuity, and the integral inequality. Thus neither a "
                        + "nonconvergent total sum nor a nonintegrable total integral is "
                        + "being assigned zero to make the conclusion vacuous. "
                        + "The all-form-domain arithmetic lower bound beta(a,N), the "
                        + "explicit prime-containing scale example, and the full "
                        + "operator Schur estimate remain paper results in this increment. "
                        + "This theorem makes no assumption about a spectral gap, "
                        + "ground-state parity, or zeros of Xi."))),
                    DescribeRole.Theorem))));
    }
}
