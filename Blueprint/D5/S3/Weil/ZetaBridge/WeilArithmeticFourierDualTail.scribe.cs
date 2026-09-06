using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArithmeticFourierDualTailDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.";
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
        Formula c = F.Id("c"), n = F.Id("n"), M = F.Id("M");
        Formula w = F.Id("w"), e = F.Id("energy"), beta = F.Id("beta");
        Formula j = F.Id("j"), m = Call("add", M, F.Id("j"), D(1));
        Formula term = Call("DualTerm", c, n, M, e, w);
        Formula exactTerm = Call("div", Call("div", Call("div",
            Grp(Call("mul", n, Call("s", c, n)), Minus,
                Call("mul", m, Call("s", c, m))),
            Grp(Call("square", m), Minus, Call("square", n))), Call("energy", j)),
            Grp(Call("square", m), Minus, Call("square", w)));
        Formula bound = Call("div", Call("mul", D(2), Call("ArithmeticBudget", c)),
            Call("mul", D(3), beta, M, Grp(M, Minus, n)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An effective infinite-tail estimate for the actual arithmetic "
                + "high-to-low Fourier readout, with a quadratic cutoff rate.",
            H("Weil Arithmetic Fourier Dual Tail"),
            Blocks(
                Paragraph(Text(
                    "Use exactly s(c,n)=arithmeticBoundarySymbol from "
                    + "WeilArithmeticCouplingJet. It includes the finite von Mangoldt "
                    + "sum, poles and the absolutely convergent Gamma sine series. "
                    + "The independently proved envelope is B(c)=arithmeticBoundaryBudget(c). "
                    + "With m=M+j+1, DualTerm(j) equals "
                    + "((n*s(c,n)-m*s(c,m))/(m^2-n^2)) / energy(j) / (m^2-w^2). "
                    + "All divisions by real scalars are cast into the complex field.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-even-dual-term"),
                    DeclarationHandle.Create(Owner + "arithmeticEvenDualTerm"),
                    H("The concrete arithmetic dual summand"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("DualTerm", c, n, M, e, w, F.Id("j")), Eq,
                        exactTerm))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the collected even divided-difference coefficient "
                        + "multiplied by the complex Fourier Cauchy response and an "
                        + "inverse energy weight. It is defined independently of any "
                        + "desired bound or eigenfunction."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-even-fourier-dual-tail-bound"),
                    DeclarationHandle.Create(Owner + "arithmetic_even_fourier_dual_tail_bound"),
                    H("Absolute convergence and a computable infinite remainder"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("And", Call("AtLeast", c, D(2)), Call("Less", n, M),
                            Call("Positive", beta), Call("AllWeightsAtLeast", e, beta),
                            Call("LessEqual", Call("norm", w), Call("div", M, D(2)))),
                        Rightarrow,
                        Call("And", Call("SummableNorm", term),
                            Call("LessEqual", Call("norm", Call("tsum", term)), bound))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The arithmetic symbol bound is derived in the imported "
                            + "source, not assumed. For m>n>=0 it gives "
                            + "|(n*s_n-m*s_m)/(m^2-n^2)|<=B/(m-n). "
                            + "The complex restriction gives |m^2-w^2|>=3*m^2/4. "
                            + "Also m-n>=(M-n)*m/M. Therefore the summand is dominated "
                            + "by 4*B*M/(3*beta*(M-n))*m^(-3).")),
                        Paragraph(Text(
                            "The positive telescoping inequality "
                            + "(x+1)^(-3)<=1/(2*x^2)-1/(2*(x+1)^2) proves both "
                            + "summability and sum_{m>M}m^(-3)<=1/(2*M^2). "
                            + "This is a genuine complete exterior series, not a finite "
                            + "terminal cutoff. No zero data, spectral gap, unknown "
                            + "operator norm or Xi convergence is an input.")),
                        Paragraph(Text(
                            "In the actual phase-adjusted unnormalized cosine basis, "
                            + "multiply this bound by t_n*L^(3/2)*|z*sin(L*z/2)|/pi^3, "
                            + "where t_0=1, t_n=2 for n>0 and w=L*z/(2*pi). "
                            + "This bounds the missing component of C*D^(-1)g_Q. "
                            + "The checker uses this bound, exact binary endpoint sums "
                            + "and an interval LDL solve on the candidate-orthogonal "
                            + "space. The complex-disk zero count follows on paper "
                            + "from the resulting strict Rouche inequality. Operator "
                            + "identification, that numerical computation and the zero "
                            + "count are not conclusions of this Lean declaration."))),
                    DescribeRole.Theorem))));
    }
}
