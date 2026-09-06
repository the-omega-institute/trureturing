using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArithmeticCouplingJetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.";
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

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), n = F.Id("n"), m = F.Id("m");
        Formula N = F.Id("N"), S = F.Id("S"), v = F.Id("v");
        Formula symbol = Call("s", c, n), budget = Call("B", c);
        Formula col = Call("Column", c, S, v, m), jet = Call("Jet", c, S, v, m);
        Formula mabs = Call("abs", m);
        Formula bound = Seq(Call("div", Seq(D(2), Sp, budget, Sp, N),
            Seq(F.Id("pi"), Sp, mabs, Sp, Grp(mabs, Minus, N))), Sp, Call("NormMass", S, v));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The explicit pole, Gamma and finite-prime boundary symbol controls "
                + "every exterior divided-difference coupling mode.",
            H("Weil Arithmetic Coupling Jet"),
            Blocks(
                Paragraph(Text(
                    "c is a natural number at least two, L=log(c), omega_n=2*pi*n/L, "
                    + "beta_j=2*j+1/2, and w_j=vonMangoldt(j)/sqrt(j). "
                    + "The symbol is s(c,n)=-2*omega_n*(cosh(L/2)-1)/(omega_n^2+1/4) "
                    + "-sum_{j>=0} omega_n*(1-exp(-beta_j*L))/(beta_j^2+omega_n^2) "
                    + "-sum_{j<c} w_j*sin(omega_n*log(j)). "
                    + "These are the actual boundary terms of the canonical arithmetic form. "
                    + "Their identification with its Fourier matrix follows the explicit "
                    + "calculations in Connes, Consani and Moscovici, arXiv:2511.22755, "
                    + "Lemma 2.3 and Section 4, and is a paper bridge in the existing theory volume.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-symbol"),
                    DeclarationHandle.Create(Owner + "arithmeticBoundarySymbol"),
                    H("The full arithmetic boundary symbol"),
                    StatementSource.FromAuthor(Disp(Seq(symbol, Eq,
                        Call("PoleGammaPrimeSineExpression", c, n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "PoleGammaPrimeSineExpression is the explicit expression in the "
                        + "introductory paragraph. The prime cutoff is the integer c, "
                        + "with its endpoint omitted since the endpoint sine is zero. "
                        + "No zeta zero positions or lowest eigenvectors enter."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-budget"),
                    DeclarationHandle.Create(Owner + "arithmeticBoundaryBudget"),
                    H("An independent arithmetic envelope"),
                    StatementSource.FromAuthor(Disp(Seq(budget, Eq,
                        D(2), Sp, Call("cosh", Call("HalfLog", c)), Plus,
                        Call("AbsolutePrimeWeightSum", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "HalfLog(c)=log(c)/2. AbsolutePrimeWeightSum(c) is the finite sum "
                        + "of |vonMangoldt(j)/sqrt(j)| over 0<=j<c. The two nonprime "
                        + "contributions are bounded by 2*(cosh(L/2)-1) and 2."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-symbol-bound"),
                    DeclarationHandle.Create(Owner + "arithmetic_boundary_symbol_bound"),
                    H("Convergence and an unconditional arithmetic symbol bound"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow,
                        Call("AbsoluteGammaSineSummability", c, n), Land,
                        Call("abs", symbol), Leq, budget))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "n is any integer. The Gamma sine series is absolutely convergent "
                        + "and |s(c,n)|<=B(c). The proof majorizes its absolute terms by "
                        + "|omega|/((2*j+1/2)^2+omega^2), proves a telescoping bound on "
                        + "every partial sum, and then controls the pole and prime terms. "
                        + "It assumes no operator-norm bound, Gamma-tail sign, spectral gap "
                        + "or Riemann hypothesis."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("coupling-column"),
                    DeclarationHandle.Create(Owner + "couplingColumn"),
                    H("The arithmetic exterior coupling column"),
                    StatementSource.FromAuthor(Disp(Seq(col, Eq,
                        Call("DividedDifferenceSum", c, S, v, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a finite set S of integers and v:Z->C, this is "
                        + "sum_{n in S} ((s(c,n)-s(c,m))/(pi*(m-n)))*v_n, with the "
                        + "real coefficient cast to C. Exterior modes in the theorem "
                        + "cannot equal an interior mode, so no denominator vanishes."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("coupling-first-jet"),
                    DeclarationHandle.Create(Owner + "couplingFirstJet"),
                    H("Retain the two boundary moments"),
                    StatementSource.FromAuthor(Disp(Seq(jet, Eq,
                        Call("BoundaryMomentJet", c, S, v, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The definition is sum_{n in S} ((s(c,n)-s(c,m))/(pi*m))*v_n. "
                        + "Collecting this finite sum gives (b0-s(c,m)*a0)/(pi*m), "
                        + "where a0=sum v_n and b0=sum s(c,n)*v_n. "
                        + "No boundary moment is required to vanish."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-coupling-first-jet-error"),
                    DeclarationHandle.Create(Owner + "arithmetic_coupling_first_jet_error"),
                    H("An all-scale exterior coupling remainder"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("AtLeastTwo", c), Land, Call("Nonnegative", N), Land,
                        Call("InteriorIndicesBounded", S, N), Land, Call("Exterior", m, N),
                        Rightarrow, Call("norm", Seq(col, Minus, jet)), Leq, bound))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "N is real and nonnegative, every n in S satisfies |n|<=N, "
                        + "and Exterior(m,N) means N<|m|. NormMass(S,v)=sum_{n in S}|v_n|. "
                        + "The coefficient difference is exactly "
                        + "(s(c,n)-s(c,m))*n/(pi*m*(m-n)). The arithmetic envelope "
                        + "and |m-n|>=|m|-N prove the displayed estimate. "
                        + "There is no upper exterior cutoff. The infinite Gram tail bound, "
                        + "the verified interval inequalities at c=3, and the resulting "
                        + "paper/computer-assisted full-space simple-even statement are "
                        + "documented separately; they are not asserted as Lean results "
                        + "of this declaration. No unbounded-scale ground-mode convergence "
                        + "to Xi is proved."))),
                    DescribeRole.Theorem))));
    }
}
