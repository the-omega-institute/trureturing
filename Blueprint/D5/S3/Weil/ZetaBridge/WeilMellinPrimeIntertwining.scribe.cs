using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilMellinPrimeIntertwiningDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.";
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
        Formula a = F.Id("a"), M = F.Id("M"), h = F.Id("h"), x = F.Id("x");
        Formula d = F.Id("d"), A = F.Id("A"), t = F.Id("t"), n = F.Id("n");
        Formula p = Call("windowMellinSum", a, M, h);
        Formula q = Call("windowMellinSum", a, M, Call("LogTimesSeed", h));
        Formula r = Call("OddPart", p);
        Formula hypotheses = Call("And",
            Call("LessEqual", Call("exp", Call("mul", D(2), a)), M),
            Call("UpperSupport", h, Call("exp", a)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual weighted prime translations on an arithmetic Mellin model "
                + "collapse to the logarithmic seed, with its full window and parity correction retained.",
            H("Mellin Prime Intertwining"),
            Blocks(
                Paragraph(Text(
                    "Write E(h)=windowMellinSum(a,M,h), Xf(x)=x*f(x), and Rf(x)=f(-x). "
                    + "The same half-density and factor four are used by the existing "
                    + "WeilPolynomialMellinWindow. The arithmetic input is Mathlib's "
                    + "vonMangoldt_sum. There is no alternative zeta, Gamma or Weil form.")),
                Describe.Lean(DescribeId.Create("window-mellin-sum"),
                    DeclarationHandle.Create(Owner + "windowMellinSum"), H("Supported arithmetic synthesis"),
                    StatementSource.FromAuthor(Disp(Seq(Call("apply", p, x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("mul", D(4), Call("exp", Call("div", x, D(2))),
                                Call("SumIcc", D(1), M, Call("apply", h,
                                    Call("mul", n, Call("exp", x))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "a is real, M natural and h complex-valued on the reals. "
                        + "Closed endpoints make reflection exact. The difference from the "
                        + "earlier Ioc convention is isolated in the agreement theorem."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("prime-forward"),
                    DeclarationHandle.Create(Owner + "primeForward"), H("Actual one-sided prime block"),
                    StatementSource.FromAuthor(Disp(Seq(Call("primeForward", a, M, F.Id("f"), x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("SumIcc", D(1), M, Call("mul",
                                Call("div", Call("vonMangoldt", n), Call("sqrt", n)),
                                Call("apply", F.Id("f"), Seq(x, Plus, Call("log", n))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The original Lambda(n)/sqrt(n) coefficients and translated function "
                        + "values are specified independently. All prime powers are included. "
                        + "The n=1 term vanishes; terms beyond exp(2a) vanish on the window, "
                        + "and a term exactly at that threshold affects only an endpoint."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("prime-symmetric"),
                    DeclarationHandle.Create(Owner + "primeSymmetric"), H("Both prime translation directions"),
                    StatementSource.FromAuthor(Disp(Seq(Call("primeSymmetric", a, M, F.Id("f"), x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("SumIcc", D(1), M, Call("mul",
                                Call("div", Call("vonMangoldt", n), Call("sqrt", n)),
                                Call("add", Call("apply", F.Id("f"), Seq(x, Plus, Call("log", n))),
                                    Call("apply", F.Id("f"), Seq(x, Minus, Call("log", n)))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the unsigned symmetric translation block. Its negative gives "
                        + "the prime contribution to the canonical Weil operator. Reflection "
                        + "relates its two directions, but they are not identified before proof."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("cut-polynomial-seed"),
                    DeclarationHandle.Create(Owner + "cutPolynomialSeed"), H("The existing polynomial seed with upper cutoff"),
                    StatementSource.FromAuthor(Disp(Seq(Call("cutPolynomialSeed", a, d, A, t), Eq,
                        Call("If", Call("LessEqual", t, Call("exp", a)),
                            Call("SumRange", d, Call("mul", Call("apply", A, F.Id("j")),
                                Call("pow", t, Call("mul", D(2), F.Id("j"))))), D(0))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The seed is zero above exp(a). It is not an unknown prolate or Weil eigenfunction."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("polynomial-window-agreement"),
                    DeclarationHandle.Create(Owner + "polynomial_window_agreement"), H("Agreement with the existing canonical polynomial model"),
                    StatementSource.FromAuthor(Disp(Seq(Call("NotEqual", x, Seq(Minus, a)), Rightarrow,
                        Call("windowMellinSum", a, M, Call("cutPolynomialSeed", a, d, A), x), Eq,
                        Call("polynomialMellinWindow", a, M, d, A, x)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof uses the existing mellin_monomial_polynomial_value. "
                        + "The cutoff m*exp(x)<=exp(a) is exactly x<=a-log(m). "
                        + "The half-density and every monomial agree. Only the earlier lower "
                        + "endpoint convention is excluded; the represented L2 functions agree."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-forward-mellin-identity"),
                    DeclarationHandle.Create(Owner + "prime_forward_mellin_identity"), H("Exact all-scale arithmetic intertwining"),
                    StatementSource.FromAuthor(Disp(Seq(hypotheses, Rightarrow,
                        Call("primeForward", a, M, p, x), Eq,
                        Seq(Call("apply", q, x), Minus, Call("mul", x, Call("apply", p, x)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Assume exp(2a)<=M and h(t)=0 whenever t>exp(a). For every real x, "
                            + "the equality is B_plus E(h)=E(log(t)*h)-X E(h). Inside the window "
                            + "the half-density cancels sqrt(n) exactly. Terms with n*m>M vanish "
                            + "by support. Regroup the remaining product pairs by k=n*m and "
                            + "use the existing sum_{d|k} Lambda(d)=log(k). Outside the window "
                            + "both compressed sides vanish. No parity, positivity, regularity, "
                            + "spectral gap or desired residual identity is assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-even-mellin-identity"),
                    DeclarationHandle.Create(Owner + "prime_even_mellin_identity"), H("Full prime action after evenization"),
                    StatementSource.FromAuthor(Disp(Seq(hypotheses, Rightarrow,
                        Call("primeSymmetric", a, M, Call("EvenPart", p), x), Eq,
                        Seq(Call("apply", q, x), Plus, Call("apply", q, Seq(Minus, x)), Minus,
                            Call("mul", D(2), x, Call("apply", r, x)), Minus,
                            Call("primeForward", a, M, r, x), Minus,
                            Call("primeForward", a, M, r, Seq(Minus, x)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here r=(p-Rp)/2 is the actual odd part. Finite prolate arithmetic "
                        + "models need not have r=0. The identity retains its coordinate and "
                        + "translation corrections and all complex phases. For a>=0, the "
                        + "paper L2 consequence bounds this correction by "
                        + "2*(a+sum Lambda(n)/sqrt(n))*norm(r). This bound requires the "
                        + "actual L2 realization and does not claim a sufficiently small "
                        + "Weil residual along an unbounded scale sequence. The theory volume "
                        + "records the independently checked fixed-prolate parity budget. "
                        + "Lean elaboration, Scribe emission and the transitive axiom audit "
                        + "have not been run in this research continuation."))),
                    DescribeRole.Theorem))));
    }
}
