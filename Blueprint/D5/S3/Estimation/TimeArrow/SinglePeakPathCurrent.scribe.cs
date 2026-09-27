using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class SinglePeakPathCurrentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the single-peak parity kernel, the forward-versus-reversed log-likelihood of every finite path "
            + "is one net current times the cycle affinity plus two endpoint terms.",
        H("Single-Current Form of the Path Likelihood Ratio"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-peak-region"),
                DeclarationHandle.Create(Module + "region"),
                H("Regions of the single-peak kernel"),
                StatementSource.FromAuthor(RegionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The state space carries a sign function chi with values plus or minus one and a "
                        + "distinguished peak z with chi(z) = 1. The region H is the peak itself, B is the "
                        + "rest of the peak's sign class, and Z is the opposite sign class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-profile"),
                DeclarationHandle.Create(Module + "profile"),
                H("Single-peak profile"),
                StatementSource.FromAuthor(ProfileFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The profile b takes the value r at the peak, the value -q on the rest of the peak's "
                        + "sign class, and the value 0 on the opposite class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-kernel"),
                DeclarationHandle.Create(Module + "kernel"),
                H("Single-peak parity kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With normalizer N, the transition weight from x to y is (1 + chi(x) chi(y) b(x)) / N. "
                        + "On the hypercube of dimension d with chi the product of coordinates and N = 2^d "
                        + "this is the parity kernel P(x,y) = (1 + a(x) chi(y)) / N with a(x) = chi(x) b(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-path-law"),
                DeclarationHandle.Create(Module + "forwardLaw"),
                H("Forward path law"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward law of the path x_0, ..., x_T starts from the uniform mass 1/N and "
                        + "multiplies the transition weights along the path."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reverse-path-law"),
                DeclarationHandle.Create(Module + "reverseLaw"),
                H("Time-reversed path law"),
                StatementSource.FromAuthor(ReverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reversed law evaluates the same path with every transition traversed backwards, "
                        + "again from the uniform mass 1/N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("region-transition-count"),
                DeclarationHandle.Create(Module + "transitions"),
                H("Region transition counts"),
                StatementSource.FromAuthor(TransitionsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "N_UV counts the times t < T at which the path moves from region U to region V."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("region-endpoint-defect"),
                DeclarationHandle.Create(Module + "endpointDefect"),
                H("Endpoint defect"),
                StatementSource.FromAuthor(DefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Delta_U is the indicator that the path starts in U minus the indicator that it ends in U."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("region-weight"),
                DeclarationHandle.Create(Module + "regionWeight"),
                H("Region transition weight"),
                StatementSource.FromAuthor(WeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The weight w with parameters a, b, c assigns a to H -> B, b to B -> Z and c to Z -> H, the negatives to the "
                        + "reversed transitions, and 0 to every transition inside one region."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-likelihood-current"),
                DeclarationHandle.Create(Module + "log_forward_div_reverse_eq_current"),
                H("Single-current form of the direction log-likelihood"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume chi takes only the values 1 and -1, chi(z) = 1, |r| < 1, |q| < 1 and N > 0. "
                            + "Then for every path x and horizon T the log of the forward law divided by the "
                            + "reversed law is the displayed expression, where A = log((1 + r)/(1 - q)), "
                            + "B_0 = log(1 + q) and C = -log(1 - r).")),
                    Paragraph(Text(
                        "Every transition weight is positive. A transition inside one region has equal "
                            + "forward and backward weights. The ratios across regions are (1 + r)/(1 - q) from "
                            + "H to B, 1 + q from B to Z and 1/(1 - r) from Z to H, because chi(x) chi(y) is 1 "
                            + "inside a sign class and -1 across classes. The uniform initial masses cancel, the "
                            + "logarithm of the product of ratios is the sum of region weights w(Y_t, Y_(t+1)) "
                            + "with a = A, b = B_0 and c = C.")),
                    Paragraph(Text(
                        "That sum is reduced to one current as follows. Each weight equals a potential "
                            + "difference plus the affinity a + b + c times the signed indicator of the edge "
                            + "between Z and H, with potential 0 on H, a on B and a + b on Z. Summing along the "
                            + "path telescopes the potentials, and the three endpoint defects add to zero, which "
                            + "turns the potential difference into a Delta_H - b Delta_Z. Consequently the "
                            + "triple (J, Y_0, Y_T) with J = N_ZH - N_HZ determines the likelihood ratio of "
                            + "the two time directions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Sub(Formula name, Formula index) => Seq(name, Underscore, Grp(index));

    private static Formula Count(string from, string to) =>
        Sub(F.Id("N"), Seq(F.Id(from), F.Id(to)));

    private static Formula Defect(string region) => Sub(Delta, F.Id(region));

    private static Formula RegionFormula()
    {
        Formula x = F.Id("x"), z = F.Id("z");
        return Disp(Seq(
            F.Id("H"), Eq, Sp, OpenBrace, z, CloseBrace, Comma, Qquad, Sp,
            F.Id("B"), Eq, Sp, OpenBrace, x, Colon, Sp, Call("chi", x), Eq, D(1), Comma, Sp, x, Sp, Neq, Sp, z,
            CloseBrace, Comma, Qquad, Sp,
            F.Id("Z"), Eq, Sp, OpenBrace, x, Colon, Sp, x, Sp, Neq, Sp, z, Comma, Sp, Call("chi", x), Sp, Neq, Sp,
            D(1), CloseBrace));
    }

    private static Formula ProfileFormula()
    {
        Formula x = F.Id("x");
        return Disp(Seq(
            Call("b", x), Eq, Sp, F.Id("r"), Sp, F.Text, Grp(F.Id("on")), Sp, F.Id("H"), Comma, Qquad, Sp,
            Call("b", x), Eq, Minus, F.Id("q"), Sp, F.Text, Grp(F.Id("on")), Sp, F.Id("B"), Comma, Qquad, Sp,
            Call("b", x), Eq, D(0), Sp, F.Text, Grp(F.Id("on")), Sp, F.Id("Z")));
    }

    private static Formula KernelFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Disp(Seq(
            Call("P", x, y), Eq, Sp,
            Frac, Grp(D(1), Plus, Call("chi", x), Sp, Call("chi", y), Sp, Call("b", x)), Grp(F.Id("N"))));
    }

    private static Formula Product(Formula body)
    {
        Formula t = F.Id("t");
        return Seq(Prod, Underscore, Grp(t, Lt, F.Id("T")), Sp, body);
    }

    private static Formula ForwardFormula()
    {
        Formula t = F.Id("t");
        return Disp(Seq(
            Call("Q", F.Id("x")), Eq, Sp, Frac, Grp(D(1)), Grp(F.Id("N")), Sp,
            Product(Call("P", Sub(F.Id("x"), t), Sub(F.Id("x"), Seq(t, Plus, D(1)))))));
    }

    private static Formula ReverseFormula()
    {
        Formula t = F.Id("t");
        return Disp(Seq(
            ReversedQ(), Open, F.Id("x"), Close, Eq, Sp,
            Frac, Grp(D(1)), Grp(F.Id("N")), Sp,
            Product(Call("P", Sub(F.Id("x"), Seq(t, Plus, D(1))), Sub(F.Id("x"), t)))));
    }

    private static Formula TransitionsFormula()
    {
        Formula t = F.Id("t");
        return Disp(Seq(
            Sub(F.Id("N"), Seq(F.Id("U"), F.Id("V"))), Eq, Sp,
            Lvert, Sp, OpenBrace, t, Lt, F.Id("T"), Colon, Sp,
            Sub(F.Id("Y"), t), Eq, F.Id("U"), Comma, Sp,
            Sub(F.Id("Y"), Seq(t, Plus, D(1))), Eq, F.Id("V"), CloseBrace, Sp, Rvert));
    }

    private static Formula ReversedQ() => Seq(F.Id("Q"), Caret, Grp(Mathrm, Grp(F.Id("rev"))));

    private static Formula Indicator(Formula condition) =>
        Seq(Mathbf, Grp(D(1)), Underscore, Grp(condition));

    private static Formula DefectFormula()
    {
        return Disp(Seq(
            Sub(Delta, F.Id("U")), Eq, Sp,
            Indicator(Seq(Sub(F.Id("Y"), D(0)), Eq, F.Id("U"))), Minus,
            Indicator(Seq(Sub(F.Id("Y"), F.Id("T")), Eq, F.Id("U")))));
    }

    private static Formula WeightFormula()
    {
        return Disp(Seq(
            Call("w", F.Id("H"), F.Id("B")), Eq, F.Id("a"), Comma, Quad, Sp,
            Call("w", F.Id("B"), F.Id("Z")), Eq, F.Id("b"), Comma, Quad, Sp,
            Call("w", F.Id("Z"), F.Id("H")), Eq, F.Id("c"), Comma, Quad, Sp,
            Call("w", F.Id("V"), F.Id("U")), Eq, Minus, Call("w", F.Id("U"), F.Id("V")), Comma, Quad, Sp,
            Call("w", F.Id("U"), F.Id("U")), Eq, D(0)));
    }

    private static Formula LogFrac(Formula top, Formula bottom) =>
        Seq(Log, Sp, Frac, Grp(top), Grp(bottom));

    private static Formula MainFormula()
    {
        Formula r = F.Id("r"), q = F.Id("q");
        Formula a = LogFrac(Seq(D(1), Plus, r), Seq(D(1), Minus, q));
        Formula b0 = Seq(Log, Open, D(1), Plus, q, Close);
        Formula c = Seq(Log, Open, D(1), Minus, r, Close);
        return Disp(Seq(
            LogFrac(Call("Q", F.Id("x")), Seq(ReversedQ(), Open, F.Id("x"), Close)), Eq, Sp,
            Open, a, Plus, b0, Minus, c, Close,
            Open, Count("Z", "H"), Minus, Count("H", "Z"), Close,
            Plus, a, Sp, Defect("H"), Minus, b0, Sp, Defect("Z")));
    }
}
