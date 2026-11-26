using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class ConditionalGiniTVDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Information/ConditionalGiniTV.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp finite-alphabet comparison between posterior total variation and conditional Gini loss.",
        H("Posterior Total Variation and Conditional Gini Loss"),
        Blocks(
            Paragraph(Text(
                "Let p be a probability mass function, r the refined readout, t the target, and f "
                + "the deterministic coarsening. M(p,r,d) is the refined fiber mass. T(p,r,t,f) "
                + "is the sum over refined fibers of their real mass times the total variation "
                + "between the two target posteriors. Each posterior coordinate is its joint "
                + "target-and-fiber mass divided by the corresponding fiber mass, using totalized "
                + "division in the extended nonnegative reals. A zero denominator gives zero. "
                + "The ratios are converted to real coordinates before taking total variation. "
                + "Total variation is half the finite sum of absolute coordinate differences. "
                + "The outer sum ranges over all refined labels. L(p,r,t,f) is the "
                + "coarse impurity minus the refined impurity in real coordinates. K(A) equals "
                + "floor(n squared over four) divided by n for a target type A of cardinality n.")),
            Describe.Lean(
                DescribeId.Create("weighted-posterior-total-variation-squared-bound"),
                DeclarationHandle.Create(Module + "weighted_posterior_totalVariation_sq_le_gini_defect"),
                H("Upper bound for mass-weighted posterior total variation"),
                StatementSource.FromAuthor(UpperBound()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a positive-mass refined fiber both posteriors are normalized. Their "
                    + "difference has sum zero. Centering its positive sign indicator and applying "
                    + "Cauchy–Schwarz gives the factor k(n-k)/n for a sign set of size k. The "
                    + "maximum over k is K(A). Weighted Cauchy–Schwarz across refined fibers then "
                    + "gives the stated inequality using the exact conditional Gini defect. Zero-mass "
                    + "fibers disappear from the weighted sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-gini-total-variation-bound-attained"),
                DeclarationHandle.Create(Module + "conditional_gini_tv_attained"),
                H("Two refined fibers attain the coefficient"),
                StatementSource.FromAuthor(Attainment()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use X equal to A, the identity target, and the constant map f from Bool to Unit. "
                    + "Split A into blocks of sizes floor(n/2) and n minus floor(n/2), assigning "
                    + "one half of the probability mass uniformly to each block. The refined readout "
                    + "reports the block. The coarse posterior is the half-mixture of both block "
                    + "posteriors. Each posterior total variation is one half. For a first block "
                    + "of size k, the defect is n divided by the product 4 k (n-k). Equality with "
                    + "positive defect forces every universal coefficient to be at least K(A)."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula UpperBound()
    {
        Formula x = F.Id("X");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula a = F.Id("A");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula f = F.Id("f");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, c, Comma, Sp, d, Comma, Sp, a,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", a), CloseBracket, Comma, RowBreak, Grp(),
            p, Colon, Sp, Call("PMF", x), Comma, Sp,
            r, Colon, Sp, x, Sp, To, Sp, d, Comma, Sp,
            t, Colon, Sp, x, Sp, To, Sp, a, Comma, Sp,
            f, Colon, Sp, d, Sp, To, Sp, c, Comma, RowBreak, Grp(),
            D(2), Sp, Le, Sp, Call("card", a), Sp, Rightarrow, Sp,
            new Formula.Power(Call("T", p, r, t, f), D(2)), Sp, Le, Sp,
            Call("K", a), Sp, Cdot, Sp, Call("L", p, r, t, f), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Attainment()
    {
        Formula a = F.Id("A");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula b = F.Id("b");
        Formula boolean = Seq(Operatorname, Grp(F.Id("Bool")));
        Formula identity = Seq(Operatorname, Grp(F.Id("id")));
        Formula constantMap = Seq(Operatorname, Grp(F.Id("const")));
        Formula weightedTV = Call("T", p, r, identity, constantMap);
        Formula loss = Call("L", p, r, identity, constantMap);
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", a), CloseBracket, Comma, Sp,
            D(2), Sp, Le, Sp, Call("card", a), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, p, Colon, Sp, Call("PMF", a), Comma, Sp,
            r, Colon, Sp, a, Sp, To, Sp, boolean, Comma, RowBreak, Grp(),
            Open, Forall, Sp, b, Colon, Sp, boolean, Comma, Sp,
            Call("M", p, r, b), Sp, Eq, Sp, half, Close, Sp, Land, Sp,
            weightedTV, Sp, Eq, Sp, half, Sp, Land, Sp, D(0), Sp, Lt, Sp, loss,
            Sp, Land, RowBreak, Grp(),
            new Formula.Power(weightedTV, D(2)), Sp, Eq, Sp,
            Call("K", a), Sp, Cdot, Sp, loss, Dot, End, Grp(F.Id("gathered"))));
    }
}
