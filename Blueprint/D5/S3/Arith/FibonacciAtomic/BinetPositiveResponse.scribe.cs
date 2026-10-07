using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class BinetPositiveResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The infinite logarithmic Binet tails give a strictly positive Dirichlet response.",
        H("Binet Tails and Positive Response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binet-logarithmic-coefficient"),
                DeclarationHandle.Create(Prefix + "beta"),
                H("The literal Binet coefficient"),
                StatementSource.FromAuthor(BetaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real q and natural n, b(q,n) is "
                    + "log(1-(-q)^n), bundled as a real arithmetic function. In Lean "
                    + "log(0)=0, so b(q,0)=0. At the actual Fibonacci parameter "
                    + "q=phi^(-2), this is the logarithmic Binet correction. The "
                    + "definition makes no sign or convergence assertion for arbitrary q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binet-complete-negative-tail"),
                DeclarationHandle.Create(Prefix + "negativeTail"),
                H("The complete negative tail"),
                StatementSource.FromAuthor(TailFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("E(q) is the infinite sum of -b(q,2(j+1)) "
                    + "over all natural j. For 0<q<=2/5 these are precisely the "
                    + "negative coefficient magnitudes, starting at index two. "
                    + "Convergence is proved in the contract below, not assumed in "
                    + "this total definition using Lean's tsum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binet-complete-positive-tail"),
                DeclarationHandle.Create(Prefix + "positiveTail"),
                H("The complete positive tail after the head"),
                StatementSource.FromAuthor(TailFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P(q) is the infinite sum of b(q,2(j+1)+1) "
                    + "over all natural j. For 0<q<=2/5 these are precisely the "
                    + "positive coefficients after b(q,1), starting at index three. "
                    + "The head is excluded from both tails."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binet-dirichlet-response"),
                DeclarationHandle.Create(Prefix + "response"),
                H("The response to the arithmetic logarithm"),
                StatementSource.FromAuthor(ResponseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each q>0, k(q) is the existing "
                    + "arithmetic-function Dirichlet inverse of b(q), multiplied by "
                    + "the existing arithmetic logarithm. The product and inverse "
                    + "in this display are Dirichlet convolution operations. "
                    + "Since b(q,1)=log(1+q)>0, the head is invertible. The value "
                    + "at zero is zero by the bundled arithmetic-function convention; "
                    + "the proof of q>0 has no mathematical effect on the response."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binet-signed-tail-response-contract"),
                DeclarationHandle.Create(Prefix + "binet_response_contract"),
                H("Summable tails, a quantitative gap, and a positive response"),
                StatementSource.FromAuthor(ContractFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real q with 0<q<=2/5, both infinite "
                        + "tail sequences are summable, and b(q,1)-E(q)-P(q)>=94q/2205. "
                        + "For every natural n, the sum of max(-b(q,d),0) over "
                        + "D(n) excluding 1 is at most E(q), and the sum of "
                        + "max(b(q,d),0) over the same set is at most P(q). Here "
                        + "D(n) is the finite positive-divisor set, with D(0) empty. "
                        + "The response satisfies k(q,1)=0; at every n>0 it is "
                        + "between (b(q,1)-E(q)-P(q))log(n)/(b(q,1)(b(q,1)-E(q))) "
                        + "and log(n)/(b(q,1)-E(q)); at every n>1 it is strictly positive.")),
                    Paragraph(Text("Parity identifies the even negative terms "
                        + "and odd positive terms. With r=q^2, the negative term "
                        + "at 2(j+1) is bounded by q^2 r^j/(1-q^2), and the positive "
                        + "term at 2(j+1)+1 is bounded by q^3 r^j. Geometric "
                        + "summability gives E(q)<=q^2/(1-q^2)^2 and "
                        + "P(q)<=q^3/(1-q^2). Splitting the shifted max sequences "
                        + "into their even and odd subsequences identifies their "
                        + "complete sums with E and P. The injective shift d to d-2 "
                        + "transfers these nonnegative infinite budgets to every "
                        + "finite divisor set excluding the head.")),
                    Paragraph(Text("The logarithmic head satisfies b(q,1)>=4q/5. "
                        + "The two geometric estimates give E(q)<=250q/441 and "
                        + "P(q)<=4q/21, leaving the stated gap. The upstream inverse "
                        + "identity discharges b(q)*k(q)=log exactly. The previously "
                        + "proved signed divisor response comparison then supplies "
                        + "both bounds, and their positive lower coefficient "
                        + "gives strict positivity when n>1. The conclusion retains "
                        + "the true infinite E and P, rather than substituting "
                        + "their geometric majorants.")),
                    Paragraph(Text("This is an infinite analytic parameter family. "
                        + "It closes the Binet budget premises of the positive "
                        + "response mechanism. It supplies no atom/lcm reconstruction "
                        + "identity, critical-scale cancellation estimate, signed "
                        + "Robin tail bound, or proof of RH."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula EvenIndex(Formula j) => Seq(D(2), Open, j, Plus, D(1), Close);
    private static Formula OddIndex(Formula j) => Seq(EvenIndex(j), Plus, D(1));

    private static Formula BetaFormula()
    {
        var q = F.Id("q"); var n = F.Id("n");
        return Disp(Seq(Forall, Sp, q, InMacro, Sp, Reals, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            Call("b", q, n), Eq, Sp, Call("log", Seq(D(1), Minus,
                new Formula.Power(Seq(Open, Minus, q, Close), n))), Comma, Sp,
            Call("b", q, D(0)), Eq, D(0)));
    }

    private static Formula TailFormula(bool negative)
    {
        var q = F.Id("q"); var j = F.Id("j");
        Formula term = negative
            ? Seq(Minus, Call("b", q, EvenIndex(j)))
            : Call("b", q, OddIndex(j));
        return Disp(Seq(Forall, Sp, q, InMacro, Sp, Reals, Comma, Sp,
            Call(negative ? "E" : "P", q), Eq, Sp,
            new Formula.Subscript(Sum, Seq(j, InMacro, Sp, Naturals)), term));
    }

    private static Formula ResponseFormula()
    {
        var q = F.Id("q");
        return Disp(Seq(Forall, Sp, q, InMacro, Sp, Reals, Comma, Sp,
            D(0), Lt, Sp, q, Rightarrow, Sp, Call("k", q), Eq, Sp,
            new Formula.Power(Call("b", q), Seq(Minus, D(1))), Star, Log));
    }

    private static Formula ContractFormula()
    {
        var q = F.Id("q"); var j = F.Id("j"); var n = F.Id("n"); var d = F.Id("d");
        Formula head = Call("b", q, D(1));
        Formula e = Call("E", q); Formula p = Call("P", q);
        Formula denominator = Seq(head, Minus, e);
        Formula budget(Formula coefficient, Formula bound) => Seq(
            new Formula.Subscript(Sum, Seq(d, InMacro, Sp, Call("D", n),
                Comma, Sp, d, Neq, D(1))), coefficient, Le, Sp, bound);
        Formula tails = Seq(Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp, Open,
            budget(Call("max", Seq(Minus, Call("b", q, d)), D(0)), e), Land, Sp,
            budget(Call("max", Call("b", q, d), D(0)), p), Close);
        Formula bounds = Seq(Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            D(0), Lt, Sp, n, Rightarrow, Sp,
            new Formula.Fraction(Seq(head, Minus, e, Minus, p),
                Seq(head, Cdot, Open, denominator, Close)), Cdot, Call("log", n),
            Le, Sp, Call("k", q, n), Le, Sp,
            new Formula.Fraction(Call("log", n), denominator));
        Formula strict = Seq(Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            D(1), Lt, Sp, n, Rightarrow, Sp, D(0), Lt, Sp, Call("k", q, n));
        return Disp(Seq(Forall, Sp, q, InMacro, Sp, Reals, Comma, Sp,
            D(0), Lt, Sp, q, Le, Sp, new Formula.Fraction(D(2), D(5)), Rightarrow, Sp,
            Open, Call("Summable", Seq(j, Mapsto, Minus, Call("b", q, EvenIndex(j)))),
            Land, Sp, Call("Summable", Seq(j, Mapsto, Call("b", q, OddIndex(j)))),
            Land, Sp, new Formula.Fraction(Seq(D(9, 4), Cdot, Sp, q), D(2, 2, 0, 5)),
            Le, Sp, head, Minus, e, Minus, p, Land, Sp, Open, tails, Close,
            Land, Sp, Call("k", q, D(1)), Eq, D(0), Land, Sp, Open, bounds, Close,
            Land, Sp, Open, strict, Close, Close));
    }
}
