using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusRateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit rate for the Möbius prime-window remainder",
        H("A double-logarithmic saving in the truncation order"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-quantitative"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_quantitative_of_rh"),
            H("The same window and decay exponent"),
            StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The signed residual E(m,a,B) is the integral of the negative part of the "
                    + "prime-only tail divided by sqrt(x) on [a,B], with 2 log(B/a) and the endpoint "
                    + "difference of the ordinary zero primitive subtracted. For 3 ≤ n ≤ m subtract "
                    + "the power difference a^(1/n−1/2)−B^(1/n−1/2) with coefficient "
                    + "−2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract the nth root "
                    + "primitive difference with coefficient −μ(n). Actual zero occurrences retain "
                    + "their analytic multiplicities.")),
                Paragraph(Text("The Chebyshev and floor convolutions reduce the Möbius prefix estimate "
                    + "to two ranges in the quotient. Choosing the quotient cutoff as the four-fifths "
                    + "power of the logarithm gives a one-fifth logarithmic saving, uniformly over "
                    + "prefixes. The signed trivial-root response inherits the saving by Abel summation.")),
                Paragraph(Text("Set L=(1+log log(m+1))/8. In the near range, with log x at most "
                    + "L(m+1), signed Abel summation costs at most a constant times exp(2L) m/log m "
                    + "after extracting the exponential in log x. This fits the stated coefficient.")),
                Paragraph(Text("In the far range, with log x at least L(m+1), split the actual unit "
                    + "frequency bins at height of order L². The low-bin mass grows at most as the "
                    + "fourth root of the cutoff. The square root of the squared high-bin mass is "
                    + "bounded by the inverse fourth root. Sum the geometric degree weights in "
                    + "the first part and use Gaussian local sampling in the second. Both parts give "
                    + "a bound proportional to m/sqrt(L).")),
                Paragraph(Text("For sufficiently large m these estimates give the explicit rate "
                    + "on the signed density. Integrating between log a and log B yields the stated "
                    + "power difference. The previous uniform linear estimate absorbs the finite "
                    + "set of smaller orders into the single constant. Equal endpoints give zero."))),
            DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, string domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), F.Seq(F.Mathbb, F.Grp(F.Id(domain))), body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula WindowEstimate()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var b = F.Id("B");
        var t = F.Id("T");
        var k = F.Id("K");
        var residual = new Formula.FunctionCall(FormulaIdentifier.Create("E"), [m, a, b]);
        var rate = new Formula.Negate(new Formula.FunctionCall(FormulaIdentifier.Create("s"), [m]));
        var gap = Subtract(new Formula.Power(a, rate), new Formula.Power(b, rate));
        var doubleLog = F.Seq(F.Log, F.Sp, F.Log, F.Sp, F.Open, Add(m, F.D(1)), F.Close);
        var scale = F.Seq(F.Sqrt, F.Grp(Add(F.D(1), doubleLog)));
        var coefficient = new Formula.Fraction(Multiply(k, m), scale);
        var bound = Le(new Formula.Absolute(residual), Multiply(coefficient, gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var constants = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(And(Le(F.D(2), t), positive), orders)));
        return F.Disp(Imp(F.Id("RH"), constants));
    }
}
