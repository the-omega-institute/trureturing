using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusSublinearDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniformly sublinear Möbius prime-window remainder",
        H("One left threshold for every accuracy"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-sublinear"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_sublinear_of_rh"),
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
                Paragraph(Text("The Chebyshev and floor convolutions for μ(n) log n give a signed "
                    + "identity for the Möbius partial sum times log n. Split at a fixed fraction "
                    + "of the cutoff. The power saving for the Chebyshev error bounds the initial "
                    + "part and Abel summation bounds the complementary part. The resulting "
                    + "little-o estimate also bounds all prefixes at the common scale. Abel "
                    + "summation then controls the increasing logarithmic trivial-root response.")),
                Paragraph(Text("The signed Chebyshev truncation tail has a logarithmic saving "
                    + "after integrating on the original positive cutoff. For log x at most "
                    + "L(m+1), the integrated Chebyshev root term and its arithmetic main term "
                    + "are each decreasing in the omitted degree. Signed summation gives the "
                    + "required saving on their difference.")),
                Paragraph(Text("For log x at least L(m+1), choose a finite set of unit frequency "
                    + "bins so the complementary squared bin masses have arbitrarily small "
                    + "sum. Gaussian local sampling bounds that complement, including the "
                    + "variation in coefficients between adjacent degrees. The finite set of "
                    + "bins satisfies the geometric weight sum bound 1+(m+1)²/log x. Choose "
                    + "L and then the minimum degree to make both contributions small.")),
                Paragraph(Text("The eventual sign of the prime-only tail fixes the left "
                    + "threshold before the accuracy and the truncation order are chosen. "
                    + "Integrate over [log a, log B] with s(m)=1/2−1/(m+1)≥1/6. Equal "
                    + "endpoints give zero on both sides."))),
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
        var k = F.Id("M");
        var epsilon = F.Id("epsilon");
        var residual = new Formula.FunctionCall(FormulaIdentifier.Create("E"), [m, a, b]);
        var rate = new Formula.Negate(new Formula.FunctionCall(FormulaIdentifier.Create("s"), [m]));
        var gap = Subtract(new Formula.Power(a, rate), new Formula.Power(b, rate));
        var bound = Le(new Formula.Absolute(residual), Multiply(Multiply(epsilon, m), gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, epsilon);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(k, m), windows));
        var cutoff = Bind(FormulaQuantifier.Exists, "M", "N", And(Le(F.D(2), k), orders));
        var accuracy = Bind(FormulaQuantifier.ForAll, "epsilon", "R", Imp(positive, cutoff));
        return F.Disp(Imp(F.Id("RH"), Bind(FormulaQuantifier.Exists, "T", "R", And(Le(F.D(2), t), accuracy))));
    }
}
