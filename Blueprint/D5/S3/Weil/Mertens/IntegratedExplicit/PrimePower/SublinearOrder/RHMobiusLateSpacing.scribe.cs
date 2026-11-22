using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusLateSpacingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusLateSpacing";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A smaller exponent on late signed RH prime windows",
        H("Keep the spacing of the high-frequency samples"),
        Blocks(
        Describe.Lean(DescribeId.Create("rh-mobius-prime-window-late-spacing"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_late_spacing_of_rh"),
            H("The signed prime-window bound with a logarithmic starting point"), StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("RH denotes Mathlib RiemannHypothesis. The window discrepancy is the integral of "
                    + "max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a). The tail primeTail(x) integrates "
                    + "(θ(t)−t)/t² over t>x, where θ(t) sums log p over primes p≤t.")),
                Paragraph(Text("The zero series use all actual nontrivial zero occurrences, "
                    + "each repeated according to its analytic multiplicity. The ordinary primitive P(x) "
                    + "is the real part of the sum of exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). "
                    + "The degree-n root primitive Pₙ(x) is the real part of the sum of "
                    + "2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)), for x>0.")),
                Paragraph(Text("The signed residual E(m,a,B) subtracts P(B)−P(a) from the "
                    + "window discrepancy and then subtracts both signed correction sums. "
                    + "For 3≤n≤m, the first sum uses −2 μ(n)n²/((n−1)(n−2)) multiplied by "
                    + "a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1, the second sum "
                    + "uses −μ(n) multiplied by Pₙ(B)−Pₙ(a).")),
                Paragraph(Text("Write q=m+1 and u=log x. Inside the integration interval u≥q^(1+d). "
                    + "With η=min(ε/3,1/12), the ordinary Möbius prefix controls the arithmetic and trivial-root terms. "
                    + "The low-frequency estimate uses the signed degree prefix with cutoff H.")),
                Paragraph(Text("The high-frequency bound retains the sampling distance u/q². "
                    + "The derivative of each phase is controlled by the square mass of the bin envelope "
                    + "min(q,1+|k|)(1+|k|)^(η−1). The total high-frequency cost is bounded by a constant times the sum "
                    + "[(1+q²/u)H^(η−1/2)+q^(1/2+η)].")),
                Paragraph(Text("Take H=floor(q^(1/2−d)), including H=1 at d=1/2. The low and high estimates "
                    + "then both have order at most q^(3/4−d/2+2η). Integrating between log a and log B "
                    + "gives the original endpoint gap, including value zero at equality."))),
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
        var rate = Subtract(new Formula.Fraction(F.D(1), Add(m, F.D(1))),
            new Formula.Fraction(F.D(1), F.D(2)));
        var gap = Subtract(new Formula.Power(a, rate), new Formula.Power(b, rate));
        var epsilon = F.Id("epsilon");
        var d = F.Id("d");
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var exponent = Add(Subtract(new Formula.Fraction(F.D(3), F.D(4)),
            new Formula.Fraction(d, F.D(2))), epsilon);
        var loga = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [a]);
        var late = Le(new Formula.Power(Add(m, F.D(1)), Add(F.D(1), d)), loga);
        var coefficient = Multiply(k, new Formula.Power(m, exponent));
        var bound = Le(new Formula.Absolute(residual), Multiply(coefficient, gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(And(Le(t, a), Le(a, b)), late), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var constants = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(And(Le(F.D(2), t), positive), orders)));
        var slack = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, epsilon);
        return F.Disp(Imp(F.Id("RH"),
                        Bind(FormulaQuantifier.ForAll, "d", "R",
                Imp(And(Le(F.D(0), d), Le(d, half)),
                    Bind(FormulaQuantifier.ForAll, "epsilon", "R", Imp(slack, constants))))));
    }
}
