using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusSpacingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSpacing";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse double-logarithmic rate for the Möbius prime window",
        H("A rate from the actual separation of the degree samples"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-spacing"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_spacing_of_rh"),
            H("Inverse double-logarithmic saving"),
            StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("RH denotes Mathlib RiemannHypothesis. Write θ(t) for the sum "
                    + "of log p over primes p ≤ t. The tail primeTail(x) is the integral of "
                    + "(θ(t)−t)/t² over t > x. The signed residual E(m,a,B) starts with the "
                    + "integral of max(−primeTail(x),0)/sqrt(x) on [a,B] minus 2 log(B/a).")),
                Paragraph(Text("The zero series run over all nontrivial zeta-zero occurrences ρ, "
                    + "with each zero repeated according to its analytic multiplicity. The ordinary "
                    + "primitive P(x) is the real part of the sum of "
                    + "exp(i Im(ρ) log x)/(ρ(1−ρ)i Im(ρ)). The degree-n root primitive Pₙ(x) is "
                    + "the real part of the sum of 2n² x^(ρ/n−1/2)/(ρ(n−ρ)(n−2ρ)). "
                    + "Both primitives use x > 0.")),
                Paragraph(Text("From E's starting expression subtract P(B)−P(a). For 3 ≤ n ≤ m "
                    + "subtract the power difference a^(1/n−1/2)−B^(1/n−1/2) multiplied by "
                    + "−2 μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m and 2n < m+1 subtract "
                    + "Pₙ(B)−Pₙ(a) multiplied by −μ(n), where μ is the Möbius function.")),
                Paragraph(Text("The Chebyshev and floor convolutions reduce the Möbius prefix estimate "
                    + "to two ranges in the quotient. Choosing the quotient cutoff as the four-fifths "
                    + "power of the logarithm gives a one-fifth logarithmic saving, uniformly over "
                    + "prefixes. The signed trivial-root response inherits the saving by Abel summation.")),
                Paragraph(Text("Set L=(1+log log(m+1))/8. In the near range, with log x at most "
                    + "L(m+1), signed Abel summation costs at most a constant times exp(2L) m/log m "
                    + "after extracting the exponential in log x. This fits the stated coefficient.")),
                Paragraph(Text("In the far range set q=m+1 and u=log x. The actual coordinates "
                    + "u/n have separation at least u/q². In a unit window the separated-sample "
                    + "estimate uses the reciprocal of min(1,u/q²) on the value integral. The "
                    + "phase derivative carries a bin weight bounded by both q and a constant "
                    + "times one plus the absolute bin index.")),
                Paragraph(Text("Interpolate those two bounds to obtain a q^(7/8) derivative cost "
                    + "and square-summable bin mass proportional to (1+|k|)^(−5/8). Apply the "
                    + "same estimate to the adjacent coefficient increments and sum their "
                    + "variation. The weighted sum over unit windows then costs at most a "
                    + "constant times 1+q²/u+q^(7/8). With u≥Lq and L=(1+log log q)/8, "
                    + "this is bounded by a constant times m/(1+log log q).")),
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
        var rate = Subtract(new Formula.Fraction(F.D(1), Add(m, F.D(1))),
            new Formula.Fraction(F.D(1), F.D(2)));
        var gap = Subtract(new Formula.Power(a, rate), new Formula.Power(b, rate));
        var doubleLog = F.Seq(F.Log, F.Sp, F.Log, F.Sp, F.Open, Add(m, F.D(1)), F.Close);
        var scale = Add(F.D(1), doubleLog);
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
