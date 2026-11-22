using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusPowerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A power-saving rate for the Möbius prime window",
        H("A rate from the actual separation of the degree samples"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-power"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_power_of_rh"),
            H("Power saving in the truncation order"),
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
                Paragraph(Text("Put q=m+1 and u=log x. The zero-free half-plane estimate "
                    + "with θ=1/2 and α=1/4 gives the ordinary Möbius prefix bound of order q^(3/4). "
                    + "For u≤q, use that bound with signed Abel summation on the omitted degrees. "
                    + "The exponential factor exp(u/p) is at most exp(2), where p=ceil(q/2).")),
                Paragraph(Text("For q≤u≤q^(29/28), split the occurrence sum at the unit-bin "
                    + "height H=floor(q^(1/7)). Below the cutoff, finite complex Abel summation "
                    + "costs the prefix bound times the total variation of the normalized mode. "
                    + "Its variation is bounded by a constant times (1+|Im ρ|u/q)/|ρ|. "
                    + "The total inverse-root mass below the cutoff is of order (H+1)^(1/4).")),
                Paragraph(Text("Above the cutoff the squared bin masses sum to at most a "
                    + "constant times H^(−1/2). The separation of the actual degree samples "
                    + "bounds that contribution by a constant times q H^(−1/4). Both "
                    + "contributions have order at most q^(27/28). For u≥q^(29/28), "
                    + "the uncut separated sampling bound costs 1+q²/u+q^(7/8).")),
                Paragraph(Text("The signed trivial-root response costs q^(3/4)(1+log q). "
                    + "On the arithmetic tail the interval Möbius prefix at q+j is bounded "
                    + "by a constant times q^(−1/4)(q+j). Abel summation with the decreasing "
                    + "Chebyshev weights gives a normalized tail of order q^(3/4).")),
                Paragraph(Text("Extract exp(−(1/2−1/q)u) from the density estimates and integrate "
                    + "between log a and log B. The resulting endpoint power difference includes "
                    + "coincident endpoints. One threshold and one constant work for every m≥2."))),
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
        var exponent = new Formula.Fraction(F.D(2, 7), F.D(2, 8));
        var coefficient = Multiply(k, new Formula.Power(m, exponent));
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
