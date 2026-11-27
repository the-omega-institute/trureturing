using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class PowerPrefixWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerPrefixWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From Möbius prefixes to uniform prime-window bounds",
        H("Balance the low and high frequencies at one cutoff"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-power-prefix"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_of_power_prefix"),
            H("A signed prime-window bound from an ordinary prefix exponent"),
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
                Paragraph(Text("M(N) is the sum of μ(n) over 1≤n≤N. The hypothesis "
                    + "|M(N)|≤P N^β gives an absolute bound P q^β for every shorter "
                    + "prefix up to q=m+1. It controls the arithmetic and near-range "
                    + "terms. The trivial-root contribution has an additional factor "
                    + "1+log q, absorbed by any fixed positive gap above β.")),
                Paragraph(Text("Let u=log x. For u≥q, Abel summation over degrees and "
                    + "the total variation of the damped mode give the low-bin cost "
                    + "O(P q^β(H+1)^(1+η)). Weighted sampling with the squared bin masses "
                    + "bounds the complement by O(q H^(η−1/2)). Both bounds are uniform "
                    + "over the full far range.")),
                Paragraph(Text("Set γ=2(1−β)/3 and H=floor(q^γ). Then H+1≤2q^γ and "
                    + "H≥q^γ/2. The latter inequality applies to the negative power in "
                    + "the tail. Both resulting exponents equal (2+β)/3+γη, and "
                    + "β<(2+β)/3<1. Choose η small enough to absorb the logarithm "
                    + "and fit the requested final slack.")),
                Paragraph(Text("Integrate the density with the factor exp(−(1/2−1/q)u) "
                    + "between log a and log B. The original endpoint gap is retained "
                    + "and vanishes when B=a. The constants are uniform in m, a and B. "
                    + "The argument places no lower bound on the size of the signed residual."))),
            DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, string domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), F.Seq(F.Mathbb, F.Grp(F.Id(domain))), body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

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
        var beta = F.Id("beta");
        var p = F.Id("P");
        var n = F.Id("N");
        var exponent = Add(new Formula.Fraction(Add(F.D(2), beta), F.D(3)), epsilon);
        var coefficient = Multiply(k, new Formula.Power(m, exponent));
        var bound = Le(new Formula.Absolute(residual), Multiply(coefficient, gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var constants = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(And(Le(F.D(2), t), positive), orders)));
        var prefix = new Formula.FunctionCall(FormulaIdentifier.Create("M"), [n]);
        var prefixBound = Le(new Formula.Absolute(prefix), Multiply(p, new Formula.Power(n, beta)));
        var allPrefixes = Bind(FormulaQuantifier.ForAll, "N", "N",
            Imp(Le(F.D(1), n), prefixBound));
        var assumptions = And(And(Le(F.D(0), beta), Lt(beta, F.D(1))),
            And(And(Lt(F.D(0), p), Lt(F.D(0), epsilon)), allPrefixes));
        return F.Disp(Imp(F.Id("RH"),
            Bind(FormulaQuantifier.ForAll, "beta", "R",
                Bind(FormulaQuantifier.ForAll, "P", "R",
                    Bind(FormulaQuantifier.ForAll, "epsilon", "R", Imp(assumptions, constants))))));
    }
}
