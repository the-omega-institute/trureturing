using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEightNinthsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEightNinths";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eight-ninths exponent for the Möbius prime window",
        H("Uniform variation of the exponentially damped degree modes"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-eight-ninths"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_eight_ninths_of_rh"),
            H("The signed prime-window estimate with positive exponent slack"),
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
                Paragraph(Text("Put q=m+1 and u=log x. For each ε>0 choose "
                    + "η=min(ε/2,1/36). The RH ordinary Möbius prefix bound has exponent "
                    + "β=2/3+η. It controls the signed arithmetic tail and the omitted "
                    + "centered response up to u=q. The trivial-root response costs "
                    + "O(q^β(1+log q)).")),
                Paragraph(Text("For u≥q, write vₙ=u/n and E(v)=exp(−u/q+v/2). "
                    + "In the difference of adjacent modes, the phase increment comes with "
                    + "E(vₙ₊₁), so E(vₙ₊₁)(vₙ−vₙ₊₁)≤2(E(vₙ)−E(vₙ₊₁)). "
                    + "The envelope telescopes and bounds the mode variation by "
                    + "O((1+|Im ρ|)/|ρ|) for every u.")),
                Paragraph(Text("The local logarithmic zero count gives an inverse-root bin "
                    + "mass of order (1+|k|)^(η−1). Finite complex Abel summation at low bins "
                    + "costs O(q^β(H+1)^(1+η)). Squaring and summing the high bin masses "
                    + "and applying weighted sampling costs O(qH^(η−1/2)). Balancing "
                    + "the two terms at H=floor(q^(2(1−β)/3)) gives the general window "
                    + "exponent (2+β)/3 with positive slack. With the stated β and "
                    + "remaining slack ε−η/3, the exponent is 8/9+ε.")),
                Paragraph(Text("Integrate the normalized density estimates with the factor "
                    + "exp(−(1/2−1/q)u) between log a and log B. The endpoint gap vanishes "
                    + "for B=a. The constants are uniform in the order and the two endpoints "
                    + "for each fixed ε."))),
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
        var exponent = Add(new Formula.Fraction(F.D(8), F.D(9)), epsilon);
        var coefficient = Multiply(k, new Formula.Power(m, exponent));
        var bound = Le(new Formula.Absolute(residual), Multiply(coefficient, gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var constants = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(And(Le(F.D(2), t), positive), orders)));
        var slack = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, epsilon);
        return F.Disp(Imp(F.Id("RH"),
            Bind(FormulaQuantifier.ForAll, "epsilon", "R", Imp(slack, constants))));
    }
}
