using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusInverseLogDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse logarithmic rate for the Möbius prime window",
        H("A rate from the actual separation of the degree samples"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-inverse-log"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_inverse_log_of_rh"),
            H("Inverse logarithmic saving"),
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
                Paragraph(Text("Put q=m+1, u=log x, and L=1+log(q)/16. The zero-free "
                    + "half-plane estimate with θ=1/2 and α=1/4 bounds every ordinary Möbius "
                    + "prefix up to m by a constant times m^(3/4). Signed Abel summation with "
                    + "the omitted degrees gives a near-range coefficient of order "
                    + "exp(2L) m^(3/4) when u≤Lq. Since exp(2L)=exp(2) q^(1/8), "
                    + "this fits m/log q.")),
                Paragraph(Text("The same prefix bound controls the signed trivial-zero "
                    + "response by a constant times m^(3/4)(1+log m). The constant term and "
                    + "the loss from omitting μ(1) fit the same inverse logarithmic budget.")),
                Paragraph(Text("For u≥Lq the actual sample spacing bounds the omitted "
                    + "nontrivial spectrum by a constant times 1+q²/u+q^(7/8), after extracting "
                    + "exp(−(1/2−1/q)u). This coefficient is also of order m/log q. The "
                    + "signed arithmetic tail has the same coefficient.")),
                Paragraph(Text("Integrating the density estimate between log a and log B "
                    + "yields the endpoint power difference with a single threshold for all "
                    + "m≥2. Equal endpoints give zero."))),
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
        var scale = F.Seq(F.Log, F.Sp, F.Open, Add(m, F.D(1)), F.Close);
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
