using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class RHMobiusLinearDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear remainder bound for the Möbius prime window",
        H("Signed summation and sampled root spectra"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-linear"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_linear_of_rh"),
            H("A linear factor for every truncation order"),
            StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E(m,a,B) be the signed residual. Start with the integral of the "
                    + "negative part of the prime-only tail divided by sqrt(x) on [a,B]. "
                    + "Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. "
                    + "For 3 ≤ n ≤ m subtract the endpoint power difference of exponent 1/n − 1/2 "
                    + "with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 "
                    + "subtract −μ(n) times the nth root primitive at B minus its value at a. "
                    + "Every primitive uses the same actual zero occurrences with multiplicity.")),
                Paragraph(Text("The identity μ(n) log n = −(μ∗Λ)(n) and the Chebyshev bound "
                    + "under RH give a logarithmic saving for the Möbius partial sums. Abel summation "
                    + "then bounds the signed sum of the trivial-zero responses by a constant times "
                    + "m. Each positive summand of the response increases with the degree, and the "
                    + "sum at the last degree is bounded by a harmonic number.")),
                Paragraph(Text("Write u=log x and q=m+1. For u≤q, the integrated Chebyshev estimate "
                    + "bounds each omitted centered root term at the target decay rate. For u≥q, "
                    + "group the samples u/n by unit intervals in 2u/q−u/n. The local mean square "
                    + "of a finite zero sum is bounded by the squares of its unit frequency bin masses. "
                    + "The Gaussian Fourier integral supplies a summable kernel in the bin difference. "
                    + "The signed unit zero count ensures square summability with analytic multiplicity.")),
                Paragraph(Text("The sample spacing is at least 1/q. On a unit interval the sampling "
                    + "bound controls the sum of the absolute values using the local integrals of the "
                    + "finite series and its derivative. Telescope over adjacent degrees to accommodate "
                    + "the varying coefficients. Their increments have size of order 1/q relative "
                    + "to the common bin majorant. Each band contributes at most a constant times q "
                    + "before its geometric weight, including the first band at zero exponent slack. "
                    + "Absolute convergence for each sample passes the bound to the full series.")),
                Paragraph(Text("The pointwise bound integrates over [log a, log B]. The rate "
                    + "s(m)=1/2−1/(m+1) is at least 1/6. The constant from integration is "
                    + "therefore uniform in m. Both sides vanish at B=a."))),
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
        var bound = Le(new Formula.Absolute(residual), Multiply(Multiply(k, m), gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var parameters = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(Le(F.D(2), t), And(positive, orders))));
        return F.Disp(Imp(F.Id("RH"), parameters));
    }
}
