using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RHMobiusSingleLogDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single-logarithm bound for the Möbius prime window",
        H("Two estimates on the same omitted root tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window-single-log"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_one_log_of_rh"),
            H("One logarithm for every truncation order"),
            StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E(m,a,B) be the signed residual. Start with the integral of the "
                    + "negative part of the prime-only tail divided by sqrt(x) on [a,B]. "
                    + "Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. "
                    + "For 3 ≤ n ≤ m subtract the endpoint power difference of exponent 1/n − 1/2 "
                    + "with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 "
                    + "subtract −μ(n) times the nth root primitive at B minus its value at a. "
                    + "Every primitive uses the same actual zero occurrences with multiplicity.")),
                Paragraph(Text("The integrated arithmetic truncation contributes at most a constant "
                    + "times m at the target decay rate. The retained root spectra leave a centered "
                    + "trivial-zero error of size (1+log n) times x^(−1/2) per root. For an omitted "
                    + "degree n use both the actual-zero coefficient bound and the Schoenfeld bound "
                    + "integrated through the same centered tail. The latter uses the global Chebyshev "
                    + "bound on rooted arguments between one and the explicit threshold.")),
                Paragraph(Text("Write u=log x, q=m+1, λ=u/q and L=1+log m. After taking out "
                    + "the target decay, the two bounds supply the minimum of (1+2λ)² and L² "
                    + "times exp(−u(1/q−1/(2n))). For n at or above the first omitted degree "
                    + "this weight is at most exp(−λ(n−ceil(q/2))/q). Its sum is at most m and "
                    + "at most 1+q/λ for λ>0. The product with the minimum is at most 24mL. "
                    + "For odd m, the first omitted degree has zero exponent slack and contributes unit weight.")),
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
        var log = F.Seq(F.Log, F.Sp, m);
        var logWeight = Add(F.D(1), log);
        var bound = Le(new Formula.Absolute(residual), Multiply(Multiply(Multiply(k, m), logWeight), gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var parameters = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(Le(F.D(2), t), And(positive, orders))));
        return F.Disp(Imp(F.Id("RH"), parameters));
    }
}
