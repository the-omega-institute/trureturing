using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RHMobiusWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-only window at an arbitrary Möbius truncation order",
        H("One real threshold for every truncation order"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-mobius-prime-window"),
            DeclarationHandle.Create(Owner + ".prime_window_mobius_of_rh"),
            H("Deterministic and spectral contributions on the same window"),
            StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E(m,a,B) be the signed residual. Start with the integral of the "
                    + "negative part of the prime-only tail divided by sqrt(x) on [a,B]. "
                    + "Subtract 2 log(B/a) and the ordinary spectral primitive at B minus its value at a. "
                    + "For 3 ≤ n ≤ m subtract the endpoint power difference of exponent 1/n − 1/2 "
                    + "with coefficient −2μ(n)n²/((n−1)(n−2)). For 2 ≤ n ≤ m with 2n < m+1 "
                    + "subtract −μ(n) times the nth root primitive at B minus its value at a. "
                    + "Every primitive uses the same actual zero occurrences with multiplicity.")),
                Paragraph(Text("A finite Möbius truncation produces an arithmetic error whose density constant "
                    + "grows at most linearly in m. Continuity of the complete-tail residual on [1,2] "
                    + "extends its existing inverse-power bound to every root argument at least one. "
                    + "The resulting centered root error is bounded by a constant times n x^(-1/2). "
                    + "Each omitted spectral density has size at most a constant times n "
                    + "times x^(1/(2n) − 1/2), which is within the target rate when 2n ≥ m+1.")),
                Paragraph(Text("Summing the errors gives a density bound with a constant times m². "
                    + "Integration over [log a, log B] preserves both endpoints. "
                    + "The rate s(m)=1/2 − 1/(m+1) lies above or at 1/6, so integration keeps one "
                    + "constant for all m. The inequality includes B=a.")),
                Paragraph(Text("At m=10 the eighth and ninth deterministic terms vanish. "
                    + "The tenth term has coefficient −25/9 and the fifth-root primitive enters "
                    + "at the same scale, with remaining decay exponent 9/22."))),
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
        var bound = Le(new Formula.Absolute(residual), Multiply(Multiply(k, new Formula.Power(m, F.D(2))), gap));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        var windows = Bind(FormulaQuantifier.ForAll, "a", "R",
            Bind(FormulaQuantifier.ForAll, "B", "R", Imp(And(Le(t, a), Le(a, b)), bound)));
        var orders = Bind(FormulaQuantifier.ForAll, "m", "N", Imp(Le(F.D(2), m), windows));
        var parameters = Bind(FormulaQuantifier.Exists, "T", "R",
            Bind(FormulaQuantifier.Exists, "K", "R", And(Le(F.D(2), t), And(positive, orders))));
        return F.Disp(Imp(F.Id("RH"), parameters));
    }
}
