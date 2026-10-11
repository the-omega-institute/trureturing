using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class GA2ForcedPrimeSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/GA2ForcedPrimeSource.";
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R(Formula n) => new Formula.Apply(F.Id("R"), [n]);
    private static Formula C(Formula n) => new Formula.Apply(F.Id("C"), [n]);
    private static Formula Logarithm(Formula x) => new Formula.Apply(Log, [x]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula ExistsNat(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Divides(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Leq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Conj(params Formula[] xs) =>
        xs.Aggregate((x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual GA2 witness yields an attained Robin maximum on every divisible forced base.",
        H("Actual Robin Maxima on Forced Multiples"),
        Blocks(
            Paragraph(Text("For positive integers n at least three, R(n) is the existing "
                + "robinRatio(n) = sigma_1(n)/(exp(gamma)*n*log(log(n))). Thus "
                + "G(n) = exp(gamma)*R(n), with gamma the Euler constant. The fixed "
                + "positive scalar cancels from GA2, maximization, and the tail bound. "
                + "C(q) denotes actualGA2(q). All logarithms are real natural logarithms.")),
            Describe.Lean(
                DescribeId.Create("actual-ga2"), DeclarationHandle.Create(Prefix + "actualGA2"),
                H("All positive multipliers"), StatementSource.FromAuthor(Ga2Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The condition includes q >= 3, so every tested "
                    + "integer aq has positive log(log(aq)). It compares the literal "
                    + "divisor-sum objective for every natural multiplier a >= 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-ga2-tail-envelope"),
                DeclarationHandle.Create(Prefix + "robinRatio_le_ga2_tail_envelope"),
                H("The lcm tail envelope"), StatementSource.FromAuthor(TailStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any integer n >= 3 and actual GA2 integer q, "
                        + "the inequality holds even when n is not a multiple of q. "
                        + "Every denominator is positive.")),
                    Paragraph(Text("Put L = lcm(q,n). The reciprocal divisor-sum "
                        + "identity from GoldenResourceOptimalInteger and inclusion of "
                        + "divisor sets give sigma_1(n)/n <= sigma_1(L)/L. Since q "
                        + "divides L, actual GA2 bounds R(L) by R(q). Finally L <= q*n, "
                        + "logarithmic monotonicity and log(1+t) <= t give the displayed "
                        + "explicit envelope. Its correction tends to zero as n tends "
                        + "to infinity with q fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("attained-actual-maximum-on-multiples"),
                DeclarationHandle.Create(Prefix + "exists_robin_maximizer_multiple_of_ga2"),
                H("Attainment on the entire multiples domain"),
                StatementSource.FromAuthor(AttainmentStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The base m is any natural integer at least three. "
                        + "It divides the supplied actual GA2 integer q. There exists "
                        + "N >= m divisible by m, with R(N) >= R(q), itself actual GA2, "
                        + "and maximizing R over every positive multiple of m.")),
                    Paragraph(Text("If no multiple improves q, choose q. Otherwise a "
                        + "strictly better multiple and the explicit vanishing envelope "
                        + "bound all sufficiently large integers strictly below that "
                        + "witness. A finite maximum below this derived cutoff is then "
                        + "a maximum on the entire infinite domain. Every positive "
                        + "multiple of N remains a multiple of m, giving actual GA2(N). "
                        + "All maximizing ties are allowed. The fixed-price maximum in "
                        + "GoldenFutureExtensionMaximum concerns a different objective.")),
                    Paragraph(Text("This proves actual attainment without assuming an "
                        + "unbounded GA2 supplier, RH failure, or an analytic prime estimate. "
                        + "The subsequent own-price insertion and permitted deletion "
                        + "thresholds, lcm inventory characterization, forced 5040p "
                        + "singleton accounting and uniform activation-loss estimate "
                        + "remain separate obligations. The exact finite lcm comparison "
                        + "must retain its same-integer terminal clock and all defect terms. "
                        + "The same-source signed Tpsi lower budget and formal U/GM "
                        + "suppliers are unresolved; the full RH/Robin/5040 inequality "
                        + "remains unproved.")),
                    Paragraph(Text("The completed ordinary audit is a design input, not "
                        + "a fresh adjudication of this implementation. The mathematical "
                        + "module and its retained Reg mirror have passed scoped Lean "
                        + "compilation using only propext, Classical.choice and Quot.sound. "
                        + "The Reg mirror supplies the complete law equivalence, variation, "
                        + "whole-family sensitivity and observational dependence proofs. "
                        + "Raw source-occurrence binding is explicitly unfinished; no "
                        + "declared_validated registration is claimed. These checks cover "
                        + "this increment and its imports, "
                        + "not the whole repository or the full RH goal."))),
                DescribeRole.Theorem))));

    private static Formula Ga2Statement()
    {
        Formula q = F.Id("q"), a = F.Id("a");
        return Disp(All("q", Iff(C(q),
            Conj(Leq(D(3), q), All("a", Implies(Leq(D(1), a),
                Leq(R(Mul(a, q)), R(q))))))));
    }

    private static Formula TailStatement()
    {
        Formula q = F.Id("q"), n = F.Id("n");
        Formula correction = new Formula.Fraction(Logarithm(q),
            Mul(Logarithm(n), Logarithm(Logarithm(n))));
        return Disp(All("q", All("n", Implies(Conj(C(q), Leq(D(3), n)),
            Leq(R(n), Mul(R(q), Add(D(1), correction)))))));
    }

    private static Formula AttainmentStatement()
    {
        Formula m = F.Id("m"), q = F.Id("q"), x = F.Id("N"), n = F.Id("n");
        Formula maximality = All("n", Implies(Leq(D(1), n),
            Implies(Divides(m, n), Leq(R(n), R(x)))));
        return Disp(All("m", All("q", Implies(Conj(Leq(D(3), m), Divides(m, q), C(q)),
            ExistsNat("N", Conj(Leq(m, x), Divides(m, x),
                Leq(R(q), R(x)), C(x), maximality))))));
    }
}
