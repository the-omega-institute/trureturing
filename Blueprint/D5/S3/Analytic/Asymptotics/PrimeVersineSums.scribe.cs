using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PrimeVersineSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Asymptotics/PrimeVersineSums.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For sigma >= 0 the series of 1 - cos p^(-sigma) over the primes converges exactly when sigma > 1/2, and its difference from half the series of p^(-2 sigma) converges exactly when sigma > 1/4, with partial sums tending to minus infinity for sigma <= 1/4; on the line sigma = 1/2 the versine sum up to x differs from half the sum of the reciprocals of the primes up to x by a quantity within 5/(48 (floor(x) + 1)) of its limit.",
        H("Versine sums over the primes"),
        Blocks(
            Paragraph(Text(
                "P denotes the set of primes. For real sigma and x, the versine sum is the finite sum "
                + "of 1 - cos(p^(-sigma)) over the primes p in the interval (0, floor(x)], where "
                + "floor(x) is the natural-number floor of x, so the sum is empty for x < 2. For "
                + "sigma >= 0 the argument t = p^(-sigma) satisfies 0 < t <= 1.")),
            Node("definition", "primeVersineSum", "The versine sum over the primes up to x",
                StatementSource.FromAuthor(DefinitionFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Definition,
                "primeVersineSum(sigma, x) is the sum of 1 - cos(p^(-sigma)) over the primes p with "
                + "p <= floor(x), where p^(-sigma) is the real power of the real number p."),
            Node("phases", "prime_versine_phases", "Thresholds and the critical line",
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                DescribeRole.Theorem,
                "In the display, Summable(p in P, f(p)) means that the family f indexed by the "
                + "primes is summable, the sum over p in P is the sum of that summable family, "
                + "delta(p) = 1/(2p) - (1 - cos(p^(-1/2))), and the limit of minus infinity is taken "
                + "as the real variable x tends to plus infinity. "
                + "The theorem has four conjuncts. For sigma >= 0, the series of 1 - cos(p^(-sigma)) "
                + "over the primes is summable if and only if sigma > 1/2. For sigma >= 0, the series "
                + "of 1 - cos(p^(-sigma)) - p^(-2 sigma)/2 is summable if and only if sigma > 1/4. "
                + "For 0 <= sigma <= 1/4, the versine sum up to x minus half the sum of p^(-2 sigma) "
                + "over the primes up to x tends to minus infinity. For every real x, the difference "
                + "between half the sum of 1/p over the primes up to x and the versine sum at "
                + "sigma = 1/2 lies between the sum of delta over all primes minus "
                + "5/(48 (floor(x) + 1)) and that sum.",
                "Put t = p^(-sigma), so 0 < t <= 1. The Mathlib bounds 1 - t^2/2 <= cos t and "
                + "|cos t - (1 - t^2/2)| <= 5 t^4/96 for |t| <= 1 give "
                + "(43/96) t^2 <= 1 - cos t <= t^2/2, so the first series converges exactly when the "
                + "series of p^(-2 sigma) over the primes does, which by Mathlib happens exactly "
                + "when -2 sigma < -1. "
                + "The second and third conjuncts rest on the lower bound "
                + "t^4/30 <= cos t - (1 - t^2/2) for |t| <= 1, proved here from the half-angle "
                + "identity cos t = 1 - 2 sin^2(t/2), the Mathlib fifth-order bound for the sine and a "
                + "polynomial inequality. The summand of the second series is minus this fourth-order "
                + "defect, which lies between t^4/30 and 5 t^4/96; so the second series converges "
                + "exactly when the series of p^(-4 sigma) does, that is when sigma > 1/4. For "
                + "sigma <= 1/4 the defect series has nonnegative terms and diverges, so its partial "
                + "sums tend to plus infinity, and the third conjunct follows. "
                + "On the line sigma = 1/2 one has t^2 = 1/p, so delta(p) is the defect at "
                + "t = p^(-1/2), nonnegative and at most 5/(96 p^2). Comparing the tail over n > N of "
                + "5/(96 n^2) with 2/(N + 1) bounds the tail of the defect series beyond N = floor(x) "
                + "by 5/(48 (N + 1)), which is the fourth conjunct.",
                "The hypothesis sigma >= 0 is used to keep t in [0, 1]; at sigma = 0 every term of the "
                + "first two series is a positive constant, in agreement with both equivalences. For "
                + "sigma < 0 the terms do not tend to 0 in any obvious way and the behaviour depends "
                + "on the distribution of p^(-sigma) modulo 2 pi; no claim is made for sigma < 0. Each "
                + "threshold is sharp because it is stated as an equivalence.",
                "Combined with the Mertens estimate Mertens.E₂p.bound, which states that the sum of "
                + "1/p over the primes up to x equals log log x + M + O(1/log x) with the Mertens "
                + "constant M, the fourth conjunct gives, as x tends to infinity, that the sum of "
                + "1 - cos(p^(-1/2)) over the primes up to x equals (log log x)/2 + M/2 minus the sum "
                + "of delta over all primes plus O(1/log x). This consequence is not one of the formal "
                + "statements of this module.",
                "The thresholds are elementary comparisons with the prime zeta series, and the "
                + "explicit tail on the critical line is a comparison with the tail of the series of "
                + "1/n^2; the combination is derived here."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("prime-versine-sums-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks([.. paragraphs.Select(static p => Paragraph(Text(p)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula LeRel(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllSigma(Formula body) =>
        Seq(Forall, Sp, SigmaLower, Sp, InMacro, Sp, Reals, Comma, Sp, body);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Primes => Seq(Mathbb, Grp(F.Id("P")));
    private static Formula P => F.Id("p");
    private static Formula X => F.Id("x");
    private static Formula Sigma => SigmaLower;
    private static Formula Half => Frac(D(1), D(2));
    private static Formula Quarter => Frac(D(1), D(4));
    private static Formula NatFloor => new Formula.Floor(X);

    private static Formula Versine(Formula exponent) =>
        Sub(D(1), Call("cos", Pow(P, exponent)));
    private static Formula MinusSigma => Seq(Minus, Sigma);
    private static Formula MinusTwoSigma => Seq(Minus, D(2), Sigma);
    private static Formula MinusHalf => Seq(Minus, D(1), Slash, D(2));
    private static Formula HalfPower => Frac(Pow(P, MinusTwoSigma), D(2));

    private static Formula SumUpTo(Formula body) => Seq(
        Sum, Underscore, Grp(P, Sp, InMacro, Sp, Open, D(0), Comma, Sp, NatFloor, CloseBracket,
            Comma, Sp, P, Sp, F.Text, Grp(F.Id("prime"))),
        Sp, Open, body, Close);
    private static Formula SumOverPrimes(Formula body) => Seq(
        Sum, Underscore, Grp(P, Sp, InMacro, Sp, Primes), Sp, body);
    private static Formula Summable(Formula body) =>
        Call("Summable", Seq(P, Sp, InMacro, Sp, Primes, Comma, Sp, body));
    private static Formula VersineSum(Formula sigma) => Call("primeVersineSum", sigma, X);
    private static Formula Delta => Seq(DeltaLower, Open, P, Close);

    private static Formula DefinitionFormula() => Disp(ForAllSigma(ForAll("x", Reals,
        Equal(VersineSum(Sigma), SumUpTo(Versine(MinusSigma))))));

    private static Formula TheoremFormula()
    {
        Formula nonnegative = LeRel(D(0), Sigma);
        Formula first = ForAllSigma(Implies(nonnegative,
            Iff(Summable(Versine(MinusSigma)), Lt(Half, Sigma))));
        Formula second = ForAllSigma(Implies(nonnegative,
            Iff(Summable(Sub(Versine(MinusSigma), HalfPower)), Lt(Quarter, Sigma))));
        Formula limit = Seq(Lim, Underscore, Grp(X, Sp, To, Sp, Infty), Sp,
            Open, Sub(VersineSum(Sigma), SumUpTo(HalfPower)), Close);
        Formula third = ForAllSigma(Implies(nonnegative, Implies(LeRel(Sigma, Quarter),
            Equal(limit, Seq(Minus, Infty)))));
        Formula gap = Sub(SumUpTo(Frac(D(1), Mul(D(2), P))), VersineSum(Half));
        Formula total = SumOverPrimes(Delta);
        Formula tail = Frac(D(5), Seq(D(4, 8), Open, Add(NatFloor, D(1)), Close));
        Formula fourth = ForAll("x", Reals, Seq(Sub(total, tail), Sp, F.Le, Sp, gap, Sp, F.Le, Sp,
            total));
        Formula deltaDefinition = Seq(
            Equal(Delta, Sub(Frac(D(1), Mul(D(2), P)), Versine(MinusHalf))), Comma, Quad, RowBreak);
        return Disp(Seq(
            deltaDefinition,
            Open, first, Close, Sp, Land, RowBreak,
            Open, second, Close, Sp, Land, RowBreak,
            Open, third, Close, Sp, Land, RowBreak,
            fourth));
    }
}
