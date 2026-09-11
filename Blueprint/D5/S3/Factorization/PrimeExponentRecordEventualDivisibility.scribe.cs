using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class PrimeExponentRecordEventualDivisibilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimeExponentRecordEventualDivisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive integer divides every sufficiently large strict record of the "
            + "prime-exponent score when the real exponent lies strictly between zero and one.",
        H("Eventual Divisibility of Prime-Exponent Records"),
        Blocks(
            Entry(
                "strict-record-factorization-antitone",
                "strictRecord_factorization_antitone",
                "Prime exponents decrease along the ordered primes",
                AntitoneFormula(),
                "At a strict record, the exponent at a larger prime is at most the exponent "
                    + "at a smaller prime. Otherwise transferring the exponent difference "
                    + "from the larger prime to the smaller one produces a smaller positive "
                    + "integer with the same score. The prime-power theorem uses this order "
                    + "to obtain a uniform exponent bound.",
                DescribeRole.Theorem),
            Entry(
                "eventual-prime-power-divisibility",
                "eventually_prime_power_dvd_records",
                "Every fixed prime power eventually divides the records",
                PrimePowerFormula(),
                "For real 0<x<1 and a fixed prime power p^a, all sufficiently large strict "
                    + "records are divisible by p^a. If the p-exponent is below a, a transfer "
                    + "at each smaller prime combines a positive one-step gain with the "
                    + "fixed-step loss E^x-(E-c)^x, which tends to zero. The exponent order "
                    + "then bounds every prime exponent by a common B. A further bound C "
                    + "excludes prime factors above 2^C, leaving only finitely many records.",
                DescribeRole.Theorem),
            Entry(
                "prime-exponent-record-eventual-divisibility",
                "prime_exponent_record_eventual_divisibility",
                "Every positive integer eventually divides the records",
                MainFormula(),
                "For every real 0<x<1 and every natural d>=1, there is a natural threshold N "
                    + "such that d divides every strict prime-exponent record n>=N. The proof "
                    + "takes the maximum of the prime-power thresholds for the finitely many "
                    + "prime factors of d. The resulting N has no explicit closed form here: "
                    + "the intermediate bounds B and C are extracted from eventual real "
                    + "estimates with Classical.choose, so the proof is nonconstructive.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "OEIS A384669 attributes this conjecture to Hal M. Switkay, dated 2025-06-06. "
                    + "The proofs in this document are repository-derived. No claim of a first "
                    + "proof or of an unresolved present status is made; subsequent literature "
                    + "was not systematically searched.")))));

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        string title,
        Formula formula,
        string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula AntitoneFormula()
    {
        Formula x = F.Id("x"), n = F.Id("n"), p = F.Id("p"), q = F.Id("q");
        Formula hypotheses = And(
            Lt(D(0), x),
            Call("StrictRecord", x, n),
            Call("Prime", p),
            Call("Prime", q),
            Lt(p, q));
        Formula conclusion = Le(
            Call("factorization", n, q),
            Call("factorization", n, p));
        return Disp(ForAll(
            [Bound("x", Reals()), Bound("n", Naturals()),
                Bound("p", Naturals()), Bound("q", Naturals())],
            Implies(hypotheses, conclusion)));
    }

    private static Formula PrimePowerFormula()
    {
        Formula x = F.Id("x"), p = F.Id("p"), a = F.Id("a");
        Formula threshold = EventualDivisibility(Power(p, a));
        return Disp(ForAll(
            [Bound("x", Reals())],
            Implies(Lt(D(0), x),
                Implies(Lt(x, D(1)),
                    ForAll(
                        [Bound("p", Naturals()), Bound("a", Naturals())],
                        Implies(Call("Prime", p), threshold))))));
    }

    private static Formula MainFormula()
    {
        Formula x = F.Id("x"), d = F.Id("d");
        Formula threshold = EventualDivisibility(d);
        return Disp(ForAll(
            [Bound("x", Reals())],
            Implies(Lt(D(0), x),
                Implies(Lt(x, D(1)),
                    ForAll(
                        [Bound("d", Naturals())],
                        Implies(Le(D(1), d), threshold))))));
    }

    private static Formula EventualDivisibility(Formula divisor)
    {
        Formula threshold = F.Id("N"), n = F.Id("n");
        Formula tail = ForAll(
            [Bound("n", Naturals())],
            Implies(
                Le(threshold, n),
                Implies(Call("StrictRecord", F.Id("x"), n), Dvd(divisor, n))));
        return Some([Bound("N", Naturals())], tail);
    }

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Dvd(Formula left, Formula right) =>
        Seq(left, Sp, Mid, Sp, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        }

        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
