using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class OeisA394407TotientTauPrimesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/OeisA394407TotientTauPrimes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/huber2026a394407");
    private const string SequenceQuotation =
        "Positive integers k such that there is no m < k with phi(m)/tau(m) = phi(k)/tau(k).";
    private const string ConjectureQuotation =
        "Conjecture: All primes p != 3 are in the sequence; equivalently, for every prime p != 3 "
        + "there is no m < p with phi(m)/tau(m) = phi(p)/tau(p) = (p - 1)/2; equivalently, "
        + "the sequence is a supersequence of A045344.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime other than three first attains its totient-to-divisor-count ratio.",
        H("Huber's Prime Conjecture for OEIS A394407"),
        Blocks(
            Paragraph(Text("The variables k, m and p are natural numbers. Nat.totient is Euler's "
                + "totient, Nat.divisors is the finite set of positive divisors, and Finset.card "
                + "counts those divisors. Both operands of division are explicitly cast to Q, "
                + "so division is rational division. The sequence concerns positive integers.")),
            Node("ratio", "The totient-to-divisor-count ratio", RatioFormula(),
                "OEIS A394407, unpaginated Name line: \"" + SequenceQuotation + "\" "
                + "The expression phi(m)/tau(m) is the quotient of Nat.totient m and "
                + "Finset.card (Nat.divisors m), each cast to Q. The total function also "
                + "has value zero at m = 0; the sequence uses only positive inputs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsTerm", "First occurrence of a ratio", IsTermFormula(),
                "OEIS A394407, unpaginated Name line: \"" + SequenceQuotation + "\" "
                + "IsTerm k requires k > 0 and compares its ratio with every positive m < k. "
                + "The domain of m follows the positive-integer sequence and its examples.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Huber's conjecture", Equal(Named("claim"), Parenthesized(ClaimBody())),
                "OEIS A394407, unpaginated Comment line: \"" + ConjectureQuotation + "\" "
                + "Nat.Prime p and p != 3 are the two hypotheses; IsTerm p expresses "
                + "membership by the positive-integer first-occurrence condition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every prime other than three is a term", ClaimBody(),
                "For a prime p the divisor set is {1, p}, so its ratio is (p - 1)/2. "
                + "If m = 1, equality with that ratio forces p = 3. If 2 <= m < p, "
                + "Nat.totient m < m and there are at least two positive divisors, giving "
                + "ratio m <= Nat.totient m / 2 < (p - 1)/2. These cases exclude every "
                + "smaller positive m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a394407-" + (name == "IsTerm" ? "is-term" : name)),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula name, params Formula[] arguments) => new Formula.Apply(name, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rationals()));
    private static Formula All(string name, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula RatioFormula()
    {
        Formula m = F.Id("m");
        Formula numerator = Cast(Call(Qualified("Nat", "totient"), m));
        Formula denominator = Cast(Call(Qualified("Finset", "card"), Call(Qualified("Nat", "divisors"), m)));
        return All("m", Equal(Call(Named("ratio"), m), new Formula.Fraction(numerator, denominator)));
    }

    private static Formula IsTermFormula()
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula distinct = NotEqual(Call(Named("ratio"), m), Call(Named("ratio"), k));
        Formula firstOccurrence = All("m", Implication(Less(D(0), m), Implication(Less(m, k), distinct)));
        return All("k", Equal(Call(Named("IsTerm"), k), Parenthesized(And(Less(D(0), k), firstOccurrence))));
    }

    private static Formula ClaimBody()
    {
        Formula p = F.Id("p");
        return All("p", Implication(Call(Qualified("Nat", "Prime"), p),
            Implication(NotEqual(p, D(3)), Call(Named("IsTerm"), p))));
    }
}
