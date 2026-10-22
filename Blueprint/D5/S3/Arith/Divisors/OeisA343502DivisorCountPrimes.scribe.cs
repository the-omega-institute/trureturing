using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class OeisA343502DivisorCountPrimesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/dequatre2021a343502");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dequatre's OEIS A343502 conjecture: every member except 2 and 3 is composite.",
        H("The OEIS A343502 Divisor-Count Prime Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a343502-membership"),
                DeclarationHandle.Create(Prefix + "InA343502"),
                H("The defining membership condition for A343502"),
                StatementSource.FromAuthor(InA343502Formula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The OEIS entry defines the sequence as numbers k such that "
                        + "tau(tau(k)) and tau(k+1) are both prime, where tau is the "
                        + "number of divisors function. The displayed expression expands "
                        + "tau literally as the cardinality of Nat.divisors and includes "
                        + "the positive-integer condition 1 ≤ k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a343502-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Dequatre's conjecture"),
                StatementSource.FromAuthor(Disp(Equal(Call("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The OEIS comment states verbatim: “Conjecture: all members except "
                        + "2 and 3 are composite.” Here composite is encoded by 1 < k and "
                        + "the negation of Nat.Prime k, while membership retains the "
                        + "positive-index and two-prime conditions above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a343502-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture holds"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Assume k is a member other than 2 or 3. If k were prime, it would "
                            + "be odd, so k + 1 would be even. The prime divisor count of "
                            + "k + 1 forces every prime factor of k + 1 to be 2; hence k + 1 "
                            + "is a power of 2. The exponent is prime, and the primality of "
                            + "the divisor count makes the exponent equal to 2, forcing k = 3, "
                            + "a contradiction.")),
                    Paragraph(Text(
                        "The proof therefore establishes 1 < k and not Nat.Prime k for every "
                            + "remaining member. The separate OEIS question about whether A343502 "
                            + "has finitely many odd terms is not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula InA343502Formula()
    {
        Formula k = F.Id("k");
        Formula tau(Formula n) => CardDivisors(n);
        Formula body = And(
            LessEqual(D(1), k),
            And(
                Call("Prime", tau(tau(k))),
                Call("Prime", tau(Add(k, D(1))))));
        return Disp(Universal("k", Iff(Call("InA343502", k), body)));
    }

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k");
        return Universal("k",
            Implies(Call("InA343502", k),
                Implies(NotEqual(k, D(2)),
                    Implies(NotEqual(k, D(3)),
                        And(Less(D(1), k), new Formula.Not(Call("Prime", k)))))));
    }

    private static Formula CardDivisors(Formula value) =>
        Call("card", Call("divisors", value));

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
