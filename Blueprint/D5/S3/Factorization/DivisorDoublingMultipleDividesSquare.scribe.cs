using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class DivisorDoublingMultipleDividesSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/DivisorDoublingMultipleDividesSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/lowell2013a225004");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A multiple whose divisor count stays below twice that of the original divides its square, "
            + "because one prime exponent exceeding twice its original value, or one new prime, "
            + "already doubles the divisor count on its own.",
        H("A Multiple with Fewer than Twice as Many Divisors Divides the Square"),
        Blocks(
            Node("the-conjectured-divisibility", "The conjectured divisibility", "claim",
                ClaimFormula(),
                "The source names, for each number, the largest of its multiples whose divisor "
                    + "count stays below twice its own, and asserts that this largest multiple "
                    + "divides the square. Recorded here is the statement for every such multiple, "
                    + "not only the largest. Naming the largest one needs a bound on how far to "
                    + "look, and the only natural bound is the square itself, so a literal rendering "
                    + "would assume what is to be shown. The form below contains the assertion "
                    + "and shows in addition that these multiples are finitely many, so the "
                    + "largest exists.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("divisibility-holds", "The divisibility holds", "result", ResultFormula(),
                "The divisor count is the product over the primes of one more than each exponent, "
                    + "and divisibility by the square is the pointwise bound of each exponent by "
                    + "twice its original. Suppose one prime broke that bound. If it is a prime of "
                    + "the multiple only, split the product at the boundary between the original "
                    + "primes and the rest: the first part is already at least the original count "
                    + "factorwise, and the second contains a factor of at least two at the "
                    + "offending prime. If it is a prime of both, then one more than its exponent "
                    + "in the multiple is at least twice one more than its exponent in the "
                    + "original, so pulling that prime out of the product supplies the factor of "
                    + "two while every remaining factor is at least its counterpart. Either way "
                    + "the divisor count of the multiple reaches twice the original, against the "
                    + "hypothesis. So no prime breaks the bound and the divisibility follows.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("divisor-doubling-multiple-divides-square"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);

    private static Formula Tau(Formula x) => Apply(F.Id("tau"), x);

    private static Formula Divides(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Divides, b);

    private static Formula Square(Formula x) => Multiply(x, x);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var hyp = And(Divides(n, m),
            Less(Tau(m), Multiply(D(2), Tau(n))));
        return Universal("n", Naturals(),
            Universal("m", Naturals(),
                Implies(hyp, Divides(m, Square(n)))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
