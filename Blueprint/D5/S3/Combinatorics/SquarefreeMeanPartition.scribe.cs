using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class SquarefreeMeanPartitionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/SquarefreeMeanPartition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/wiseman2023a360070");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A squarefree number above one has no partition whose parts and whose multiplicities share "
            + "a mean, because squarefreeness turns the mean condition into a count of distinct "
            + "parts that exceeds the count of parts unless every multiplicity is one.",
        H("Squarefree Numbers Have No Partition Whose Parts and Multiplicities Agree in Mean"),
        Blocks(
            Node("the-conjectured-exclusion", "The conjectured exclusion", "claim", ClaimFormula(),
                "A partition is presented by its set of distinct parts together with a "
                    + "multiplicity function. The mean of the parts is the total divided by the "
                    + "number of parts, and the mean of the multiplicities is the number of parts "
                    + "divided by the number of distinct parts. Equating them and clearing "
                    + "denominators gives the total times the number of distinct parts equal to "
                    + "the square of the number of parts; both denominators are positive for a "
                    + "partition of a positive number, so nothing is lost and the statement stays "
                    + "inside the naturals. The bound above one is the source's own, and it is "
                    + "needed: at one the single-part partition has both means equal to one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-exclusion-holds", "The exclusion holds", "result", ResultFormula(),
                "Squarefreeness enters once. The total divides the square of the number of parts, "
                    + "so for a squarefree total it divides the number of parts; write the "
                    + "quotient. Substituting and cancelling the positive total leaves the number "
                    + "of distinct parts equal to the total times the square of that quotient. "
                    + "Every multiplicity is at least one, so the distinct parts are at most as "
                    + "many as the parts, which forces the quotient to be one, and then the "
                    + "number of parts and the number of distinct parts both equal the total. "
                    + "Those two being equal forces every multiplicity to be exactly one, so the "
                    + "total is the sum of that many distinct positive parts; one of them "
                    + "exceeding one would push the sum past the total, so every part is one, so "
                    + "the distinct parts number at most one, against their number being the "
                    + "total, which exceeds one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("squarefree-mean-partition"),
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

    private static Formula Parts(Formula y) => Apply(F.Id("parts"), y);

    private static Formula Distinct(Formula y) => Apply(F.Id("distinct"), y);

    private static Formula Total(Formula y) => Apply(F.Id("total"), y);

    private static Formula Partitions(Formula n) =>
        Seq(F.Id("Partitions"), Open, n, Close);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var y = F.Id("y");
        var hyp = And(Seq(F.Id("squarefree"), Sp, n), Less(D(1), n));
        var unequal = NotEqual(Multiply(Total(y), Distinct(y)),
            new Formula.Power(Parts(y), D(2)));
        return Universal("n", Naturals(),
            Implies(hyp, Universal("y", Partitions(n), unequal)));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

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
