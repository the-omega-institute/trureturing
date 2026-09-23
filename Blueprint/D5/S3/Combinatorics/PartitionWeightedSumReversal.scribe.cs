using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class PartitionWeightedSumReversalDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/PartitionWeightedSumReversal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/wiseman2023a362559");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversing a partition leaves the divisibility of its weighted sum by the total "
            + "unchanged, because the weighted sum of a list and of its reverse add to one more "
            + "than the length times the total.",
        H("Reversal and the Weighted Sum of a Partition"),
        Blocks(
            Node("weighted-sum", "The one-based weighted sum", "weightedSum",
                WeightedSumFormula(),
                "The weight of a position is its one-based index, so the first entry carries "
                    + "weight one. Written without indices, adding an entry at the front "
                    + "contributes that entry once and raises every later weight by one, which "
                    + "is the total of the remaining entries. The source entry records the same "
                    + "quantity as the sum of the partial sums of the reverse.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("partitions", "Partitions of a total", "IsPartition", PartitionFormula(),
                "A partition of a natural number is a weakly decreasing list of positive "
                    + "naturals with that total. The presentation matters only for the reading "
                    + "of the word reverse; the argument below uses neither the decrease nor the "
                    + "positivity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjectured-equivalence", "The conjectured equivalence", "claim",
                ClaimFormula(),
                "The source asserts that a partition of a number has weighted sum divisible by "
                    + "that number exactly when its reverse does, and leaves the assertion "
                    + "unjudged on two of its entries.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("equivalence-holds", "The equivalence holds", "result", ResultFormula(),
                "One identity carries everything: the weighted sum of a list and the weighted "
                    + "sum of its reverse add to one more than the length times the total. "
                    + "Reindexing the reversed sum sends the weight at a position to its "
                    + "complement, so the two weights at each entry add to one more than the "
                    + "length, and the entry-wise sum is that constant times the total. On a "
                    + "partition the total is the modulus, so the right-hand side is a multiple "
                    + "of it and the two weighted sums are congruent up to sign. Formally the "
                    + "identity follows from appending a single entry, which adds that entry "
                    + "weighted by one more than the current length, applied along the "
                    + "recursion for the reverse. Neither the decrease of the parts nor their "
                    + "positivity is used, so the hypothesis carries the correspondence to the "
                    + "source sentence and nothing else.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("partition-weighted-sum-reversal"),
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

    private static Formula Weighted(Formula x) => Apply(F.Id("W"), x);

    private static Formula Total(Formula x) => Apply(F.Id("sum"), x);

    private static Formula Reverse(Formula x) => Apply(F.Id("reverse"), x);

    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);

    private static Formula WeightedSumFormula()
    {
        var x = F.Id("x");
        var t = F.Id("t");
        var head = Seq(F.Id("cons"), Sp, x, Sp, t);
        return Disp(Equal(Weighted(head), Add(Add(x, Weighted(t)), Total(t))));
    }

    private static Formula PartitionSet(Formula n) =>
        Seq(F.Id("Partition"), Open, n, Close);

    private static Formula PartitionFormula()
    {
        var n = F.Id("n");
        var y = F.Id("y");
        var body = And(And(Seq(F.Id("decreasing"), Sp, y), Seq(F.Id("positive"), Sp, y)),
            Equal(Total(y), n));
        return Disp(Equal(PartitionSet(n),
            Seq(OpenBrace, y, Sp, Mid, Sp, body, CloseBrace)));
    }

    private static Formula Statement()
    {
        var n = F.Id("n");
        var y = F.Id("y");
        return Universal("n", Naturals(),
            Universal("y", PartitionSet(n),
                Iff(Divides(n, Weighted(y)), Divides(n, Weighted(Reverse(y))))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
