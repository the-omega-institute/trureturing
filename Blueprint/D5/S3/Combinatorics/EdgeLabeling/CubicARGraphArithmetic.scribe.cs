using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The additive-triple cardinality and the strict cubic-labeling union bound.",
        H("Counting additive triples for cubic AR labeling"),
        Blocks(
            Node("additivePairs", "The free additive triples", DescribeRole.Definition,
                "The finite set contains the smaller ordered pair of labels in a triple "
                + "a<b<a+b with all labels in the interval from three to m. It is formed "
                + "as disjoint rows indexed by a minus three."),
            Node("mem_additivePairs", "The additive-triple constraints", DescribeRole.Theorem,
                "For m at least six, membership of the pair (a,b) is equivalent to "
                + "three at most a, a less than b, and a+b at most m."),
            Node("four_mul_card_additivePairs_le", "A square upper bound", DescribeRole.Theorem,
                "Four times the number of additive pairs is at most the square of m-5. "
                + "This follows from the rectangular cardinality and the nonnegative "
                + "square of the difference between its side lengths."),
            Node("bad_count_lt_factorial", "The factorial-weighted strict union bound", DescribeRole.Theorem,
                "For m at least twelve, 3n=2m, and 4t at most (m-5)^2, the sum of (m-3)!, "
                + "2(2m-7)(m-4)!, and 6(n-3)t(m-5)! is strictly below (m-2)!. "
                + "Multiply the normalized inequality by the positive factorial (m-5)! "
                + "and use the factorial recurrence.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cubic-ar-arithmetic-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
