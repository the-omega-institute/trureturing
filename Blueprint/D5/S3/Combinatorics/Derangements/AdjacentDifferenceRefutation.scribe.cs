using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Derangements;

internal sealed class AdjacentDifferenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/kagey2024a378495");
    private static readonly LibraryNoteRef Sequence =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lang2014a238474");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal adjacent-column identity with the zero-based index n-4 fails at n=5: the actual cardinality difference is twenty and the absolute sequence value is six.",
        H("A Counterexample to the Literal Adjacent Difference"),
        Blocks(
            Node("sequence", "The zero-based auxiliary sequence", "b",
                "For every natural m, b(m) is (-1)^m times (m+3)! divided by 2(m+1), computed in the rationals. The factorial and m+1 are first computed in the natural numbers and then cast. The denominator is nonzero for every m >= 0. This is the formula of A238474 with offset zero: b(0)=-1 to the zeroth power times 3! divided by two, hence three, and b(1)=-6. The exponent uses the rational number minus one, rather than natural truncated subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Sequence)),
            Node("literal-claim", "The literal adjacent-column conjecture", "claim",
                "The proposition claim asserts that for every natural n with 4 <= n, T(n,n-1)-T(n,n-2) equals the absolute value of b(n-4). Here T is the cardinality of all permutations of Fin n with no fixed point and no cycle factor of the forbidden length. Each cardinality is cast to the rationals before ordinary subtraction; the absolute value is rational. Every index subtraction is natural subtraction, and the hypothesis ensures that n-4 has its ordinary nonnegative meaning. The shift is exactly n-4, with no change of the zero offset of b and no upper bound on n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("literal-refutation", "Five labels contradict the asserted equality", "result",
                "The proposition claim is false. At n=5, a derangement cannot contain a 4-cycle: the remaining label would be fixed. Thus excluded(5,4) is empty, whereas the cycle type (3,2) contributes exactly 5!/(2 times 3)=20 excluded permutations at length three. Applying the complementary-count identities to the same derangement set gives T(5,4)=T(5,3)+20 and hence the rational difference twenty. The source sequence has b(5-4)=b(1)=-6, whose absolute value is six. Since 20 differs from 6 and five satisfies the stated lower bound, this one exact counterexample negates the whole universal proposition. It does not assert a replacement formula or negate the separate terminal-column identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a378495-adjacent-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromLean(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
