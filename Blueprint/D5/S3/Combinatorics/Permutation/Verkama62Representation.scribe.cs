using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62RepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Representation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-based notation and the rational bound.",
        H("One-based notation and the rational bound"),
        Blocks(
            Node("verkama62-representation-containsonebased", "Printed classical avoidance", "ContainsOneBased",
                "An occurrence is an increasing embedding of the six positions whose relative value order equals [3,5,1,6,2,4]. The values pi(i).val + 1 represent the source labels in {1,...,n}. Subtracting one from each pattern value gives [2,4,0,5,1,3].", DescribeRole.Definition),
            Node("verkama62-representation-word-inversions", "Equality with the list inversion statistic", "word_inversions",
                "For every finite permutation pi, the existing inversion counter of its one-based word PSW.word pi equals the increasing-position pair count on all positions. The proof identifies the range-indexed row counts and their finite sums.", DescribeRole.Theorem),
            Node("verkama62-representation-rational-bound-of-ear-run", "Exact rational comparison", "rational_bound_of_ear_run",
                "For every n and permutation pi, one-based classical 351624-avoidance and a northeast ear run reaching all positions imply inv(pi) >= (7/4)n - 3 over the rationals. The proof uses the subtraction-free integer comparison 7n <= 4 inv(pi) + 12. Existence of the run is an explicit hypothesis.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
