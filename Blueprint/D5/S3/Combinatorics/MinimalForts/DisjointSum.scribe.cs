using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class DisjointSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/DisjointSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All minimal forts of disjoint graph sums.", H("All minimal forts of disjoint graph sums"),
        Blocks(
            Node("fort-sum-iff", "Forthood on every disjoint subset", "fort_sum_iff", "For arbitrary finite decidable simple graphs G and H and arbitrary vertex subsets S and T, their disjoint sum is a fort exactly when at least one subset is nonempty and every unselected vertex of each summand has a selected-neighbor count different from one in that summand. Empty summands and empty intersections are retained.", DescribeRole.Theorem),
            Node("minimalfort-disjsum-iff", "Complete minimality classification", "minimalFort_disjSum_iff", "For arbitrary finite decidable simple graphs G and H, the disjoint subset S union T is an inclusion-minimal nonempty fort exactly when S is a minimal fort of G and T is empty, or S is empty and T is a minimal fort of H. Minimality ranges over all subsets.", DescribeRole.Theorem),
            Node("minimalfort-sum-count", "Exact additive full count", "minimalFort_sum_count", "For all finite decidable simple graphs G and H, the number of all actual minimal forts of their disjoint union equals the sum of their full minimal-fort counts. The proof constructs disjoint injective images and proves exhaustiveness, using the full minimality classification.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
