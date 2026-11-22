using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class CambieQ19SummationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphSubtrees/cambiejookenwagner2026meansubtrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grouping intervals by their attachment marks evaluates each of the four moments and gives the exact rational difference between the two means.",
        H("A strict counterexample to the mean-order comparison"),
        Blocks(
            Node("count-order", "CountOrder", "Count and total order",
                "Each pair stores a natural count and a natural sum of vertex orders.", DescribeRole.Definition),
            Node("code-moments", "codeMoments", "The configuration moments",
                "Sum the count and order contributions over the finite configurations. The tree version weights each configuration by its deletion multiplicity and the connected-set version weights each configuration once.", DescribeRole.Definition),
            Node("induced-exact-moments", "induced_exact_moments", "Exact induced moments",
                "The count and total order of the actual connected induced vertex supports are 10,425,438,990,512 and 43,855,001,336,852,520.", DescribeRole.Theorem),
            Node("tree-exact-moments", "tree_exact_moments", "Exact tree moments",
                "The count and total order of the actual tree subgraphs are 14,578,492,765,509 and 61,323,620,645,707,018.", DescribeRole.Theorem),
            Node("exact-gap", "exactGap", "The exact rational gap",
                "The connected-set mean minus the subtree mean is exactly 1769250196421378505239933 divided by 18998398362554330511481326.", DescribeRole.Theorem),
            Node("strict-comparison", "strictComparison", "Strict comparison on the witness",
                "The mean order of actual tree subgraphs is strictly smaller than the mean order of connected vertex supports.", DescribeRole.Theorem),
            Node("result", "result", "Question 1.9 is false",
                "The fixed connected graph has subtree mean strictly below its connected-set mean, refuting the universal comparison.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cambie-jooken-wagner-mean-order-comparison"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
