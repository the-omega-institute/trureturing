using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class RootComparabilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rooted comparability of pairs stranded by a small actual configuration cut.",
        H("RootComparability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stranded-pair-comparable"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_comparable"),
                H("Root comparability under one small cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let the host be any finite connected simple undirected graph. Fix one cut of its full mixed mutual-visibility reconfiguration graph whose size is smaller than minimum degree, a clean root, and a surviving pair that cannot reach the root singleton after that cut. Then one endpoint belongs to every shortest path from the other endpoint to the root. The direction can depend on the pair. No assumption on host order, girth, dominating sets, or ranks of other configurations is imposed."))),
                DescribeRole.Theorem),
            Paragraph(Text("Every surviving singleton belongs to the same component because the cut is smaller than the host order. A component stranded from the root therefore contains no singleton, and every label of each pair in that component has its singleton in the cut. Cleanliness rules out a visible triple consisting of such a pair and the root, and also rules out host edges from either endpoint to the root. Three-label nonvisibility leaves rooted comparability or mandatory passage through the root.")),
            Paragraph(Text("Suppose instead that a stranded pair has all its geodesics pass through the root. Among visible configurations containing that pair and having every pair face in the stranded component, choose one of maximum cardinality. If it has at least three labels, the root-hub lemma makes all its pairs pass through the root; at rank two this is the initial pair. All pair distances are at least four. Consequently an outside label is adjacent to at most one selected label, so at most one actual slide can use it.")),
            Paragraph(Text("Partition the selected configuration's neighbors by their unique outside label, together with internal deletions. Its cut singleton faces pay the internal deletions. For an outside label whose singleton is cut, that singleton pays the possible slide. A visible extension is either cut or fails pair completeness by maximality; deleting towards an outside pair then supplies a distinct nonsingleton cut for the addition. For a surviving outside singleton, a proper deletion chain pays a slide; if the extension is itself cut that payment is separate. If the extension survives, the distinct proper cyclic deletion chains give at least two cuts containing the outside label. These suffice for the one possible slide and one addition. The classes are disjoint for different outside labels and from internal cuts. The resulting degree is at most the same cut size, contradicting its size below minimum degree.")),
            Paragraph(Text("The model retains existential shortest paths in the original host, every feasible rank including zero, token addition and removal, and slides along actual host edges to unoccupied labels. This rooted restriction does not establish the full equality between vertex connectivity and minimum degree. The complete local degree count for a minimum rooted pair and the universal separator composition are separate obligations.")))));
}
