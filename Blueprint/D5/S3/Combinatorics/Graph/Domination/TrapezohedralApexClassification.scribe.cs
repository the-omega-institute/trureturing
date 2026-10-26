using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralApexClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected minimal dominating subset has exactly one apex and one selected opposite rim label.",
        H("Classification by an apex and an opposite label"),
        Blocks(
            Paragraph(Text("All statements concern the original graph on alpha, beta, a(i), b(i), and actual selected vertex subsets. Closed domination and minimality among all proper subsets are unchanged. If both apices are selected, minimality forces the disconnected apex pair. If neither is selected, domination of each apex supplies selected labels of both types. A unique selected label of either type would force all labels of the other type into two neighbors, contradicting n>=3. Closed-private witnesses then force each selected b-vertex to have at most one selected a-neighbor. Connectivity propagates the same a-label along every selected walk, contradicting the existence of two selected a-labels. This avoids any finite-size extrapolation.")),
            Node("one-apex", "Exactly one apex", "exactly_one_apex",
                "For every n>=3 and every admissible original subset S, exactly one of alpha and beta belongs to S."),
            Node("alpha-opposite", "The alpha branch", "alpha_unique_opposite",
                "If alpha belongs to S and beta does not, exactly one b-label is selected. Connectivity prevents a selected b-vertex from using itself privately; alpha prevents either neighboring a-label from witnessing it privately. Its private witness is therefore beta, which forces uniqueness."),
            Node("reconstruction", "Read and reconstruct", "alpha_reconstruction",
                "In the alpha branch the unique selected b-label j and the membership of the selected a-labels reconstruct the entire original subset. Different j cannot reconstruct the same subset. No quotient by graph symmetries is taken.")), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
