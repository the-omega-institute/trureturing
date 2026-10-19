using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourExceptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exceptional order-five obstruction", H("The exceptional order-five obstruction"),
        Blocks(
            Paragraph(Text("The universal linear lower bound permits eleven landmarks at order five. Their incidence structure forces an additional contradiction.")),
            Node("five-obstruction", "Eleven landmarks are impossible", "five_obstruction",
                "No actual weak-four landmark set on Fin 5 times Fin 5 has eleven elements. Each incidence part would have one degree-three vertex and four degree-two vertices. A low vertex with two low neighbors forces a four-cycle with degree total nine, whose diagonal pair is separated by only three. Thus each of the eight low vertices needs an edge to a high vertex, but the two high degrees provide only six incidences.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
