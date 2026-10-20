using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;
internal sealed class DisconnectedSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedSupport.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disconnection of a balanced native choice is equivalent to actual activity of both roots and a root-separating edge coloring.",
        H("The Actual Disconnection Criterion"), Blocks(
            Describe.Lean(DescribeId.Create("literal-disconnected-count"), DeclarationHandle.Create(Prefix + "disconnectedCount"),
                H("A count of original choices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite count filters native Choices by Balanced and failure of ActiveConnected. It counts labelled choices, with unused vertices omitted from connectivity and without identifying any choices by a symmetry."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-coloring-criterion"), DeclarationHandle.Create(Prefix + "actual_disconnected_iff_coloring"),
                H("Both roots must be active"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every parameter t at least two and every balanced native choice, failure of active connectivity holds exactly when both roots are active and a Boolean coloring takes distinct prescribed values at those roots while remaining equal across every chosen edge. Actual rootedness makes every active component meet a used root. The coloring is constant on the equivalence closure of selected edges, so its distinct root values separate those components."))), DescribeRole.Theorem)), []));
}
