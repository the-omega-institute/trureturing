using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSymmetryDAGNodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteSymmetryDAGNode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Untrusted finite symmetry replay nodes",
        H("Untrusted finite symmetry replay nodes"),
        Blocks(
            Paragraph(Text("A node proposes a bound test, a symmetry action or all value children of a literal split. Node identity by itself establishes no acceptance at any context.")),
            Node("Node", "Node", "Finite literal node data",
                "The data type keeps the complete coordinate and every value child. The checker, rather than the data producer, establishes acceptance.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
