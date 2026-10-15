using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCacheStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCacheState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thirty-two exact local cache proposals",
        H("Thirty-two exact local cache proposals"),
        Blocks(
            Paragraph(Text("The executable cache stores sixteen triangle and sixteen singleton states. Each state carries a representative index, earned-action proposal and small mirror row. Retaining the row removes packed lower decoding at leaves, while its equality with the indexed mirror is a separate proved invariant. These definitions assert no score bound or replay acceptance.")),
            Node("triangle-step", "triangleStep", "Transport and update an affected triangle state",
                "The old action sends the actual fill into representative coordinates and values. The per-row word supplies the new row and action, and the new action is composed with the old one in the checked order.", DescribeRole.Definition),
            Node("singleton-step", "singletonStep", "Transport and update an affected singleton state",
                "The analogous actual singleton action and transition decode retain a new literal row for later arithmetic.", DescribeRole.Definition),
            Node("step", "step", "Update exactly the affected original blocks",
                "Literal incidence selects each affected block's local coordinate. Blocks absent from the incidence retain their entire previous state and row literal.", DescribeRole.Definition),
            Node("lower", "lower", "Sum all thirty-two literal lower fields",
                "The original sixteen triangle and sixteen singleton bounds are all included with unchanged signs and weights. No sorted multiset or branch shape substitutes for actual cache association.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
