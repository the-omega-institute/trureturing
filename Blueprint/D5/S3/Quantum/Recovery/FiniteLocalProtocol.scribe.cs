using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteLocalProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complete finite subtree of local completely positive instruments conserves the trace of every input matrix, including off-diagonal spectator entries. Each node changes only its selected holder and the subsequent tree depends only on its observed outcome.",
        H("FiniteLocalProtocol"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-subtree-trace"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteLocalProtocol.complete_subtree_trace"),
            H("complete subtree trace"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every complete finite subtree of local completely positive instruments conserves the trace of every input matrix, including off-diagonal spectator entries. Each node changes only its selected holder and the subsequent tree depends only on its observed outcome."))),
            DescribeRole.Theorem))));
}
