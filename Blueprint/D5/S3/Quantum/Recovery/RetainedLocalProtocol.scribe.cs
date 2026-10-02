using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class RetainedLocalProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite local instrument tree and every input matrix with arbitrary finite inaccessible garbage and untouched spectator, tracing the recursively retained outputs reproduces the complete coarse terminal and prefix lists. At every nonterminal root the internally selected spectral Kraus data reproduce its actual CP action on every local matrix. Later operations leave old garbage coordinates untouched and branch only on observed outcomes.",
        H("RetainedLocalProtocol"),
        Blocks(Describe.Lean(
            DescribeId.Create("recursive-coarse-retained"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/RetainedLocalProtocol.recursive_coarse_retained"),
            H("recursive coarse retained"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every finite local instrument tree and every input matrix with arbitrary finite inaccessible garbage and untouched spectator, tracing the recursively retained outputs reproduces the complete coarse terminal and prefix lists. At every nonterminal root the internally selected spectral Kraus data reproduce its actual CP action on every local matrix. Later operations leave old garbage coordinates untouched and branch only on observed outcomes."))),
            DescribeRole.Theorem))));
}
