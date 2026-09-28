using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PurifiedLocalPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite local protocol with a nonempty finite holder set and a finite spectator, with independent mixed local ancillas, internally chosen local purifications reproduce the original initialization on every matrix. Every observed path has an exact holder-local product factorization with explicit inaccessible-register regrouping, isometric root maps, the accumulated local recurrence and inactive identity coordinate equivalences.",
        H("PurifiedLocalPath"),
        Blocks(Describe.Lean(
            DescribeId.Create("purified-local-path-bridge"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/PurifiedLocalPath.purified_local_path_bridge"),
            H("purified local path bridge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every finite local protocol with a nonempty finite holder set and a finite spectator, with independent mixed local ancillas, internally chosen local purifications reproduce the original initialization on every matrix. Every observed path has an exact holder-local product factorization with explicit inaccessible-register regrouping, isometric root maps, the accumulated local recurrence and inactive identity coordinate equivalences."))),
            DescribeRole.Theorem))));
}
