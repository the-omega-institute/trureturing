using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FisherDiscord;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit flagged state refutes partial-trace monotonicity of Fisher discord.",
        H("Fisher discord decreases under a partial trace"), Blocks(
            Describe.Lean(DescribeId.Create("fisher-discord-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/FisherDiscord/Result.result"),
                H("Explicit refutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the diagonal qubit state with weights one fifth and four fifths and the Pauli X observable. Its Fisher discord is four twenty-fifths. The flagged state with support on the basis vectors 00 and 11 has the same marginal and zero discord for the lifted observable, so the universal partial-trace inequality fails."))),
                DescribeRole.Theorem))));
}
