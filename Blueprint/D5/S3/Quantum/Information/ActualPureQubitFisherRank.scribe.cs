using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitFisherRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitFisherRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral SLD information bounds measurement Fisher information and controls the rank-one branch.",
        H("Fisher information and the qubit rank alternative"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-fisher"),
                DeclarationHandle.Create(Module + "actual_fisher"), H("Measurement Fisher lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every differentiable positive curve with the exact affine measurement probabilities has spectral SLD information at least the classical Fisher information. Two-sided positivity first forces the derivative's kernel-to-kernel block to vanish (Pker D Pker = 0), producing an SLD without invertibility. Positive residual squares then give the measurement bound.")))),
            Describe.Lean(DescribeId.Create("actual-rank-alternative"),
                DeclarationHandle.Create(Module + "actual_rank_alternative"), H("Rank alternative and binary cost gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual nonconstant pure-qubit readout has rank two or incurs the binary-measurement lower bound from any negative and positive score. Rank zero and rank three are excluded by the visible projection geometry.")))))));
}
