using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedAnalyticDriftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform derivative drift bound for chirped correlations.",
        H("A uniform derivative drift bound for chirped correlations"),
        Blocks(
            Describe.Lean(DescribeId.Create("has-fderiv-at-residual"),
                DeclarationHandle.Create(Module + ".hasFDerivAt_residual"),
                H("Fréchet derivative of the correlation residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The derivative differentiates both seed factors in each Hermitian pairing, followed by the "
                    + "specified real or imaginary projection."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("derivative-drift"),
                DeclarationHandle.Create(Module + ".derivative_drift"),
                H("The derivative is globally 16-Lipschitz"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each phase sign is either plus or minus one. Parseval bounds the normalized Fourier transforms "
                    + "of the spectrum and its derivative. Combining the bounds for the two factors yields the stated "
                    + "constant in the operator norm induced by coordinate sup norms."))),
                DescribeRole.Theorem))));
}
