using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreFirstJetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-seven normalized marginal differential",
        H("The rank-seven normalized marginal differential"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorefirstjet-regularreadout-rank-seven"),
                DeclarationHandle.Create(Module + ".regularReadout_rank_seven"),
                H("Seven independent real readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every length n ≥ 7 the derivative at the witness of four real and three imaginary components of the normalized adjacent-pair matrix has real rank seven. Explicit Fibonacci coefficient formulas yield invertible real and imaginary blocks once the imaginary part of the first chart coordinate is fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorefirstjet-local-regular-reconstruction"),
                DeclarationHandle.Create(Module + ".local_regular_reconstruction"),
                H("Local coordinates from the regular readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Adjoining the imaginary part of the first chart coordinate makes the derivative invertible. The inverse function theorem turns the augmented readout into local coordinates around the witness."))),
                DescribeRole.Theorem))));
}
