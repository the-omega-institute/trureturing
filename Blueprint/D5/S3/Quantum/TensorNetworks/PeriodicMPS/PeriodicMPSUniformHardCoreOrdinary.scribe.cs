using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreOrdinaryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreOrdinary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary trace invariants of the cyclic witness",
        H("Ordinary trace invariants of the cyclic witness"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreordinary-ordinary-invariants-of-hard-core-amplitudes"),
                DeclarationHandle.Create(Module + ".ordinary_invariants_of_hard_core_amplitudes"),
                H("Determination of the ordinary invariants"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n ≥ 7, vanishing of the words starting in 11 and equality of the vacuum, singleton and separated-pair amplitudes to one nonzero constant force the first core trace to be nonzero, the second trace and both determinants to vanish, and the mixed trace to equal the square of the first trace. Three different gap products in the two-term Cayley–Hamilton recurrence force the remaining determinant to vanish."))),
                DescribeRole.Theorem))));
}
