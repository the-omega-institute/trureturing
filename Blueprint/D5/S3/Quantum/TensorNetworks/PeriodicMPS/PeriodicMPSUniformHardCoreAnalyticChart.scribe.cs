using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreAnalyticChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The analytic fold in the actual hard-core chart",
        H("The analytic fold in the actual hard-core chart"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticchart-exists-coherence-fold"),
                DeclarationHandle.Create(Module + ".exists_coherence_fold"),
                H("A fold after straightening the regular readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At each length n ≥ 7 the seven regular normalized readouts, augmented by the imaginary part of the first coordinate, are analytic local coordinates at the witness. In these coordinates the negative real 00,01 coherence has a strict fold in the free variable."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticchart-exists-generic-actual-reconstruction"),
                DeclarationHandle.Create(Module + ".exists_generic_actual_reconstruction"),
                H("Transfer of chart recovery to actual projectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume there are chart points arbitrarily near the witness with equal regular observations and coherence and distinct forbidden-corner populations. The analytic fold theorem gives an open dense singleton-fiber locus in a chart neighborhood. Localization by the normalized marginal confines all actual competitors to a smaller compact chart set. Its compact image of the excluded set is closed, yielding a relatively open dense target set in an open neighborhood of the witness in the actual projector image."))),
                DescribeRole.Theorem))));
}
