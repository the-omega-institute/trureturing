using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalFiberCanonicalKernelBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive finite spectral time fibers are exactly the canonical future-readout kernels.",
        H("Temporal Fiber Canonical-Kernel Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("temporal-range-kernel-eq-observation-setoid"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge.temporal_range_kernel_eq_observation_setoid"),
                H("Consecutive temporal fibers reuse the canonical observation kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equality kernel of the spectral readout on times zero through the selected depth is the repository's canonical observation setoid at that depth.")),
                    Paragraph(Text(
                        "The proof identifies the finite spectral word with futureReadoutWord and introduces no parallel time-kernel hierarchy."))),
                DescribeRole.Theorem))));
}
