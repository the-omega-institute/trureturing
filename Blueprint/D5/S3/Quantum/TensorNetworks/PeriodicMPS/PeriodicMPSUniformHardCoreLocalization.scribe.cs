using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreLocalizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Localization from the hard-core marginal",
        H("Localization from the hard-core marginal"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorelocalization-closure-actualprojectors-witness-fiber"),
                DeclarationHandle.Create(Module + ".closure_actualProjectors_witness_fiber"),
                H("The complete compact witness fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n ≥ 7 the trace-one witness projector is the only point in the compact closure of the actual projector image with its adjacent two-site marginal. A point in the closure is a rank-one projector with cyclic columns. The fixed-witness recovery result for cyclic amplitudes then identifies its ray."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorelocalization-exists-open-normalizedmarginal-localization"),
                DeclarationHandle.Create(Module + ".exists_open_normalizedMarginal_localization"),
                H("Control of every actual competitor near the witness observation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Compactness and continuity keep every projector above a sufficiently small open marginal neighborhood near the witness projector. The vacuum coordinate gives a continuous full-amplitude representative there. Applying the ordinary decoder to that representative forces the first core trace to be nonzero and places the ordinary trace invariants in any prescribed neighborhood of the witness invariants."))),
                DescribeRole.Theorem))));
}
