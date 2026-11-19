using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiSupportedNoiseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/UmegakiSupportedNoise.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support containment and a one-sided data-processing bound yield convergence of finite Umegaki entropy.",
        H("Umegaki entropy under supported density noise"), Blocks(
            Describe.Lean(DescribeId.Create("tendsto-finitetracelogrelativeentropy-of-noise"),
                DeclarationHandle.Create(Prefix + "tendsto_finiteTraceLogRelativeEntropy_of_noise"),
                H("One-sided supported entropy limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the first density state be supported inside the second. As the weight tends to zero from above, each state mixes with its own fixed density noise. The mixtures must eventually have support containment and finite entropy at most the original finite entropy.")),
                    Paragraph(Text("The self-log term converges by continuity. The supported cross-log comparison supplies the required lower limit by bounding the second mixture with a positive shift of the original second state. The eventual upper bound then gives convergence of the finite divergence."))),
                DescribeRole.Theorem))));
}
