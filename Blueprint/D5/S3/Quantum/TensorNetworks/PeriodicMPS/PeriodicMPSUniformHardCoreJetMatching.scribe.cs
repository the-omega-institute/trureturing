using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreJetMatchingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetMatching";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matching regular hard-core coefficients",
        H("Matching regular hard-core coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorejetmatching-exists-opposite-regular-match"),
                DeclarationHandle.Create(Module + ".exists_opposite_regular_match"),
                H("A matched polynomial path at the opposite slope"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every length n ≥ 7 the regular equations can be solved through order four by successive real quadratic, imaginary cubic and real quartic corrections. At the opposite slope the real 00,01 coherence agrees through order three. The 11,11 coefficients agree below order four, and their fourth-order difference is the certified quartic."))),
                DescribeRole.Theorem))));
}
