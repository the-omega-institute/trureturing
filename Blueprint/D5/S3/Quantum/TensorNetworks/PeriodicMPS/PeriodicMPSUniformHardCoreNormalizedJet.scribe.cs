using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreNormalizedJetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreNormalizedJet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace normalization and the first opposite-branch difference",
        H("Trace normalization and the first opposite-branch difference"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorenormalizedjet-opposite-forbidden-first-difference"),
                DeclarationHandle.Create(Module + ".opposite_forbidden_first_difference"),
                H("The first normalized difference has degree four"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At every length n ≥ 7 the physical raw coefficients and mass coefficients determine the normalized coefficients by formal division. At the opposite slope, matching the seven regular rows through degree three makes the normalized 11,11 differences vanish below degree four. Their fourth coefficient is quartic(n), which is nonzero with sign (−1)^(n−1)."))),
                DescribeRole.Theorem))));
}
