using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recovery from a certified adjacent two-site marginal",
        H("Recovery from a certified adjacent two-site marginal"),
        Blocks(
            Claim("unitPhase_of_rawTwo_eq", "The full actual competitor has a single unit phase",
                "Equal two-site marginals give equal forward and reverse block products in the rational swap basis. Triplet proportionality fixes the singlet proportion as well. Equality of the original nonzero marginal fixes the absolute value of the scalar."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-recovery-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
