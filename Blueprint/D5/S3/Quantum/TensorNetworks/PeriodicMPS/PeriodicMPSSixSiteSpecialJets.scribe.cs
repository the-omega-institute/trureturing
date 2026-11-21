using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteSpecialJetsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialJets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational cubic separation at the two six-site lifts",
        H("Rational cubic separation at the two six-site lifts"),
        Blocks(
            Claim("tangent_nonsingular", "Invertible tangent matrices",
                "Each tangential Jacobian has an exact rational inverse.", DescribeRole.Theorem),
            Claim("exact_jet_coefficients", "Normal coefficients after tangent correction",
                "The two certified paths use the same ambient tangent direction and cancel the tangential quadratic coefficient.", DescribeRole.Theorem),
            Claim("normalCubics_ne", "Different cubic coefficients",
                "The normal cubic coefficients along the common direction are unequal.", DescribeRole.Theorem))));

    private static DocumentBlock Claim(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitespecialjets-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
