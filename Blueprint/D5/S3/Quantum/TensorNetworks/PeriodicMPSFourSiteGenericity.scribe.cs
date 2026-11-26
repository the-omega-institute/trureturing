using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteGenericityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic recovery of the four-site periodic binary bond-two state",
        H("Generic recovery of the four-site periodic binary bond-two state"),
        Blocks(
            Claim("generic_unitPhase_recovery", "Recovery on a relatively open dense part of the actual state image",
                "The norm square of the coefficient certificate is a real polynomial in the full amplitudes. Its pullback to the real tensor coordinates is nonzero at a physical witness. Polynomial density and the continuous parametrization give the relatively open dense locus, with unit-phase uniqueness against every actual competitor."),
            Claim("normalized_generic_unitPhase_recovery", "Recovery in the unit-mass slice",
                "The positive rays of the certificate locus meet the unit-mass slice in a relatively open dense set. Rescaling both tensor pairs preserves equality of the two-site marginal and transports unit-phase recovery to this slice."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-genericity-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
