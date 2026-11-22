using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCompactExceptionalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactExceptional";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exceptional lifts of the six-site compact trace graph",
        H("Exceptional lifts of the six-site compact trace graph"),
        Blocks(
            Claim("exceptional_amplitude", "Two charts cover the base fibers",
                "Every amplitude projector over a base point is a shear of a nonzero normal direction or its symbol exchange. The column factorization extends to all compact limits in the chart.", DescribeRole.Theorem),
            Claim("exceptional_observation_difference_eq_zero", "Excluding the special observation",
                "If an exceptional lift has zero adjacent-ones probability, its singleton diagonal and exchange entries coincide.", DescribeRole.Theorem))));

    private static DocumentBlock Claim(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitecompactexceptional-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
