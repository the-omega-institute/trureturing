using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteInterpolationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteInterpolation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective interpolation for homogeneous quotient bounds",
        H("Projective interpolation for homogeneous quotient bounds"),
        Blocks(
            Claim("common_zeros_proportional_of_finrank_le_one", "A one-dimensional quotient gives projective uniqueness",
                "A positive-degree homogeneous component separates any two nonproportional nonzero projective points by powers of linear forms. If the quotient image has dimension at most one, any two such common zeros are proportional."),
            Claim("finrank_quotient_ge_of_projective_points", "Evaluation and directional derivatives bound the bidegree quotient",
                "Bilinear separators isolate a selected projective point and its first-order variation. The resulting independent evaluation and derivative functionals give a lower bound for the quotient dimension."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-interpolation-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
