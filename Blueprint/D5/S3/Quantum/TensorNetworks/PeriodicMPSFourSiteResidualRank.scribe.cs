using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteResidualRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualRank";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear algebra certificate for the degree-eight quotient",
        H("A linear algebra certificate for the degree-eight quotient"),
        Blocks(
            Claim("quotient_finrank_le_of_minor", "A coefficient minor leaves at most one quotient dimension",
                "There are 45 degree-eight ternary monomials. An invertible coefficient minor on 44 homogeneous ideal elements makes those elements linearly independent in the kernel of the quotient map."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-residualrank-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
