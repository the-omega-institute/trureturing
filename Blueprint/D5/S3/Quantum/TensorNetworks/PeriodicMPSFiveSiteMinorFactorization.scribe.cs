using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteMinorFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorFactorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Determinant from triangular factors",
        H("Determinant from triangular factors"),
        Blocks(
            Claim("determinant_of_factors", "A row permutation and a triangular factorization give the determinant as a signed product of diagonal entries."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesiteminorfactorization-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
