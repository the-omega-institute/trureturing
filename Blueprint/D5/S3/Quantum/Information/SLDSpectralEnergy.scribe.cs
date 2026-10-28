using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SLDSpectralEnergyDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("sld-spectral-energy-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Information/SLDSpectralEnergy." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density matrices and spectral energy of symmetric logarithmic derivatives.",
        H("Hermitian SLD energy"), Blocks(
            Item("IsDensity", "Density matrices", "A density matrix is a positive semidefinite complex matrix with trace one on an arbitrary finite index type.", DescribeRole.Definition),
            Item("diagonal_energy", "Energy in a specified diagonal basis", "For a real diagonal D with entries w, a Hermitian L satisfying LD+DL=2B has real trace(LDL) equal to the sum over ordered pairs of 2 times the squared modulus of B(i,j), divided by w(i)+w(j). Real division gives zero when the denominator vanishes. The statement allows any real diagonal; positivity is not needed for this algebraic identity."),
            Item("spectral_energy", "Energy in an eigenbasis", "For a positive semidefinite rho and every Hermitian L satisfying L rho+rho L=2B, real trace(L rho L) equals spectralQFI(rho,B). The proof conjugates the equation into the eigenvector basis and applies the diagonal energy identity. This is the same spectralQFI defined in ActualPureQubitGeometry, including its convention at zero eigenvalue sums."))));
}
