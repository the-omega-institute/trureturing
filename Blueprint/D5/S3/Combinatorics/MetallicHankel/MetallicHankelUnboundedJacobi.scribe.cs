using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedJacobiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifted Hankel determinants of any integral formal power series satisfy the Desnanot-Jacobi identity, including at vanishing determinants.",
        H("The Shifted Hankel Desnanot-Jacobi Identity"),
        Blocks(
            Node("metallic-hankel-unbounded-jacobi-hankel-jacobi", "Adjacent shifts and determinant sizes", "hankel_jacobi",
                "For every integral formal power series Phi and all nonnegative integers ell and j, write Delta_r^{(s)} for the determinant with entries [q^{s+a+b}]Phi and size r. Then (Delta_{j+1}^{(ell+1)})^2 = Delta_{j+1}^{(ell)} Delta_{j+1}^{(ell+2)} - Delta_{j+2}^{(ell)} Delta_j^{(ell+2)}. The empty determinant is one. No determinant is assumed nonzero, and the identity holds also for j equal to zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
