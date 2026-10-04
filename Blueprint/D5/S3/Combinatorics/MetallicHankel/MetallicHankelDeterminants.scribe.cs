using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelDeterminantsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A monic moment relation determines a Hankel zero interval, its endpoint and the determinant at the next shift without division.",
        H("Integral Hankel Zero Runs and Shift Relations"),
        Blocks(
            Node("metallic-hankel-determinants-zero-run", "The determinant formula from a zero run of moments", "zero_run",
                "Let Phi(q) = sum_{r >= 0} f_r q^r be an integral formal power series, let ell and s be nonnegative integers and let m be positive. Suppose c_s = 1, sum_{r=0}^s c_r f_{ell+r+t} = 0 for every nonnegative t less than s+m-1, and sum_{r=0}^s c_r f_{ell+r+s+m-1} = h. Then Delta_{s+m}^{(ell)} = (-1)^{m(m-1)/2} h^m Delta_s^{(ell)}; Delta_j^{(ell)} = 0 whenever s < j < s+m; and Delta_s^{(ell+1)} = (-1)^s Delta_s^{(ell)} c_0. These equalities hold over the integers even when h or Delta_s^{(ell)} vanishes.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
