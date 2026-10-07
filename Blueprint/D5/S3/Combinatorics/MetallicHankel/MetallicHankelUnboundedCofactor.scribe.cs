using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedCofactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two orthogonal moment relations determine the shifted cofactor of a unit Hankel determinant.",
        H("A Cofactor Identity at Normal Hankel Indices"),
        Blocks(
            Node("metallic-hankel-unbounded-cofactor-normal-cofactor", "The shifted cofactor from moment relations", "normal_cofactor",
                "Let Phi be an integral formal power series, ell a nonnegative integer and m a positive integer. Let c and b be integer sequences and h an integer. Suppose c_m = 1, and b_1 = 0 when m = 1. For each t from zero through m-1, suppose the sum of c_r [q^{ell+r+t}]Phi over r from zero through m is zero. For each t from zero through m-2, suppose the sum of b_r [q^{ell+r+t}]Phi over r from zero through m-1 is zero, and suppose that the latter sum at t = m-1 equals h. If Delta_m^{(ell)} is an integer unit, then h Delta_{m-1}^{(ell+2)} = Delta_m^{(ell)}(c_1 b_0 - c_0 b_1). The unit condition means that Delta_m^{(ell)} is either one or minus one; no nonvanishing condition is imposed on the smaller determinant.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
