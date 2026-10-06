using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuImagesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuImages.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four integer-indexed Gaussian image families enumerate paths in a floor-reflected strip.",
        H("The Weighted Image Formula"),
        Blocks(
            Node("li-uncu-images-imagekernel", "The displacement kernel", "imageKernel",
                "For nonnegative L and integer d, the kernel is G(L,(L+d)/2) with integer indices when L+d is even, and zero otherwise.", DescribeRole.Definition),
            Node("li-uncu-images-imagepolynomial", "The four image families", "imagePolynomial",
                "Put p = 2H + 3 and i = H + 1 - a. Sum over all integers t the weight q^(2pt^2+(2a+1)t) times the kernels at displacements b-a-2pt and b+a+1+2pt. Subtract the sums of q^((2t+1)(pt+i)) times the kernels at displacements b-p+1+a-2pt and b+p-a+2pt. Each exponent is truncated at zero before taking a power. These are finite-support sums for endpoints in the strip.", DescribeRole.Definition),
            Node("li-uncu-images-path-image-formula", "Images enumerate bounded paths", "path_image_formula",
                "For every H at least one, every nonnegative length L, and integer endpoints a and b between zero and H, imagePolynomial(H,L,a,b) equals pathPolynomial(H,L,a,b).", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
