using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of two signed Narayana strip series is the Narayana strip series with squared parameters at heights 4m and 4m + 1.",
        H("Cigler's Narayana Strip Product Formula"),
        Blocks(
            Node("cigler-strip-product-result", "The product formula at both strip heights", "result", "For every positive integer m and each height h equal to 4m or 4m + 1, C^{(h)}(t^2, z^2) = c^{(h)}(t, z)c^{(h)}(-t, -z) as formal power series in z with coefficients in the integer polynomial ring in t. Here C^{(h)} and c^{(h)} sum Dyck paths confined to heights zero through h, with z marking semilength, every up-step weighted one, and down-step arrival weights repeating 1, t for C^{(h)} and 1, t, -1, -t for c^{(h)}. The equality holds for every coefficient of z and proves Conjecture 2, equation (79), of Cigler's paper. First-return decomposition gives the continuant representation of each bounded series. The numerator and denominator factorizations at indices h + 1, together with invertibility of the denominators, give the product identity.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
