using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq207TripleProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler convolution and Durfee normalization give a formal Jacobi triple product.",
        H("Formal Jacobi Triple Product"),
        Blocks(
            Node("inversionseq207-triple-product-shifted-euler-factor", "Shifted Euler factor", "shiftedEulerFactor", "The shifted Euler factor is the Laurent-valued power series whose coefficient at each degree sums the Euler coefficients after multiplication by the corresponding power of the series variable.", DescribeRole.Definition),
            Node("inversionseq207-triple-product-formal-theta", "Formal theta series", "formalTheta", "The formal theta series is the product of the Euler Laurent expansion and the inverted shifted Euler factor.", DescribeRole.Definition),
            Node("inversionseq207-triple-product-formal-triple-product", "Formal triple product identity", "formal_triple_product", "For every integer index, the pentagonal power series multiplied by the power series of the index coefficient of formal theta equals the signed monomial at the triangular exponent determined by the sign of the index.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
