using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;
internal sealed class RectangularDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpectralTopology/RectangularDilation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/radsararanando2026apollonian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive second eigenvalues of unequal Hermitian block dilations.", H("Unequal block dilation spectra"), Blocks(
            Node("unequal_dilation_second", "The complex unequal-block identity",
                "For arbitrary finite types I and J with decidable equality, let B be a complex I by J matrix and let P=[[0,B],[B*,0]] be Hermitian. Suppose I has at least two elements and the second decreasing eigenvalue of BB* is strictly positive. The second decreasing real eigenvalue of P equals the positive square root of the second decreasing eigenvalue of BB*. Both lists count algebraic multiplicity. The two block sizes may differ or the second block may be empty; strict positivity rules out insufficient positive rank. Zero padding preserves the positive ordered prefix. A permutation identifies the square padded dilation with P plus a zero block; roots of characteristic polynomials retain signs and multiplicities.", DescribeRole.Theorem),
            Node("eigenvalues_ofReal", "Real inclusion preserves the ordered spectrum",
                "For any finite index type with decidable equality, a Hermitian real matrix and its entrywise inclusion in the complex field have identical decreasing real eigenvalue lists. The equality preserves characteristic-polynomial multiplicities and all indices.", DescribeRole.Theorem),
            Node("unequal_real_dilation_second", "The real unequal-block identity",
                "For arbitrary finite types I and J with decidable equality, let B be a real I by J matrix and let P=[[0,B],[transpose B,0]] be Hermitian. If I has at least two elements and the second decreasing eigenvalue of BB* is strictly positive, the second decreasing real eigenvalue of P equals its positive square root. For real matrices B*=transpose B. The proof embeds entries in the complex field, transports the full characteristic-root multiset and its decreasing order, and applies the complex unequal-block identity.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rectangulardilation-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
