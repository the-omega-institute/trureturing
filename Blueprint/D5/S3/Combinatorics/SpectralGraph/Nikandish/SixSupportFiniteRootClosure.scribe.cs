using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportFiniteRootClosureDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootClosure." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual finite D places of the integral closure", H("All actual finite D places of the integral closure"),
        Blocks(
            Paragraph(Text("Let k be a characteristic-zero field and let K=k(b). The quadratic field H=K(sqrt(D)) and the further quadratic field F=H(sqrt(f)) use the fixed polynomials of the six-support equality curve. The finite places considered here lie above roots of D on the affine b-line. Their normalized multiplicative valuations, residue fields and ramification indices refer to the actual integral closure and its prime localizations.")),
            Item("unique", "closure_unique_prime_above", "Unique actual integral-closure prime", "Every prime of the actual integral closure over the original base root is the constructed prime."),
            Item("bijection", "rootToClosurePlace_bijective", "Exact root to normalization-place bijection", "All actual prime-spectrum places of the integral closure over the D roots are included."),
            Item("count", "actual_closure_place_count", "Exactly eight actual normalization places", "The full normalization fiber has eight points over every algebraically closed characteristic-zero field."),
            Item("valuation", "closure_valuation_delta", "Actual normalized base valuation", "The library normalized valuation on the same H at the actual closure localization has the exact base-parameter value exp(-2)."),
            Item("data", "every_closure_place_data", "Complete data for every actual normalization place", "Every actual point has the exact prime, DVR/local uniformizer, ramification index2, residue degree1, local representative of the same f, and normalized y/base/f values. The fiber consists of all finite places above roots of D.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootCount"))]));
}
