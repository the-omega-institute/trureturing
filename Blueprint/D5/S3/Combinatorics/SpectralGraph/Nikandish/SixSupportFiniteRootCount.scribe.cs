using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportFiniteRootCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootCount." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual finite D places over the quadratic order", H("All actual finite D places over the quadratic order"),
        Blocks(
            Paragraph(Text("Let k be a characteristic-zero field and let K=k(b). The quadratic field H=K(sqrt(D)) and the further quadratic field F=H(sqrt(f)) use the fixed polynomials of the six-support equality curve. The finite places considered here lie above roots of D on the affine b-line. Their normalized multiplicative valuations, residue fields and ramification indices refer to the actual integral closure and its prime localizations.")),
            Item("bijection", "rootToPlace_bijective", "All actual places and actual roots correspond", "The actual prime-spectrum fiber over the base D-root ideals is in bijection with all D roots. The bijection covers the entire fiber."),
            Item("count", "actual_place_count", "Exactly eight geometric finite D places", "For every algebraically closed characteristic-zero field, the full actual fiber has cardinality8. The statement includes the algebraic closure of the rationals."),
            Item("place-data", "every_place_data", "Every actual place has the complete source data", "The theorem produces the root and actual prime equality, DVR, uniformizer, e2, residue1, local f unit and all normalized valuations for every member of the fiber.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootUnits"))]));
}
