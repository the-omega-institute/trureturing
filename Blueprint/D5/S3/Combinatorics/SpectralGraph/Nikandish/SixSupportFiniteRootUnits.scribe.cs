using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportFiniteRootUnitsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootUnits." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual residue degree and f units at finite D places", H("Actual residue degree and f units at finite D places"),
        Blocks(
            Paragraph(Text("Let k be a characteristic-zero field and let K=k(b). The quadratic field H=K(sqrt(D)) and the further quadratic field F=H(sqrt(f)) use the fixed polynomials of the six-support equality curve. The finite places considered here lie above roots of D on the affine b-line. Their normalized multiplicative valuations, residue fields and ramification indices refer to the actual integral closure and its prime localizations.")),
            Item("residue", "residue_degree_one", "Residue degree one", "The actual residue field of every D-root prime is k, with library inertia degree1."),
            Item("unit", "localF_unit", "The actual f has a local unit representative", "The local numerator and denominator are units at every actual D root; the local representative maps to the same supplied f in H."),
            Item("same-field", "localF_intoH", "The local representative maps to the actual f", "The map is the fixed actual localization embedding into H, with its prescribed algebra structure."),
            Item("valuation", "valuation_f", "Every actual finite D place gives valuation one", "Multiplicative normalized valuation of f is1, equivalently additive order zero.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootGeometry"))]));
}
