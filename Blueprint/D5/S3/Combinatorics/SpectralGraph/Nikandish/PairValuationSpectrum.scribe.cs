using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class PairValuationSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairValuationSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd good-prime valuation obstructions on actual graphs", H("Odd good-prime valuation obstructions on actual graphs"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open.")),
            Item("actual-odd-valuations", "actual_odd_valuations", "The full arbitrary-prime odd-valuation exclusion", "The source lower prime bounds and coprime tails are retained, with arbitrary positive tails above the repeated minimum. Actual graph integrality supplies the full determinant root."),
            Item("progression-orders", "progression_orders", "Exact orders throughout the full progression", "Every n>=0 in 156+2450n has the stated first orders at five and seven; this is not a finite progression sample."),
            Item("actual-progression", "actual_progression", "Actual unbounded progression of nonintegral graphs", "All n and all source-admissible tails are retained. The result consumes the full root-valuation theorem.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairLowArithmetic"))]));
}
