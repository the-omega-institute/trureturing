using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairSharedSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairSharedSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual shared-tail obstruction without coprimality", H("Actual shared-tail obstruction without coprimality"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("actual-first-orders", "actual_first_orders", "Both first-order low-root obstructions", "Arbitrary shared tails are permitted. Only the original failures of the minimum tail valuation at the two stated good primes are assumed."),
            Item("actual-progression", "actual_progression", "Entire shared-tail progression", "Every n>=0 and every pair of sufficiently large tails with the two specified order failures are retained; no coprimality assumption is added.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairSharedRoot")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairValuationSpectrum"))]));
}
