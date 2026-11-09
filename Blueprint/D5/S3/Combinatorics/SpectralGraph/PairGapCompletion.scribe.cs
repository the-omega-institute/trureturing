using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairGapCompletionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairGapCompletion." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive tail gap three and four is nonintegral.", H("Every positive tail gap three and four is nonintegral."),
        Blocks(
            Paragraph(Text("Source: four-prime-weighted-midpoint and four-prime-even-midpoint, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("three", "actual_gap_three", "The entire gap-three domain", "All positive natural a,b and arbitrary distinct primes are included. The proof joins the full weighted quadrant, four unbounded small-tail polynomial rows and the existing unit and repeated-two/three/four results. It does not assert the half-unit window in every small case."),
            Item("four", "actual_gap_four", "The entire gap-four domain", "All positive natural a,b and arbitrary distinct primes are included. The b=4 small-tail case uses its own unit window, retaining the exact source distinction. No finite exponent rectangle is used.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairGapSpectrum"))]));
}
