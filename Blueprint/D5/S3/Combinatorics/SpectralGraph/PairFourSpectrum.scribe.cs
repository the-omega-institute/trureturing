using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairFourSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairFourSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete repeated-four actual ideal-graph nonintegrality.", H("Complete repeated-four actual ideal-graph nonintegrality."),
        Blocks(
            Paragraph(Text("Source: four-prime-pair-four, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("minimum", "minimum_window", "A genuine minimum in the full interval one to four", "For all real tails at least two, the complete symmetrized four-cell operator has a smallest actual eigenvalue strictly between one and four. Every nonzero eigenpair of the weighted tensor is included in the comparison."),
            Item("ordinary", "actual_nonexception_window", "The ordinary actual-graph window", "For every pair of natural tails at least two except the exact exchanged pair two and six, the actual ideal graph has an eigenvalue in (V-3,V) avoiding V-1 and V-2."),
            Item("exception", "exception_eigenpair", "The exact cubic at the exceptional pair", "Both orderings of tails two and six have the same cubic factor x cubed minus 161x squared plus 5775x minus 35343. It has a genuine tensor eigenvalue strictly between seven and eight, giving graph interval (V-7,V-6)."),
            Item("actual", "four_equal_obstruction", "Every positive tail and coordinate permutation", "The entire positive natural (4,4,b,c) domain on arbitrary distinct prime coordinates is nonintegral. Unit tails reuse the existing actual-graph unit theorem; both exceptional orderings retain their cubic witness. No classification is asserted beyond the stated family.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairFourEndpoints"))]));
}
