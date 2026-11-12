using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairGapSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairGapSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full high-root windows and actual graph nonintegrality.", H("Full high-root windows and actual graph nonintegrality."),
        Blocks(
            Paragraph(Text("Source: the four small-gap and midpoint notes, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("small-root", "small_gap_eigenpair", "Both full small-gap root windows", "Every positive natural a,b with tail gap one or two has a genuine K eigenpair in (a+b+1,a+b+2)."),
            Item("square-root", "square_gap_eigenpair", "All original square-size half-unit windows", "Every positive natural a,b,r with r>=2 and b>=r squared has a full operator eigenpair in (a+b+(r+1)/2,a+b+(r+2)/2)."),
            Item("weighted-root", "weighted_gap_eigenpair", "All original weighted half-unit windows", "The same full half-unit interval holds at every positive natural a,b with r>=3 and 4ab>=(2a+1)r squared. Equality is included."),
            Item("even-root", "even_gap_eigenpair", "The complete parity-aware sign window", "Every positive natural a,b with r>=2 and 8ab>=(2a+1)r squared has a full K eigenpair in (a+b+r/2,a+b+r/2+1). This sign-window result alone does not assert nonintegrality for odd r."),
            Item("small", "actual_small_gap", "Actual graphs for all gap-one/two families", "All positive a,b and arbitrary distinct prime coordinates are nonintegral. No relative-size premise is used."),
            Item("square", "actual_square_gap", "All actual square-size cases", "The genuine graph lift V+1-kappa gives nonintegrality over the entire original size domain and both parities."),
            Item("weighted", "actual_weighted_gap", "All actual weighted half-unit cases", "The complete original domain and equality boundary lift to the actual ideal graph. No root uniqueness or broader classification follows."),
            Item("even", "actual_even_gap", "All actual even-gap cases", "Even r is explicitly required to exclude integers from the full unit interval. Equality in the weighted condition and r=2 are included.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairGapSigns"))]));
}
