using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class PairTailCandidatesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite candidate sets and uniform effective bounds.", H("Complete finite candidate sets and uniform effective bounds."),
        Blocks(
            Paragraph(Text("Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.")),
            Item("count", "candidate_card", "The complete fixed-pair candidate count", "All roots at all d-1 offsets are retained in the finite set. The cardinal is at most 2(d-1); no convenient finite sample replaces the candidate domain."),
            Item("harmonic-count", "harmonic_card", "The full sharpened b-1 candidate count", "Positive-root uniqueness at every harmonic offset reduces the complete set to at most b-1 candidates. The empty b=1 case remains included."),
            Item("actual", "actual_mem", "Every actual integral tail belongs to the complete set", "Every positive free tail with actual graph integral spectrum lies in the full fixed-pair candidate set, uniformly over arbitrary distinct prime coordinates."),
            Item("harmonic-actual", "actual_harmonic_mem", "All unequal integral tails belong to the smaller set", "For b<c the complete harmonic set is necessary for actual integrality. This is no classification in variable a,b."),
            Item("effective", "actual_le_cutoff", "The full floor-square cutoff", "The entire actual integral domain obeys c<=U[U+a(d-1)+a squared b], with d=(a+1)b and U=floor(d squared/4). Larger tails are excluded without scanning them."),
            Item("harmonic-bound", "actual_le_harmonic", "The full sharpened harmonic cutoff", "For a>=3 and b<c the exact maximum of the source constant at T=2b-1 gives the smaller effective upper bound. Equality in the offset estimate is retained.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum"))]));
}
