using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairTailCutoffComparisonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairTailCutoffComparison." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete old/new uniform tail-cutoff comparison", H("The complete old/new uniform tail-cutoff comparison"),
        Blocks(
            Paragraph(Text("Sources: four-prime-large-tail and four-prime-tail-reduction, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All positive repeated and first-tail exponents are retained, with no relative ordering. The old large-tail graph conclusion is reused through the stronger quadratic cutoff; this does not supply the separate original ordered-second-eigenvalue statement or claim to rerun original exact controls. Necessary candidate membership never proves integrality. Original attribution, prerequisites, reported controls, failed methods and general Q3 boundaries remain. The escape audit is unfinished under linked issue #28398.")),
            Item("comparison", "cutoff_comparison", "The full strict improvement by more than 128", "The floor of d squared over four remains actual integer division. The proof establishes 128Q<R for every positive integer a and b."),
            Item("five", "cutoff_five", "Both exact original five/five cutoff values", "The complete values are Q=111375 and R=186913752; this arithmetic is a specialization, not a finite substitute for the uniform theorem."),
            Item("actual", "actual_large_tail", "Every actual ideal graph beyond the old cutoff is nonintegral", "All four distinct graph primes and every positive repeated and first-tail exponent are retained. The stronger full actual-graph quadratic candidate bound supplies the conclusion without a tail scan.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairTailCandidates"))]));
}
