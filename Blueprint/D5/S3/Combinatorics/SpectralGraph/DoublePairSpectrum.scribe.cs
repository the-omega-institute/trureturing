using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class DoublePairSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/DoublePairSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive double-pair actual ideal graph is nonintegral.", H("Every positive double-pair actual ideal graph is nonintegral."),
        Blocks(
            Paragraph(Text("Source: four-prime-double-pair-completion, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("low", "low_eigenpair", "The full ordered real upper-four interval", "For every real a at least two and b at least a, an eigenpair of the full tensor has eigenvalue in (1,4)."),
            Item("noninteger", "noninteger_eigenpair", "Endpoint exclusion over the entire natural domain", "Both possible integers two and three are excluded by complete source endpoint reductions. The witness belongs to the whole four-cell operator."),
            Item("actual", "double_pair_obstruction", "All positive double pairs and coordinate permutations", "All natural a,b greater than zero are included without an ordering premise. The all-equal diagonal is included. Reindexing carries prime values and exponent coordinates together. The three finer minimum-interval ranges remain separate from this checked nonintegrality conclusion.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/DoublePairCubic"))]));
}
