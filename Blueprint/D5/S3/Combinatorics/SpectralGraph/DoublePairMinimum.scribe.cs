using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class DoublePairMinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/DoublePairMinimum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full sharp minimum intervals of the double-pair family", H("Full sharp minimum intervals of the double-pair family"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("minimum-window", "minimum_window", "A true minimum of the entire operator", "The theorem produces a nonzero full eigenvector and compares its eigenvalue with every eigenpair of the same operator."),
            Item("low-region", "low_region", "The complete lower tail region", "The original integer parameter domain and all threshold conditions are retained."),
            Item("middle-region", "middle_region", "The complete middle region with its endpoint boundary", "The full source intervals and integer endpoint exclusions are retained."),
            Item("high-region", "high_region", "The complete high region through the source cutoff", "Every original natural parameter a>=5 and a<=b<=H(a) is retained."),
            Item("unit-region", "unit_region", "The full a=1 tail ray", "Every positive integer tail is retained.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/DoublePairSpectrum")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedTensorMinimum"))]));
}
