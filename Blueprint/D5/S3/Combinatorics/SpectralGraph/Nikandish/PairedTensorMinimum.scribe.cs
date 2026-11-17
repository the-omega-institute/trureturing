using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class PairedTensorMinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairedTensorMinimum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine minimum of every positive real four-cell tensor.", H("The genuine minimum of every positive real four-cell tensor."),
        Blocks(
            Paragraph(Text("Source: original repeated-pair notes and Mathlib Hermitian eigenbasis, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("minimum", "minimum", "Every nonzero tensor eigenpair participates in the comparison", "The actual full four-dimensional weighted tensor has a nonzero real minimum eigenpair above one for every positive real a,b,c. Diagonal similarity transports every eigenpair into the complete finite Hermitian spectrum. This common consumed helper supports the original balanced and zero-constant smallest-root claims.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions"))]));
}
