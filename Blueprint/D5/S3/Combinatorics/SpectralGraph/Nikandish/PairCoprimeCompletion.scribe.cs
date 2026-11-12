using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairCoprimeCompletionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairCoprimeCompletion." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete coprime repeated-minimum exclusion", H("Complete coprime repeated-minimum exclusion"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("three-exception", "three_exception", "All endpoint-three arithmetic exceptions", "The complete possibilities a=6,7,12,22 follow from the actual determinant-root condition and the stated coprimality."),
            Item("small-three-nonzero", "small_three_nonzero", "All eleven original unbounded quadratic rows", "All eleven source rows are retained. Two additional exact a=7 rows prove that branch directly; they do not replace the distinct general modular theorem. The other tail is unbounded."),
            Item("actual-nonintegral", "actual_nonintegral", "Actual graph obstruction on the entire coprime source domain", "The actual four-prime graph retains all original positive and repeated-minimum conditions. No bounded tail rectangle replaces the universal conclusion.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairLowArithmetic"))]));
}
