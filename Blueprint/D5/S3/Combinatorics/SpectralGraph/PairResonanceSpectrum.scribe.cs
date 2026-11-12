using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairResonanceSpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/PairResonanceSpectrum." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete residue tables and unbounded actual resonant family", H("Complete residue tables and unbounded actual resonant family"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("complete-table-five", "complete_table_five", "All five residues at root two", "The complete passing residues are zero and two. This kernel-checked table is not an exponent scan."),
            Item("complete-table-seven", "complete_table_seven", "All seven residues at root three", "The complete passing residues are zero, three and five."),
            Item("actual-progression", "actual_progression", "All n,m and the full large-tail ray", "The actual graph has a=6+25n, b=20+100n+125m and every c>=2a-2. Equality is included and no tail coprimality or relative ordering is introduced.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairResonanceLocal")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairLowArithmetic"))]));
}
