using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairSharedRootDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairSharedRoot." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete shared-prime root valuation and resonance", H("Complete shared-prime root valuation and resonance"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("root-ranges", "root_ranges", "Every min/max valuation alternative", "There is no coprimality premise on the tails. Negative root offsets and every good prime are retained."),
            Item("normalized-root-resonance", "normalized_root_resonance", "Constructed normalized cubic resonance", "Integer quotient witnesses are obtained from the actual determinant root. Residue reduction never silently reduces a nonintegral rational."),
            Item("root-first-order", "root_first_order", "First-order offset forces first-order shared tails", "This is the original full first-order obstruction at every good prime."),
            Item("root-unequal-resonance", "root_unequal_resonance", "Both distinct residues for unequal tail valuations", "The theorem constructs the normalized units and both residue alternatives, including their distinctness.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairRootArithmetic")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder"))]));
}
