using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairRootArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairRootArithmetic." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full integer-root division and valuation", H("Full integer-root division and valuation"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("root-division", "root_division", "Exact full determinant division", "The identity is over every commutative ring. The root offset may be negative; zero-tail substitutions are polynomial identities, not graph parameters."),
            Item("root-divides", "root_divides", "Every integer root gives the original divisibility condition", "The determinant is of the full repeated-pair tensor. No arbitrary scalar root premise replaces a graph conclusion; PairLowArithmetic supplies the actual integrality consumer."),
            Item("root-valuation", "root_valuation", "Exact good-prime valuation for coprime positive tails", "Every positive integer exponent and every integer root s>=2 are retained. The good-prime exclusion is exactly s(s-1)(2s-1), and valuations use the absolute value of a possibly negative offset.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
