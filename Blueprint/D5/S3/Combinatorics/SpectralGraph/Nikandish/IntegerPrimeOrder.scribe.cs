using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class IntegerPrimeOrderDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact prime orders for signed integer arithmetic", H("Exact prime orders for signed integer arithmetic"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open.")),
            Item("valuation-of-exact", "valuation_of_exact", "Exact divisibility order equals the valuation", "The exact-order predicate handles arbitrary signed integers and is connected to padicValInt, rather than being an answer-encoding premise."),
            Item("unit-decomposition", "unit_decomposition", "Constructed integer unit after exact prime scaling", "A quotient witness and nondivisibility are both produced from the original exact order."),
            Item("equal-of-high-remainder", "equal_of_high_remainder", "Two orders coincide under a strictly higher remainder", "This general integer lemma is consumed by the full shared-prime root proof, with all exponent comparisons established there.")),
        []));
}
