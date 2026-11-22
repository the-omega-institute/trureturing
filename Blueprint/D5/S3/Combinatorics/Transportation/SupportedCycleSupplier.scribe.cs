using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;
internal sealed class SupportedCycleSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge.", H("SupportedCycleSupplier"), Blocks(
        Describe.Lean(DescribeId.Create("simple-cycle"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle"),
            H("A simple cycle of target disagreements"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge."))), DescribeRole.Theorem),
        Paragraph(Text("The supplier follows the consumed cycle-extraction proof of Guanyang Wang in KTV at immutable revision 15b5f47c9ac833bfdf99b8b29374af7a678ef4bc. Its MIT copyright and license are retained with the Lean source. Finite iteration supplies a repeated positive disagreement. A shortest alternating closed walk has no repeated row or column, since either repetition would cut out a shorter closed walk. No mathematical priority claim is made.")))));
}
