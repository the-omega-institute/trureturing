using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryLimit.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual proper-limit advancement of one strict past", H("Actual proper-limit advancement"), Blocks(
            Describe.Lean(DescribeId.Create("actual-history-limit-archive"),
                DeclarationHandle.Create(Owner + "archive"), H("Canonical strict-past archive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a proper limit a above omega and one pairwise coherent strict past, Archive reads the full canonical Q at each born row and the actual selected R at max(row,label). The successor arrival of every such R lies strictly before a. Its Data are exactly the already proved strict Data, including the original incoming I/J. The base onto invariant comes from the actual earlier stage omega. There is no supplied complete history or promised future extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-history-limit-state"),
                DeclarationHandle.Create(Owner + "limitState"), H("Retain the same actual limit event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The approved proper-limit constructor is called on that strict Archive and its proven Laws. The resulting State retains its actual Extension, exact I/J and carrier readbacks, original births, regular bounded F and DI/DJ. Whole U/B/V/nu are carried together through literal carrier equality. One outgoing Q is then prepared once and one actual ordinary or delayed Result is selected on that same Q."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-history-limit-coherence"),
                DeclarationHandle.Create(Owner + "limit_coherent"), H("Coherence with every actual earlier state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The constructed limit State extends every state of its own strict past: exact carriers and canonical whole births agree, permanent N equals the unique earlier R arrival, and incoming I/J almost refine every eligible old set. Regular bounded F is obtained from that same Extension.F before the weaker predecessor interface can discard its output regularity and bound."))), DescribeRole.Theorem))));
}
