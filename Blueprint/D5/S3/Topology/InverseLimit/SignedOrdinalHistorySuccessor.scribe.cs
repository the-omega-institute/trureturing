using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistorySuccessorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistorySuccessor.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successor extension of one actual past", H("Successor extension of one actual past"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistorysuccessor-0"),
                DeclarationHandle.Create(Owner + "next_coherent"), H("Exact adjacent coherence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The actual selected Result is the next literal Prefix and its nextP is the next predecessor. The next clopen table is read from the same current whole birth pack. All older U, V and nu fields agree by literal carrier transport. The permanent arrival uses the same Result.N at its outgoing maximum stage. Its oldI and oldJ give the required refinement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalhistorysuccessor-1"),
                DeclarationHandle.Create(Owner + "next_coherent_earlier"), H("Preservation of every earlier state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If the current state is coherent with an earlier state, advancing its actual selected Result preserves that coherence. Whole birth equality composes through the current old pack; older arrival entries are retained exactly. The one-sided almost inclusions of I and J compose. No replacement history or extension witness is supplied as a premise."))), DescribeRole.Theorem))));
}
