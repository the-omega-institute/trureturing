using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryStateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryState.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual states and strict-past coherence", H("Actual states and strict-past coherence"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistorystate-0"),
                DeclarationHandle.Create(Owner + "State"), H("Incoming stage and outgoing birth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A proper stage state contains its literal Prefix, actual Predecessor, incoming initial, successor or limit evidence, regular bounded F, and one selected outgoing event. A limit incoming record retains the entire actual Extension, not merely its resulting predecessor. Coherence compares exact earlier carriers, whole birth packs, permanent max(row,label) arrivals and eligible almost inclusions of I and J. The initial finite and omega carriers remain the full coordinate cubes. This state type by itself asserts no global existence."))), DescribeRole.Definition))));
}
