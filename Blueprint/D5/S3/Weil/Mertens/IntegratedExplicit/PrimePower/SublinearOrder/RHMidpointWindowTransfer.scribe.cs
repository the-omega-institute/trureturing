using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMidpointWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer of weighted midpoint estimates to signed prime windows",
        H("The arithmetic limsup from a weighted midpoint comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-window-midpoint-transfer"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer.signed_window_midpoint_transfer"),
            H("The same remainder profile controls the normalized signed window"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A uniform upper comparison and a signed lower comparison at center zero "
                    + "for the normalized exponential root average imply an estimate for the "
                    + "limsup of the original signed prime-window discrepancy. The limit is taken "
                    + "over late starting points at each fixed width.")),
                Paragraph(Text("Absolute summability makes both the whole weighted interval and its midpoint "
                    + "continuous functions of the same actual phase vector. A cofinal return "
                    + "transfers the lower comparison at the origin. The arithmetic term tends "
                    + "to zero after division by the original positive power gap."))),
            DescribeRole.Theorem))));
}
