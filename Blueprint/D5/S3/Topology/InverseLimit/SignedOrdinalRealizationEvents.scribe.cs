using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalRealizationEventsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SignedOrdinalRealizationEvents", H("Same actual events on the literal realization"), Blocks(
            Describe.Lean(DescribeId.Create("actual-event-prepared-measure-read"),
                DeclarationHandle.Create(Owner + "prepared_measure_read"), H("Whole prepared measure readback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every old prepared whole measure equals the original whole birth on the final literal carrier, with its label and every natural index preserved. Both delayed source and target measures use this same readback."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-event-selected-projection"),
                DeclarationHandle.Create(Owner + "selected_projection"), H("The actual selected projection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The actual selected R literal projection, after final projection to succ(a), equals final projection to the original row transported only across literal carrier equality. The same split and coordinate restriction are used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-event-successor-j"),
                DeclarationHandle.Create(Owner + "successor_J"), H("Same outgoing and incoming J"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At succ(a), original eligible J is exactly the same selected R.J at a. The outgoing R carrier belongs to succ(a), while its J becomes incoming at that stage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-event-ordinary-cofinal"),
                DeclarationHandle.Create(Owner + "ordinary_cofinal"), H("Actual ordinary events on the final prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Arbitrarily late ordinary execution retains the same Treatment and Result, its exact final carrier at succ(a), and every original whole-birth measure at each natural index. That Result retains its quantitative_g, quantitativeClopen and strictly increasing column indices. No oscillation premise is supplied."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-event-delayed-cofinal"),
                DeclarationHandle.Create(Owner + "delayed_cofinal"), H("Actual delayed events on the final prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Intrinsic validity on the final original whole birth yields an actual later delayed event with the identical Task, Result and certificate. Both B supports read back to their original decoded birth pair. The permanent source reservoirs and source J at succ(a) are exactly those of the same R. Its certificate keeps the same M sets and literal clopen; no second split transport is introduced."))), DescribeRole.Theorem),
            Paragraph(Text("These are realization interfaces; final signed and AH endpoint proofs are separate.")))));
}
