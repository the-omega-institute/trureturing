using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class IffRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact iff registrations over finite object states.",
        H("IffRegistrations"),
        Blocks(
            Node("unsettledCode", "The shared constructor-written zero in Fin 5 codes the unsettled claim.", DescribeRole.Definition),
            Node("openPermissionReadout", "Pinned finite equality with unsettledCode gives the Boolean table for open-outcome permission after decoding each claim.", DescribeRole.Definition),
            Node("openUnsettledReadout", "Pinned finite equality with unsettledCode gives the Boolean table for the decoded claim being unsettled.", DescribeRole.Definition),
            Node("openCodeArena", "Fin 5 re-coordinates every Claim in order: unsettled, nonformalJudgment, consequentUnderConditions, assertP, assertNegP. All four non-unsettled claims remain in the arena.", DescribeRole.Definition),
            Node("openRealization", "The explicit iff template receives separate permission and unsettled Boolean readouts on all five codes.", DescribeRole.Definition),
            Node("open_bridge", "Local encode and decode maps form Claim ≃ Fin 5 via decodeEncode and encodeDecode. leftDecoded and rightDecoded independently identify the readouts with the decided original permission and unsettled predicates at every code. pointwise uses Bool.eq_iff_iff to transport Boolean equality to the original iff, and the coordinate equivalence transports its universal quantifier.", DescribeRole.Theorem),
            Node("open_lawSensitive", "The frozen open-permission characterization satisfies the encoded law; constant true and false readouts falsify it at the unsettled code.", DescribeRole.Theorem),
            Node("open_slotSensitive", "Both Boolean readout slots have checked sensitivity witnesses.", DescribeRole.Theorem),
            Node("dualFixedReadout", "Pinned Boolean equality compares both coordinates of a Convention to read duality fixedness.", DescribeRole.Definition),
            Node("dualAlternativesReadout", "Bool.rec selects the second coordinate's equality to false or true according to the first coordinate, reading the FvF or AvA alternatives.", DescribeRole.Definition),
            Node("dualArena", "The source state is one of the four Boolean tie-breaking conventions.", DescribeRole.Definition),
            Node("dualRealization", "The explicit iff template receives dualFixedReadout and dualAlternativesReadout on the unchanged Convention carrier.", DescribeRole.Definition),
            Node("dual_bridge", "leftIff and rightIff independently check fixedness and the FvF or AvA alternatives in all four Boolean cases. pointwise uses Bool.eq_iff_iff to identify equality of the readouts with the original iff, without using dual_fixed_iff inside the bridge.", DescribeRole.Theorem),
            Node("dual_lawSensitive", "The frozen dual-fixed characterization satisfies the law; constant true and false readouts falsify it.", DescribeRole.Theorem),
            Node("dual_slotSensitive", "Both Boolean readout slots have checked sensitivity witnesses.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/IffRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
