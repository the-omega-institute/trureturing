using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MembershipRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact annihilator membership registrations over four frequencies.",
        H("MembershipRegistrations"),
        Blocks(
            Paragraph(Text("These registrations retain the annihilator membership predicate and decide it by finite modular multiplication, using the standard character's primitivity. No finite seal is supplied; the registration diagnostics remain visible.")),
            Node("objectArena", "Both frozen statements use the same four-frequency object arena and catalog.", DescribeRole.Definition),
            Node("memberArena", "Positive polarity requires the anchor to belong to the supplied set.", DescribeRole.Definition),
            Node("nonmemberArena", "Negative polarity requires the anchor to lie outside the supplied set.", DescribeRole.Definition),
            Node("member_slotSensitive", "The positive law has independently checked membership-readout and anchor support.", DescribeRole.Theorem),
            Node("nonmember_slotSensitive", "The negative law has independently checked membership-readout and anchor support.", DescribeRole.Theorem),
            Node("twoRealization", "The original annihilator membership predicate is retained with anchor two, using computable kernel membership and a finite universal test for zero modular products.", DescribeRole.Definition),
            Node("two_bridge", "The bridge preserves the frozen statement that frequency two belongs to the annihilator.", DescribeRole.Theorem),
            Node("two_lawSensitive", "The frozen membership theorem satisfies the law; changing the anchor to one falsifies it by the frozen exclusion theorem.", DescribeRole.Theorem),
            Node("oneRealization", "The same original annihilator membership predicate is retained with anchor one.", DescribeRole.Definition),
            Node("one_bridge", "The bridge preserves the frozen statement that frequency one does not belong to the annihilator.", DescribeRole.Theorem),
            Node("one_lawSensitive", "The frozen exclusion theorem satisfies the law; changing the anchor to two falsifies it by the frozen membership theorem.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
