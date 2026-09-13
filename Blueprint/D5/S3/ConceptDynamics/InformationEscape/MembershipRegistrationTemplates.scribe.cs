using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MembershipRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact membership registration at an explicit object anchor.",
        H("MembershipRegistrationTemplates"),
        Blocks(
            Node("membershipSignature", "An ADMIT membership readout and an ANCHOR retain the set and the tested element separately.", DescribeRole.Definition),
            Node("membershipRealization", "The readout decides membership in the supplied set without substituting proven facts; the anchor is the supplied element.", DescribeRole.Definition),
            Node("membershipArena", "A polarity selector requires membership or nonmembership at the anchor of an explicit finite object arena.", DescribeRole.Definition),
            Node("membershipLegacy", "The original membership or nonmembership proposition is equivalent to its Boolean readout law by decidable reflection.", DescribeRole.Theorem),
            Node("membership_sensitivity", "Distinct object states witness independent sensitivity of the membership readout and anchor for either polarity.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/MembershipRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
