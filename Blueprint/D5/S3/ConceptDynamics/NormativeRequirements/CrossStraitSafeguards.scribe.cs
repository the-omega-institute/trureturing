using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeRequirements;

internal sealed class CrossStraitSafeguardsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/NormativeRequirements/CrossStraitSafeguards.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional cross-strait judgments distinguish unification goals, means, consent, and rights.",
        H("Cross-Strait Safeguards"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unification-aim-does-not-replace-consent"),
                DeclarationHandle.Create(Prefix + "unification_aim_does_not_replace_consent"),
                H("A unification aim does not supply a necessary consent premise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume endorsement requires the freely expressed consent of Taiwan residents. "
                    + "If a proposal serves a unification aim but lacks that consent, it is not "
                    + "endorsed under this standard, and the aim is not a sufficient criterion. "
                    + "The theorem supplies no polling data, historical entitlement, sovereignty "
                    + "ruling, or premise that a particular real proposal lacks consent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("failed-cross-strait-safeguard-excludes-endorsement"),
                DeclarationHandle.Create(Prefix + "failed_cross_strait_safeguard_excludes_endorsement"),
                H("A failed safeguard excludes endorsement under the stated standard"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the explicit premise that endorsement requires peaceful implementation, "
                    + "residents' consent, and protection of basic rights, failure of any one "
                    + "excludes endorsement. This is a chosen evaluative standard, not a complete "
                    + "definition of international legality or a uniquely proved moral theory. "
                    + "No voting population, threshold, or measurement method is silently fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unification-outcome-does-not-determine-endorsement"),
                DeclarationHandle.Create(Prefix + "unification_outcome_does_not_determine_endorsement"),
                H("The final arrangement alone need not determine endorsement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two proposals lead to one arrangement, one is endorsed, and the other "
                    + "violates a necessary safeguard, endorsement cannot be a function of the "
                    + "arrangement alone. Both the equal-arrangement comparison and the endorsement "
                    + "premise remain explicit. The argument applies the reusable safeguard theorem "
                    + "without independently reproving its factorization step."))),
                DescribeRole.Theorem))));
}
