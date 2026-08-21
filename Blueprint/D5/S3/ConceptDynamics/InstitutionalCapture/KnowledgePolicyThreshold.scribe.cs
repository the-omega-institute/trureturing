using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class KnowledgePolicyThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Secret recovery and injective secret policies have the same coalition-size threshold.",
        H("Knowledge Policy Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coalition-readout"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold."
                        + "coalitionReadout"),
                H("Coalition readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coalition readout exposes a participant's share exactly when its label "
                        + "belongs to the coalition, using none for absent labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coalition-size-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold."
                        + "knowledge_policy_threshold_consistent"),
                H("Knowledge and policy thresholds agree"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The secret and policy are readouts on the same state space. The policy "
                            + "factors through the secret by a map injective on the secret image, "
                            + "so its values preserve every secret distinction.")),
                    Paragraph(Text(
                        "For each finite coalition, policy factorization is equivalent to secret "
                            + "factorization: the forward direction uses the inverse selected on "
                            + "the secret image, and the reverse direction composes the policy map.")),
                    Paragraph(Text(
                        "Consequently the two sets of attainable coalition cardinalities are equal, "
                            + "and their natural infima, the source minimum thresholds, agree."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula ThresholdFormula()
    {
        Formula share = F.Id("share");
        Formula secret = F.Id("secret");
        Formula policy = F.Id("policy");
        Formula policyFactor = F.Id("policyFactor");
        Formula fullRecovery = F.Id("fullRecovery");
        Formula coalition = F.Id("coalition");
        Formula policyMinimum = Apply("minimumCoalitionSize",
            Apply("Refines", policy, Apply("coalitionReadout", share, coalition)));
        Formula secretMinimum = Apply("minimumCoalitionSize",
            Apply("Refines", secret, Apply("coalitionReadout", share, coalition)));

        return Disp(Seq(
            Forall, Sp, share, Comma, Sp,
            Forall, Sp, secret, Comma, Sp,
            Forall, Sp, policy, Comma, Sp,
            policyFactor, Sp, Land, Sp, fullRecovery, Sp, Rightarrow, Sp,
            policyMinimum, Sp, Eq, Sp, secretMinimum, Dot));
    }
}
