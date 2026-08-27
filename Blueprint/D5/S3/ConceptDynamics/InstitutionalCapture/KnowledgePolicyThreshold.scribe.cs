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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula ThresholdFormula()
    {
        Formula participantType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula shareType = F.Id("V");
        Formula secretType = F.Id("B");
        Formula policyType = F.Id("U");
        Formula share = F.Id("share");
        Formula secret = F.Id("secret");
        Formula policy = F.Id("policy");
        Formula policyFactor = F.Id("policyFactor");
        Formula fullRecovery = F.Id("fullRecovery");
        Formula coalition = F.Id("K");
        Formula policyMap = F.Id("policyMap");
        Formula type = F.Id("Type");
        Formula finsetI = Apply("Finset", participantType);
        Formula coalitionReadout = Apply("coalitionReadout", share, coalition);
        Formula policyFactorLaw = Seq(
            Exists, Sp, policyMap, Colon, Sp, Arrow(secretType, policyType), Comma, Sp,
            policy, Sp, Eq, Sp, policyMap, Sp, Circ, Sp, secret, Sp, Land, Sp,
            Apply("InjOn", policyMap, Apply("range", secret)));
        Formula fullRecoveryLaw = Apply(
            "Refines",
            secret,
            Apply(
                "coalitionReadout",
                share,
                Seq(Open, F.Id("univ"), Colon, Sp, finsetI, Close)));
        Formula policyMinimum = Apply(
            "minimumCoalitionSize",
            Grp(
                Lambda, Sp, coalition, Colon, Sp, finsetI, Comma, Sp,
                Apply("Refines", policy, coalitionReadout)));
        Formula secretMinimum = Apply(
            "minimumCoalitionSize",
            Grp(
                Lambda, Sp, coalition, Colon, Sp, finsetI, Comma, Sp,
                Apply("Refines", secret, coalitionReadout)));

        return Disp(Seq(
            Forall, Sp,
            participantType, Comma, Sp, stateType, Comma, Sp, shareType, Comma, Sp,
            secretType, Comma, Sp, policyType, Colon, Sp, type, Comma, Esc,
            Typeclass("Fintype", participantType), Comma, Sp,
            Typeclass("DecidableEq", participantType), Comma, Sp,
            Typeclass("Nonempty", secretType), Comma, Esc,
            share, Colon, Sp, Arrow(participantType, Arrow(stateType, shareType)), Comma, Sp,
            secret, Colon, Sp, Apply("Concept", stateType, secretType), Comma, Sp,
            policy, Colon, Sp, Apply("Concept", stateType, policyType), Comma, Esc,
            policyFactor, Colon, Sp, Grp(policyFactorLaw), Comma, Esc,
            fullRecovery, Colon, Sp, fullRecoveryLaw, Comma, Esc,
            policyMinimum, Sp, Eq, Sp, secretMinimum, Dot));
    }
}
