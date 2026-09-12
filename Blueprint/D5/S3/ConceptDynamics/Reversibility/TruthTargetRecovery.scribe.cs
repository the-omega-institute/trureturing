using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class TruthTargetRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A left inverse recovers every Boolean truth target of the original state.",
        H("Truth Target Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truth-target-recovers"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Reversibility/TruthTargetRecovery.truth_target_recovers"),
                H("Truth Target Recovery"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The state carrier and recorded carrier are arbitrary. A total map R is supplied with R(U(x)) = x for every original state x. Applying the existing all-target recovery theorem to a Boolean-valued target yields truth = (truth composed with R) composed with U.")),
                    Paragraph(Text("Here a truth value is a fixed Boolean function of the original state. Recoverability does not assert that the same predicate has an unchanged value on the evolved state. It also does not give a local observer access to R or establish reversibility of any physical universe."))),
                DescribeRole.Theorem))));
}
