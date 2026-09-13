using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class SignedProfileRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Spatial Profile Realization.",
        H("Signed Spatial Profile Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signedprofilerealization-exists-signed-profile"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/SignedProfileRealization.exists_signed_profile"),
                H("Simultaneous realization in every spatial fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In every finite dimension, each finitely supported integer spatial profile is the "
                    + "selected spatial charge of a finite rich history. All archived events are current, "
                    + "occur at time zero, lie in the support of the profile, and have empty causality. "
                    + "The entire current region has zero spatial charge and is globally balanced. "
                    + "At each supported position, equally many positive and negative events are created, "
                    + "and the events whose sign agrees with the prescribed coefficient are selected. "
                    + "A zero profile gives an empty archive."))),
                DescribeRole.Theorem))));
}
