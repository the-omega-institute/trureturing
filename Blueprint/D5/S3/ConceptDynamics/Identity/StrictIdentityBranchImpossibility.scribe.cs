using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class StrictIdentityBranchImpossibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two distinct objects cannot both be strictly identical to one object.",
        H("Strict Identity Branch Impossibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-identity-branch-impossible"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Identity/StrictIdentityBranchImpossibility."
                        + "strict_identity_branch_impossible"),
                H("Strict identity cannot branch"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier and all three objects are independent source primitives. "
                            + "Strict identity is represented by Lean equality itself.")),
                    Paragraph(Text(
                        "If y and z both equal x, transitivity with the symmetric second "
                            + "equality gives y equal to z, contradicting their distinction.")),
                    Paragraph(Text(
                        "No exact repository or pinned Mathlib theorem states this full "
                            + "three-object implication, so the proof applies the core equality "
                            + "operations directly."))),
                DescribeRole.Theorem))));
}
