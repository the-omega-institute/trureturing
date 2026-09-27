using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryResetEstimatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryResetEstimates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-step common mass.",
        H("Three-step common mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parryresetestimates-parry-three-step-minorization"),
                DeclarationHandle.Create(Prefix + "parry_three_step_minorization"),
                H("Three-step common mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k >= 2, every state s in State k, and every sign a in Bool, put "
                    + "p = parryParameter k and let z be the zero suffix in Fin k. Then the three-step kernel "
                    + "satisfies (kernel k p)^3(s,(a,z)) >= 1/8. The paths 000 and 010 reach respectively the "
                    + "complementary and unchanged zero-suffix signs; each path product is p^3 divided by the "
                    + "starting suffix weight, and each is at least 1/8. Consequently the two zero-suffix states "
                    + "carry at least common mass 1/4 in every three-step row."))),
                DescribeRole.Theorem))));
}
