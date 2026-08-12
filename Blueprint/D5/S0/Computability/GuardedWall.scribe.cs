using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class GuardedWallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A consistent guarded wall cannot become positive while its gatekeepers stay positive.",
        H("Guarded Walls Stay Outside Forbidden Configurations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guarded-walls-never-become-positive"),
                DeclarationHandle.Create("D5/S0/Computability/GuardedWall.wall_never_positive"),
                H("Guarded walls never become positive"),
                StatementSource.FromAuthor(Disp(F.Id("wallNeverPositive"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A wall is a set of statements that must stay outside a forbidden "
                        + "positive configuration. If every gatekeeper is positive, any "
                        + "positive wall statement would make that configuration forbidden. "
                        + "Consistency rules out the forbidden configuration, so every wall "
                        + "statement is necessarily non-positive at every time.")),
                    Paragraph(Text(
                        "The Lean proof is a direct contradiction argument: specialize the "
                        + "forbidden-configuration hypothesis to the wall statement and feed "
                        + "it the gatekeeper positivity witnesses, then apply consistency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boolean-guarded-wall-witness"),
                DeclarationHandle.Create("D5/S0/Computability/GuardedWall.boolean_guarded_wall_witness"),
                H("A Boolean guarded wall has a concrete witness"),
                StatementSource.FromAuthor(Disp(F.Id("booleanGuardedWallWitness"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Boolean instance makes all hypotheses simultaneously explicit: "
                        + "true is the sole positive statement, false is the wall, and the "
                        + "forbidden predicate requires both values at once. The witness "
                        + "therefore certifies the hypotheses and the wall's non-positivity "
                        + "without any numerical or external evidence."))),
                DescribeRole.Theorem))));
}
