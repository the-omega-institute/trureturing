using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ConvexBarrier;

internal sealed class ScalarMechanismDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repository-derived formalization of the power-cone analytic and geometric support path.",
        H("ScalarMechanism"),
        Blocks(Paragraph(Text("The machine-checked module is retained as a repository-derived formalization.")))));
}
