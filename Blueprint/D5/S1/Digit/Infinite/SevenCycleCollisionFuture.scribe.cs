using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionFutureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One tail for every horizon", H("One tail for every horizon"),
        Blocks(Paragraph(Text("The same actual first-source tail survives every finite future test against the fixed rival. Its two original predecessors use labels three and null and admit first colors one and two. Both predecessors lead into the same literal future.")))));
}
