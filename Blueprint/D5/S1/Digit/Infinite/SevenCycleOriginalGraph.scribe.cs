using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleOriginalGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SevenCycleOriginalGraph", H("SevenCycleOriginalGraph"),
        Blocks(Paragraph(Text("The denominator is twenty times 244760. The original seed set retains all state, branch-domain and effective observation endpoints. The endpoint set keeps only scalars in the original support with conjugate absolute value at most the chosen radius.")))));
}
