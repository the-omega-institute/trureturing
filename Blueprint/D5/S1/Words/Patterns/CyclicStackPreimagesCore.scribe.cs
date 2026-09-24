using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class CyclicStackPreimagesCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal consecutive cyclic stack map preserves entries and obeys the target-order barrier.",
        H("Consecutive Cyclic-Stack Semantics and Barriers"),
        Blocks(
            Paragraph(Text(
                "The stack is written top-first. An incoming value x is forbidden above a,b "
                    + "exactly when x<a<b, b<x<a, or a<b<x, representing 123, 231, and 312. "
                    + "The drain operation pops the top and repeats this test until a push is "
                    + "allowed, so it removes the shortest forced prefix. Processing then pushes "
                    + "x and continues with the remaining input; exhausted input flushes the "
                    + "stack top-first. This is the convention of Zhan and Bie's Figure 3, "
                    + "where 3124 maps to 4213.")),
            Paragraph(Text(
                "The prefix operation run records both the emitted output and the remaining "
                    + "stack. Its append law and its relation to process express composition of "
                    + "successive input prefixes. Processing preserves the permutation of the "
                    + "input together with the initial stack.")),
            Paragraph(Text(
                "For m=floor(n/2), the target is (1,...,m,n,...,m+1). Every low entry precedes "
                    + "every high entry in this output, and the lows increase. Entries already "
                    + "on a stack keep their top-to-bottom order in future output. Consequently "
                    + "a high entry above a low entry cannot occur in a successful residual "
                    + "stack. The resulting barrier controls drains while a low remains and "
                    + "excludes consecutive low entries after a high in a successful input.")))));
}
