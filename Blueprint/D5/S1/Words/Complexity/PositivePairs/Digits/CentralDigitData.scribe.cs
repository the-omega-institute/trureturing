using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal digit blocks preserve lower coefficients and expose leading coordinates.",
        H("CentralDigitData"),
        Blocks(
            Paragraph(Text(
                "This module proves the private coefficient bookkeeping for one digit block, "
                + "one selected direction, and the complete direction-major word. It shows that "
                + "the construction preserves every lower-degree coefficient and records the "
                + "exact degree-r difference consumed by the final injectivity theorem.")))));

}
