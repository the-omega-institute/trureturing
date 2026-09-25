using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal digit blocks preserve lower coefficients and expose leading coordinates.",
        H("CentralDigitData"),
        Blocks(
            Paragraph(Text(
                "For each length r, ActualLyndonWord is the subtype of actual words of length r "
                + "that satisfy IsLyndon. The module publicly installs a lifted linear order on "
                + "this subtype and, for finite A, a Fintype instance obtained by injection into "
                + "length-r vectors. These two anonymous public instances support the cardinality "
                + "and deterministic selection below; the digit construction itself is a "
                + "repository result, not a claim attributed to the cited paper.")))));

}
