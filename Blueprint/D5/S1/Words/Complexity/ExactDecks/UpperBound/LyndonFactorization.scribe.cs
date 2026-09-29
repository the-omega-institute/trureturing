using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundLyndonFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite word factors into nonincreasing Lyndon words.",
        H("LyndonFactorization"),
        Blocks(
            Paragraph(Text(
                "This module privately constructs the Chen-Fox-Lyndon factorization by inserting "
                + "successive letters, joining adjacent factors when the required order fails. "
                + "Its specification gives the original flattened word, Lyndonhood of every "
                + "factor, and nonincreasing factor order for the recovery proof.")))));

}
