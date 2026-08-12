using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class GoldenFractionalPartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Natural golden-rotation indices have canonical fractional representatives.",
            H("Golden Fractional Part"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Dynamics/GoldenFractionalPart"),
                    Text(" assigns each natural index "),
                    Math(Id("n")),
                    Text(" the fractional part of its golden-ratio multiple.")),
                new DocumentBlock.DisplayFormula(
                    Equal(
                        Call("goldenFractionalPart", Id("n")),
                        Call("fract", Multiply(Id("n"), new Formula.Phi())))))));
}
