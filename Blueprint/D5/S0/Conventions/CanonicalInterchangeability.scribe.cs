using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class CanonicalInterchangeabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful digit specifications are canonically interchangeable through decoding.",
        H("Canonical Interchangeability"),
        Blocks(
            Paragraph(
                Text("For any two faithful digit specifications whose word carriers decode equivalently to natural numbers, composing the decodings gives a bijection of digit words and a commuting decoding triangle.")),
            Paragraph(
                Text("Every property factoring only through decoding is independent of the specification choice; the W-digit specification "),
                Ref("D5/S0/Conventions/WDigits"),
                Text(" is a concrete witness to the quantified domain.")))));
}
