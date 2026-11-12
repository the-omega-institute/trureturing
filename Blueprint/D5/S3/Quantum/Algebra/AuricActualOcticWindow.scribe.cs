using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricActualOcticWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual window construction uses an arbitrary field extension and the original multiplication.",
        H("Actual arbitrary octic window"),
        Blocks(Paragraph(Text(
            "Let D/F be an arbitrary characteristic zero field extension of degree eight and W an arbitrary "
            + "four dimensional F subspace. The quotient set consists of u/v with u and v in W and v nonzero, "
            + "and includes zero. For a outside this set, multiplication by a followed by the actual quotient "
            + "D/W is injective on W and hence an isomorphism. Composing its inverse with inclusion and "
            + "quotient gives the original F linear operator with square zero and image and kernel W. "
            + "No element one is required in W. The strict embedding rank and cut-free conclusions require "
            + "the scalar-only multiplication idealizer of this same actual W."))),
        [])));
}
