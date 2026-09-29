using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The upper arch involution, midpoint winding and lower rainbow connectivity encode the OEIS semi-meander model.",
        H("The Semi-Meander Model"),
        Blocks(
            Paragraph(Text("Upper matchings are fixed-point-free noncrossing involutions on twice n endpoints. "
                + "The winding counts arches crossing the midpoint once each. The one-loop predicate "
                + "uses upper pairing steps and the fixed lower rainbow. The corresponding formal "
                + "definition is presented with the all-order count."))),
        []));
}
