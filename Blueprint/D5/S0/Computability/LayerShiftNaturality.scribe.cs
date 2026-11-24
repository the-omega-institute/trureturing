using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class LayerShiftNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A layer-shift natural transformation commutes with every lifting morphism.",
        H("Layer Shift Is Natural"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("layer-shift-commutes-with-lifting-morphisms"),
                DeclarationHandle.Create("D5/S0/Computability/LayerShiftNaturality.layer_shift_naturality"),
                H("Layer shift commutes with lifting morphisms"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("shift"), Underscore, Grp(F.Id("Y")), Sp, Circ, Sp,
                    F.Id("Current"), Open, F.Id("f"), Close,
                    Sp, Eq, Sp,
                    F.Id("Shifted"), Open, F.Id("f"), Close, Sp, Circ, Sp,
                    F.Id("shift"), Underscore, Grp(F.Id("X"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the objects and morphisms of a category encode one layer's "
                        + "objects and their lifting maps. A current-layer interpretation "
                        + "and a shifted-layer interpretation are connected by a natural "
                        + "transformation. For every lifting morphism, the theorem states "
                        + "that applying the current interpretation and then shifting is "
                        + "equal to shifting first and applying the shifted interpretation. "
                        + "Thus the layer shift is independent of which endpoint of the "
                        + "lifting map is used to compute the comparison.")),
                    Paragraph(Text(
                        "The category operations satisfy the identity and associativity laws, "
                        + "and both interpretations preserve identities and composition. "
                        + "The transformation supplies the commuting-square law for every "
                        + "morphism. The proof applies that law to the given lifting map."))),
                DescribeRole.Theorem))));
}
