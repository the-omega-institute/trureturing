using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class LayerShiftNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Computability/LayerShiftNaturality",
            "A layer-shift natural transformation commutes with every lifting morphism."),
        H("Layer Shift Is Natural"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("layer-shift-commutes-with-lifting-morphisms"),
                H("Layer shift commutes with lifting morphisms"),
                LeanTheorem(
                    "D5/S0/Computability/LayerShiftNaturality.layer_shift_naturality"),
                Disp(Seq(
                    F.Id("shift"), Underscore, Grp(F.Id("Y")), Sp, Circ, Sp,
                    F.Id("Current"), Open, F.Id("f"), Close,
                    Sp, Eq, Sp,
                    F.Id("Shifted"), Open, F.Id("f"), Close, Sp, Circ, Sp,
                    F.Id("shift"), Underscore, Grp(F.Id("X")))),
                DescribeProvenance.RepoDerived(),
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
                        "The pinned Mathlib source was searched before proving. Its "
                        + "CategoryTheory.NatTrans.naturality declaration is exactly the "
                        + "required commuting square, so the Lean theorem is a declared "
                        + "thin honest wrapper with no reconstructed category-theory proof. "
                        + "The formal scope is the source atom's compatibility claim: "
                        + "mechanism-specific status labels are not added to the categorical "
                        + "statement. The claim is structural and universal, so there is no "
                        + "numerical certificate to mirror.")))
            ))));
}
