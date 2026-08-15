using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Classification;

internal sealed class SubobjectClassifierCoordinateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A subobject classifier bijectively coordinates subobjects by characteristic morphisms.",
        H("Subobject Classifier Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("subobject-classifier-coordinate-bijection"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Classification/SubobjectClassifierCoordinate."
                    + "subobject_classifier_coordinate_bijection"),
                H("Characteristic morphisms bijectively coordinate subobjects"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("classifier"), Colon, Sp,
                    Operatorname, Grp(F.Id("SubobjectClassifier")), Open, F.Id("C"), Close,
                    Comma, Sp, Forall, Sp, F.Id("X"), InMacro, Sp, F.Id("C"), Comma, Esc,
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Open, F.Id("characteristic"), Colon, Sp,
                    Operatorname, Grp(F.Id("Hom")), Open, F.Id("X"), Comma, Sp,
                    Omega, Underscore, Grp(F.Id("classifier")), Close, Close,
                    Sp, Mapsto, Sp,
                    Operatorname, Grp(F.Id("pullback")), Open,
                    F.Id("characteristic"), Comma, Sp,
                    Operatorname, Grp(F.Id("truth")), Underscore,
                    Grp(F.Id("classifier")), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a category with pullbacks and a chosen subobject classifier, "
                            + "pulling back the truth subobject along a morphism from X into "
                            + "Omega produces a subobject of X. The map is bijective, so every "
                            + "subobject has one characteristic morphism and distinct "
                            + "subobjects receive distinct coordinates.")),
                    Paragraph(Text(
                        "Pinned Mathlib already packages this map as the homEquiv field of "
                            + "Subobject.Classifier.representableBy. The Lean theorem applies "
                            + "that exact equivalence's bundled bijectivity result; it does not "
                            + "reprove the representability theorem or introduce a competing "
                            + "notion of classification."))),
                DescribeRole.Theorem))));
}
