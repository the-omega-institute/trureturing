using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ProObjects;

internal sealed class GeneralHomFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Morphisms between presented pro-objects form a limit of stage-map colimits.",
        H("The General Pro-Object Hom Formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("general-pro-object-hom-formula"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ProObjects/GeneralHomFormula."
                        + "pro_category_hom_formula"),
                H("Morphisms are a limit of stage-map colimits"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I and J be small filtered categories. Diagrams X : I^op -> C "
                            + "and Y : J^op -> C present cofiltered pro-objects. For each target "
                            + "stage Y_j, source refinement gives the filtered colimit of the "
                            + "ordinary morphism types X_i -> Y_j.")),
                    Paragraph(Text(
                        "These colimits vary contravariantly with the target stages. Their limit "
                            + "therefore records precisely the compatible target-stage classes, "
                            + "and is canonically equivalent to the morphism type between the two "
                            + "presented pro-objects.")),
                    Paragraph(Text(
                        "Every target component has a representative at one sufficiently refined "
                            + "source stage. When both index categories have one object, the two "
                            + "universal constructions reduce to the ordinary Hom type; in Type, "
                            + "the identity function supplies an explicit inhabitant.")),
                    Paragraph(Text(
                        "The Lean construction reuses the repository pro-object category and the "
                            + "pinned Mathlib Ind inclusion, its fully faithful Hom equivalence, "
                            + "pointwise colimit preservation, and the colimit-Yoneda Hom "
                            + "equivalence."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Hom(Formula category, Formula source, Formula target) =>
        Seq(Operatorname, Grp(F.Id("Hom")), Underscore, Grp(category),
            Open, source, Comma, Sp, target, Close);

    private static Formula TheoremFormula()
    {
        Formula category = F.Id("C");
        Formula sourceIndex = F.Id("I");
        Formula targetIndex = F.Id("J");
        Formula sourceDiagram = F.Id("X");
        Formula targetDiagram = F.Id("Y");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula proCategory = Seq(
            Operatorname, Grp(F.Id("ProObjectCategory")), Open, category, Close);
        Formula presentedSource = Seq(
            Operatorname, Grp(F.Id("presentedObject")), Open, sourceDiagram, Close);
        Formula presentedTarget = Seq(
            Operatorname, Grp(F.Id("presentedObject")), Open, targetDiagram, Close);
        Formula stageHom = Hom(
            category, Sub(sourceDiagram, i), Sub(targetDiagram, j));

        return Disp(Seq(
            Hom(proCategory, presentedSource, presentedTarget), Sp, Equiv, Sp,
            Operatorname, Grp(F.Id("lim")), Underscore, Grp(j), Sp,
            Operatorname, Grp(F.Id("colim")), Underscore, Grp(i), Sp,
            stageHom, Dot));
    }
}
