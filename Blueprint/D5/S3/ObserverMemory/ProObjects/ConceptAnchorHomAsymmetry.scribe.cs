using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ProObjects;

internal sealed class ConceptAnchorHomAsymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant-object morphisms in a presented pro-object compute as a stage colimit and a stage limit.",
        H("Constant-Object Hom Formulas for Presented Pro-Objects"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-anchor-hom-asymmetry"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry."
                        + "concept_anchor_hom_asymmetry"),
                H("The two constant-object Hom formulas"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be a small filtered category and let X : J^op -> C be the "
                            + "cofiltered stage diagram. The presented pro-object is constructed "
                            + "as the opposite of the Ind-colimit of the opposite diagram, while "
                            + "cA and cD are constructed by the opposite Ind-Yoneda embedding.")),
                    Paragraph(Text(
                        "A morphism from X to cD is canonically equivalent to the filtered "
                            + "colimit of the stage morphisms X_j -> D. In the reverse direction, "
                            + "a morphism from cA to X is canonically equivalent to the "
                            + "cofiltered limit of the stage morphisms A -> X_j.")),
                    Paragraph(Text(
                        "The Lean construction applies the pinned fully faithful Ind inclusion, "
                            + "its limit-to-inclusion comparison, Yoneda, pointwise colimit "
                            + "preservation, and the library Hom-limit equivalence directly."))),
                DescribeRole.Theorem))));

    private static Formula Hom(Formula category, Formula source, Formula target) =>
        Seq(Operatorname, Grp(F.Id("Hom")), Underscore, Grp(category),
            Open, source, Comma, Sp, target, Close);

    private static Formula IndexedOperator(string name, Formula index, Formula body) =>
        Seq(Operatorname, Grp(F.Id(name)), Underscore, Grp(index), Sp, body);

    private static Formula TheoremFormula()
    {
        Formula category = F.Id("C");
        Formula index = F.Id("J");
        Formula stage = F.Id("j");
        Formula stages = F.Id("X");
        Formula source = F.Id("A");
        Formula target = F.Id("D");
        Formula oppositeIndex = Seq(index, Caret, Grp(F.Id("op")));
        Formula proCategory = Seq(Operatorname, Grp(F.Id("Pro")), Open, category, Close);
        Formula constantSource = Seq(F.Id("c"), Open, source, Close);
        Formula constantTarget = Seq(F.Id("c"), Open, target, Close);
        Formula stageObject = new Formula.Subscript(stages, stage);

        Formula outgoing = Seq(
            Hom(proCategory, stages, constantTarget), Sp, Equiv, Sp,
            IndexedOperator("colim", stage,
                Hom(category, stageObject, target)));
        Formula incoming = Seq(
            Hom(proCategory, constantSource, stages), Sp, Equiv, Sp,
            IndexedOperator("lim", stage,
                Hom(category, source, stageObject)));

        return Disp(Seq(
            Forall, Sp, category, Comma, Sp, index, Comma, Sp,
            stages, Colon, Sp, oppositeIndex, Sp, To, Sp, category, Comma, Sp,
            source, Comma, Sp, target, Colon, Sp, category, Comma, Sp,
            outgoing, Sp, Land, Sp, incoming, Dot));
    }
}
