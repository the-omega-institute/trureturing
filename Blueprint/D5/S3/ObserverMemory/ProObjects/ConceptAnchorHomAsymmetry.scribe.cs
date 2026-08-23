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

    private static Formula TheoremFormula()
    {
        Formula category = F.Id("C");
        Formula index = F.Id("J");
        Formula stages = F.Id("X");
        Formula source = F.Id("A");
        Formula target = F.Id("D");
        Formula morphism = F.Id("f");
        Formula oppositeIndex = Seq(index, Caret, Grp(F.Id("op")));
        Formula proCategory = Seq(
            Operatorname, Grp(F.Id("ProObjectCategory")), Open, category, Close);
        Formula presented = Seq(
            Operatorname, Grp(F.Id("presentedObject")), Open, stages, Close);
        Formula constantSource = Seq(
            Operatorname, Grp(F.Id("constantObject")), Open, source, Close);
        Formula constantTarget = Seq(
            Operatorname, Grp(F.Id("constantObject")), Open, target, Close);

        Formula outgoingMap = Seq(
            Open, morphism, Colon, Sp,
            Hom(proCategory, presented, constantTarget), Sp, Mapsto, Sp,
            Operatorname, Grp(F.Id("presentedToConstantEquiv")),
            Open, stages, Comma, Sp, target, Close, Open, morphism, Close, Close);
        Formula incomingMap = Seq(
            Open, morphism, Colon, Sp,
            Hom(proCategory, constantSource, presented), Sp, Mapsto, Sp,
            Operatorname, Grp(F.Id("constantToPresentedEquiv")),
            Open, source, Comma, Sp, stages, Close, Open, morphism, Close, Close);

        return Disp(Seq(
            Forall, Sp, category, Comma, Sp, index, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Category")),
            Open, category, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("SmallCategory")),
            Open, index, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("IsFiltered")),
            Open, index, Close, CloseBracket, Comma, Esc,
            stages, Colon, Sp, oppositeIndex, Sp, To, Sp, category, Comma, Sp,
            source, Comma, Sp, target, Colon, Sp, category, Comma, Sp,
            Operatorname, Grp(F.Id("Bijective")), Open, outgoingMap, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Bijective")), Open, incomingMap, Close, Dot));
    }
}
