using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class AbelianTranslationInteractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent translations commute, so an observed order defect excludes that model.",
        H("Interaction Witness from Noncommuting Interventions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("abelian-translation-commutation-and-defect-exclusion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/AbelianTranslationInteraction."
                        + "abelian_translation_commutation_and_defect_exclusion"),
                H("Independent translations commute and defects exclude them"),
                StatementSource.FromAuthor(InteractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be an abelian group, U an intervention-index type, and F_u the "
                            + "intervention at u. The first public clause assumes the interventions "
                            + "are constructed from independently indexed displacements and proves "
                            + "that every pair commutes.")),
                    Paragraph(Text(
                        "For a canonical concept readout T, the second public clause says that a "
                            + "nonempty set of states distinguished by the two intervention orders "
                            + "rules out every independent additive-translation representation.")),
                    Paragraph(Text(
                        "This state-level mechanism is the rigorous interaction witness behind the "
                            + "source's drug-order, legal-measure, course-order, trauma-and-repair, "
                            + "and multiple-cause examples."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula InteractionFormula()
    {
        Formula xType = F.Id("X");
        Formula indexType = F.Id("U");
        Formula targetType = F.Id("Y");
        Formula intervention = F.Id("F");
        Formula displacement = F.Id("a");
        Formula target = F.Id("T");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula x = F.Id("x");
        Formula atU = Subscript(intervention, u);
        Formula atV = Subscript(intervention, v);
        Formula atW = Subscript(intervention, w);
        Formula displacementU = Subscript(displacement, u);
        Formula displacementW = Subscript(displacement, w);
        Formula translatedAtU = Seq(x, Sp, Plus, Sp, displacementU);
        Formula translatedAtW = Seq(x, Sp, Plus, Sp, displacementW);
        Formula forwardOrder = Apply(target, Apply(atU, Apply(atV, x)));
        Formula reverseOrder = Apply(target, Apply(atV, Apply(atU, x)));

        Formula commutationClause = Grp(
            Forall, Sp, displacement, Colon, Sp, Arrow(indexType, xType), Comma, Sp,
            Grp(Forall, Sp, u, Colon, Sp, indexType, Comma, Sp,
                x, Colon, Sp, xType, Comma, Sp,
                Apply(atU, x), Sp, Eq, Sp, translatedAtU), Sp, Rightarrow, RowBreak,
            Forall, Sp, u, Comma, Sp, v, Colon, Sp, indexType, Comma, Sp,
            Seq(atU, Sp, Circ, Sp, atV), Sp, Eq, Sp,
            Seq(atV, Sp, Circ, Sp, atU));

        Formula defectSet = Grp(
            OpenBrace, x, Colon, Sp, xType, Sp, Mid, Sp,
            forwardOrder, Sp, Neq, Sp, reverseOrder, CloseBrace);
        Formula exclusionClause = Grp(
            Forall, Sp, target, Colon, Sp, Arrow(xType, targetType), Comma, Sp,
            u, Comma, Sp, v, Colon, Sp, indexType, Comma, Sp,
            Operatorname, Grp(F.Id("Nonempty")), Open, defectSet, Close,
            Sp, Rightarrow, RowBreak,
            Neg, Sp, Exists, Sp, displacement, Colon, Sp, Arrow(indexType, xType), Comma, Sp,
            Forall, Sp, w, Colon, Sp, indexType, Comma, Sp,
            x, Colon, Sp, xType, Comma, Sp,
            Apply(atW, x), Sp, Eq, Sp, translatedAtW);

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, indexType, Comma, Sp,
            targetType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("AddCommGroup")), Open,
            xType, Close, CloseBracket, Comma, Sp,
            intervention, Colon, Sp, Arrow(indexType, Arrow(xType, xType)), Comma, Esc,
            commutationClause, Sp, Land, Sp, exclusionClause, Dot));
    }
}
