using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class KnowledgeMonotoneRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty refinement of a singleton-answer information state preserves the same "
            + "target value.",
        H("Knowledge Monotonicity Under Nonempty Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("knowledge-monotone-under-nonempty-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/KnowledgeMonotoneRefinement."
                        + "knowledge_monotone_under_nonempty_refinement"),
                H("Knowledge preserves its target value under nonempty refinement"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a target readout T, the answer set of an information state S is "
                            + "constructed directly as the image of S under T. Knowledge at S "
                            + "requires S to be nonempty and this answer set to have cardinality one.")),
                    Paragraph(Text(
                        "The refined state S' is publicly required to be a nonempty subset of S. "
                            + "The conclusion exposes one value y and states that both answer sets "
                            + "are exactly the singleton containing y, so the retained value is "
                            + "literally the same object.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Set.ncard_eq_one extracts y from the source knowledge "
                            + "test, and Set.image_mono transports the subset relation. A witness "
                            + "in S' supplies the reverse singleton inclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula AnswerSet(Formula target, Formula state)
    {
        Formula x = F.Id("x");
        return Seq(
            OpenBrace, Apply(target, x), Sp, Mid, Sp,
            x, InMacro, Sp, state, CloseBrace);
    }

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("Y");
        Formula target = F.Id("T");
        Formula source = F.Id("S");
        Formula refined = Seq(F.Id("S"), Apos);
        Formula value = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula powerset = Seq(Operatorname, Grp(F.Id("Set")), Open, stateType, Close);
        Formula sourceAnswers = AnswerSet(target, source);
        Formula refinedAnswers = AnswerSet(target, refined);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, targetType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            target, Colon, Sp, Arrow(stateType, targetType), Comma, Sp,
            source, Comma, Sp, refined, Colon, Sp, powerset, Comma,
            RowBreak, Grp(),
            refined, Sp, Subseteq, Sp, source, Sp, Land, Sp,
            refined, Sp, Neq, Sp, Emptyset, Sp, Land, Sp,
            Open, source, Sp, Neq, Sp, Emptyset, Sp, Land, Sp,
            Lvert, Sp, sourceAnswers, Sp, Rvert, Sp, Eq, Sp, D(1), Close,
            RowBreak, Grp(),
            Rightarrow, Sp, Exists, Sp, value, Colon, Sp, targetType, Comma, Sp,
            sourceAnswers, Sp, Eq, Sp, OpenBrace, value, CloseBrace, Sp, Land, Sp,
            refinedAnswers, Sp, Eq, Sp, OpenBrace, value, CloseBrace, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
