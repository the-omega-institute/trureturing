using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class AnswerabilityCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorization, fiber constancy, and absence of a defect pair are equivalent criteria "
        + "for answering a question from a concept readout.",
        H("Answerability Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("answerability-factorization-fiber-and-defect-criterion"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/AnswerabilityCriterion."
                    + "answerability_criterion"),
                H("Three equivalent criteria characterize answerability"),
                StatementSource.FromAuthor(AnswerabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state anchor is part of the source model. It supplies an actual "
                            + "question value, which is exactly the inhabitance needed to extend "
                            + "a fiber-constant question from the image of the concept readout to "
                            + "its full answer domain.")),
                    Paragraph(Text(
                        "The defect relation is constructed directly from the two readouts: it "
                            + "contains precisely those state pairs with equal concept values and "
                            + "unequal question values. Thus its emptiness is independently "
                            + "equivalent to constancy on every concept fiber.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Function.factorsThrough_iff is the exact factorization "
                            + "criterion and is applied directly. Repository searches found only "
                            + "an adjacent one-way kernel-refinement theorem, not this complete "
                            + "three-clause equivalence."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Factorization(
        Formula concept, Formula question, Formula conceptAnswer, Formula questionAnswer)
    {
        Formula answer = F.Id("answer");
        return Seq(
            Exists, Sp, answer, Colon, Sp, conceptAnswer, Sp, To, Sp, questionAnswer,
            Comma, Sp, question, Sp, Eq, Sp, answer, Sp, Circ, Sp, concept);
    }

    private static Formula FiberConstancy(
        Formula state, Formula concept, Formula question)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(concept, x), Sp, Eq, Sp, Apply(concept, y), Sp, Rightarrow, Sp,
            Apply(question, x), Sp, Eq, Sp, Apply(question, y));
    }

    private static Formula Defect(Formula state, Formula concept, Formula question)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Seq(
            OpenBrace, Open, x, Comma, Sp, y, Close, Colon, Sp,
            state, Sp, Times, Sp, state, Sp, Mid, Sp,
            Apply(concept, x), Sp, Eq, Sp, Apply(concept, y), Sp, Land, Sp,
            Apply(question, x), Sp, Neq, Sp, Apply(question, y), CloseBrace);
    }

    private static Formula AnswerabilityFormula()
    {
        Formula state = F.Id("X");
        Formula conceptAnswer = F.Id("B");
        Formula questionAnswer = F.Id("A");
        Formula anchor = F.Id("anchor");
        Formula concept = F.Id("concept");
        Formula question = F.Id("question");
        Formula factorization = Factorization(
            concept, question, conceptAnswer, questionAnswer);
        Formula fiberConstancy = FiberConstancy(state, concept, question);
        Formula defectEmpty = Seq(
            Defect(state, concept, question), Sp, Eq, Sp, Emptyset);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, conceptAnswer, Comma, Sp, questionAnswer,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            anchor, Colon, Sp, state, Comma, Sp,
            concept, Colon, Sp, state, Sp, To, Sp, conceptAnswer, Comma, Sp,
            question, Colon, Sp, state, Sp, To, Sp, questionAnswer, Comma, RowBreak,
            Open, factorization, Sp, Leftrightarrow, Sp, fiberConstancy, Close,
            Sp, Land, RowBreak,
            Open, fiberConstancy, Sp, Leftrightarrow, Sp, defectEmpty, Close,
            Sp, Land, RowBreak,
            Open, defectEmpty, Sp, Leftrightarrow, Sp, factorization, Close, Dot));
    }
}
