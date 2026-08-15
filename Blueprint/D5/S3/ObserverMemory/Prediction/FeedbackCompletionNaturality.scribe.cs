using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FeedbackCompletionNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projected-state feedback preserves a family of semiconjugate updates.",
        H("Feedback Completion Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projected-state-feedback-preserves-semiconjugate-updates"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/FeedbackCompletionNaturality."
                    + "feedback_completion_naturality"),
                H("Projected-state feedback preserves semiconjugate updates"),
                StatementSource.FromAuthor(NaturalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let update and completedUpdate be families of state updates indexed "
                            + "by a common control type, and let projection map the original "
                            + "state into the completed state. Assume projection semiconjugates "
                            + "the two updates for every control value.")),
                    Paragraph(Text(
                        "Choose each control value by applying feedback to the projected "
                            + "current state. Then projection also semiconjugates the resulting "
                            + "closed-loop updates. The control on both sides is identical "
                            + "because it depends only on that projected state.")),
                    Paragraph(Text(
                        "Loogle found Function.Semiconj.comp_eq as an exact library result for "
                            + "turning pointwise semiconjugacy into function equality; the Lean "
                            + "proof imports and applies it. Loogle also returned the pointwise "
                            + "and equivalence forms, while a shaped family query did not "
                            + "elaborate. LeanSearch returned only generic semiconjugacy and flow "
                            + "results. Repository and receipt searches found no equal or "
                            + "stronger closed-loop theorem. A Boolean instance witnesses that "
                            + "the hypotheses are satisfiable."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Apply(Apply(function, first), second);

    private static Formula NaturalityFormula()
    {
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula u = F.Id("u");
        Formula update = F.Id("update");
        Formula completed = F.Id("completedUpdate");
        Formula projection = F.Id("projection");
        Formula feedback = F.Id("feedback");
        Formula closedUpdate = Seq(
            Open, y, Sp, Mapsto, Sp,
            Apply2(update, Apply(feedback, Apply(projection, y)), y), Close);
        Formula completedClosedUpdate = Seq(
            Open, z, Sp, Mapsto, Sp,
            Apply2(completed, Apply(feedback, z), z), Close);

        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("Z"), Comma, Sp, F.Id("U"),
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            update, Colon, Sp,
            new Formula.TypeArrow(F.Id("U"),
                new Formula.TypeArrow(F.Id("Y"), F.Id("Y"))), Comma, Esc,
            completed, Colon, Sp,
            new Formula.TypeArrow(F.Id("U"),
                new Formula.TypeArrow(F.Id("Z"), F.Id("Z"))), Comma, Esc,
            projection, Colon, Sp, new Formula.TypeArrow(F.Id("Y"), F.Id("Z")),
            Comma, Sp, feedback, Colon, Sp,
            new Formula.TypeArrow(F.Id("Z"), F.Id("U")), Comma, Esc,
            Open, Forall, Sp, u, Comma, Sp,
            projection, Sp, Circ, Sp, Apply(update, u), Sp, Eq, Sp,
            Apply(completed, u), Sp, Circ, Sp, projection, Close,
            Sp, Rightarrow, Sp,
            projection, Sp, Circ, Sp, closedUpdate, Sp, Eq, Sp,
            completedClosedUpdate, Sp, Circ, Sp, projection, Dot));
    }
}
