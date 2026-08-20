using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class PredictionCompletionIdempotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive completion separates completed states and is idempotent.",
        H("Prediction Completion Idempotence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prediction-completion-is-idempotent"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/PredictionCompletionIdempotence."
                        + "prediction_completion_idempotent"),
                H("Prediction completion is idempotent"),
                StatementSource.FromAuthor(IdempotenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary state update and readout, the completed state space is "
                            + "the quotient by equality of complete future readout itineraries. "
                            + "Its update and current readout descend from those source maps.")),
                    Paragraph(Text(
                        "On that completed system, the second-stage relation again compares every "
                            + "future readout. The representative calculation supplied by the "
                            + "cascade theorem and quotient induction show that this relation is "
                            + "exactly equality on all completed states.")),
                    Paragraph(Text(
                        "Specializing the exact repository cascade-completion theorem to the same "
                            + "readout on both stages and the identity forgetful map supplies the "
                            + "displayed equivalence from the second quotient back to the first "
                            + "completed state space.")),
                    Paragraph(Text(
                        "Repository search found the exact cascade_completion and "
                            + "second_stage_relation_projection declarations. Pinned Mathlib "
                            + "supplies Quotient.inductionOn₂' and Quotient.eq; all four hits are "
                            + "applied directly in the Lean theorem."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Hatted(Formula value) => Seq(Widehat, Grp(value));

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula QuotientOf(Formula relation) =>
        Seq(Operatorname, Grp(F.Id("Quotient")), Open, relation, Close);

    private static Formula IdempotenceFormula()
    {
        Formula y = F.Id("Y");
        Formula o = F.Id("O");
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula z = F.Id("z");
        Formula zPrime = F.Id("zPrime");
        Formula completedState = Subscript(F.Id("Z"), q);
        Formula secondRelation = Hatted(Subscript(F.Id("R"), q));

        return Disp(Seq(
            Forall, Sp, y, Comma, Sp, o, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, tau, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            q, Colon, Sp, y, Sp, To, Sp, o, Comma, Esc,
            Open, Forall, Sp, z, Comma, Sp, zPrime, Sp, InMacro, Sp,
            completedState, Comma, Esc,
            Apply2(secondRelation, z, zPrime), Sp, Iff, Sp,
            z, Sp, Eq, Sp, zPrime, Close, Sp, Land, Esc,
            QuotientOf(secondRelation), Sp, Equiv, Sp, completedState, Dot));
    }
}
