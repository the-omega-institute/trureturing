using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class StochasticTargetCompletionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Completion/StochasticTargetCompletion."
            + "stochastic_target_completion_is_least";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional-law completion is the least prediction-sufficient conservative refinement.",
        H("Stochastic Target Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stochastic-target-completion-is-least"),
                DeclarationHandle.Create(Declaration),
                H("Conditional-law completion is the least sufficient refinement"),
                StatementSource.FromAuthor(LeastCompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite source state is assigned its complete conditional law in "
                            + "PMF(Y). Completing a concept joins its original readout with "
                            + "that law-valued kernel.")),
                    Paragraph(Text(
                        "The completed concept is prediction-sufficient and still refines the "
                            + "original concept. Thus it preserves the old information while "
                            + "making the full conditional distribution recoverable.")),
                    Paragraph(Text(
                        "Every other concept that both refines the original readout and makes "
                            + "the same kernel recoverable also receives a factor map from the "
                            + "completion. This is the claimed least conservative completion."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Sufficient(Formula concept, Formula kernel) =>
        Call("TargetSufficient", concept, kernel);

    private static Formula RefinesConcept(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula LeastCompletionFormula()
    {
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula futureType = F.Id("Y");
        Formula candidateType = F.Id("D");
        Formula concept = F.Id("concept");
        Formula candidate = F.Id("candidate");
        Formula kernel = F.Id("K");
        Formula laws = Call("PMF", futureType);
        Formula completion = Call("targetClosure", concept, kernel);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, conceptType, Comma, Sp, futureType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, stateType, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            Typed(concept, Arrow(stateType, conceptType)), Comma, Sp,
            Typed(kernel, Arrow(stateType, laws)), Comma, RowBreak, Grp(),
            Sufficient(completion, kernel), Sp, Land, RowBreak, Grp(),
            RefinesConcept(concept, completion), Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(candidateType, TypeUniverse()), Comma, Sp,
            Typed(candidate, Arrow(stateType, candidateType)), Comma, RowBreak, Grp(),
            RefinesConcept(concept, candidate), Sp, Rightarrow, Sp,
            Sufficient(candidate, kernel), Sp, Rightarrow, Sp,
            RefinesConcept(completion, candidate), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
