using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Termination;

internal sealed class GuardedRankingTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A well-founded rank forbids infinite guard-preserving transition chains.",
        H("Guarded Ranking Termination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guarded-ranking-terminates"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Termination/GuardedRankingTermination."
                        + "guarded_ranking_terminates"),
                H("A decreasing rank terminates guarded transitions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source transition is constructed from two independent primitives: "
                            + "`guard x` enables execution at the current state, and `step x y` "
                            + "relates that state to its successor.")),
                    Paragraph(Text(
                        "Every enabled step strictly lowers `rank` according to the named "
                            + "well-founded relation `less`. The conclusion quantifies over every "
                            + "candidate trajectory and finds an adjacent pair where the guarded "
                            + "transition fails.")),
                    Paragraph(Text(
                        "The proof directly applies the pinned library theorem "
                            + "`WellFounded.not_rel_apply_succ` to the ranked trajectory. "
                            + "No transition or rank object is defined from the conclusion.")),
                    Paragraph(Text(
                        "A natural-number countdown checks that the hypotheses admit a nonempty "
                            + "guarded transition relation and instantiates the public theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula rankType = F.Id("W");
        Formula state = F.Id("x");
        Formula next = F.Id("y");
        Formula index = F.Id("n");
        Formula guard = F.Id("guard");
        Formula step = F.Id("step");
        Formula rank = F.Id("rank");
        Formula less = F.Id("less");
        Formula trajectory = F.Id("trajectory");
        Formula prop = F.Id("Prop");
        Formula nat = F.Id("Nat");
        Formula type = F.Id("Type");
        Formula trajectoryAt = Apply(trajectory, index);
        Formula nextIndex = Seq(index, Sp, Plus, Sp, D(1));
        Formula trajectoryNext = Apply(trajectory, nextIndex);
        Formula enabledStep = Seq(
            Apply(guard, trajectoryAt), Sp, Land, Sp,
            Apply(step, trajectoryAt, trajectoryNext));
        Formula decrease = Seq(
            Forall, Sp, state, Comma, Sp, next, Colon, Sp, stateType, Comma, Sp,
            Open, Apply(guard, state), Sp, Land, Sp, Apply(step, state, next), Close,
            Sp, Rightarrow, Sp,
            Apply(less, Apply(rank, next), Apply(rank, state)));
        Formula premises = Seq(
            Apply(
                Seq(Operatorname, Grp(F.Id("IsWellFounded"))),
                rankType, less),
            Sp, Land, Sp, Open, decrease, Close);
        Formula conclusion = Seq(
            Forall, Sp, trajectory, Colon, Sp, Arrow(nat, stateType), Comma, Sp,
            Exists, Sp, index, Colon, Sp, nat, Comma, Sp,
            Neg, Sp, Open, enabledStep, Close);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, rankType, Colon, Sp, type, Comma, Sp,
            guard, Colon, Sp, Arrow(stateType, prop), Comma, Sp,
            step, Colon, Sp, Arrow(stateType, Arrow(stateType, prop)), Comma, RowBreak, Grp(),
            rank, Colon, Sp, Arrow(stateType, rankType), Comma, Sp,
            less, Colon, Sp, Arrow(rankType, Arrow(rankType, prop)), Comma, RowBreak, Grp(),
            Open, premises, Close, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
