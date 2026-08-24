using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class SupportGapTargetLawDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Policy/SupportGapTargetLaw.support_gap_target_law";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target branch outside behavior support admits data-equivalent transition models "
            + "with different target laws.",
        H("Support Gap Target Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("support-gap-target-law"),
            DeclarationHandle.Create(Declaration),
            H("Missing behavior support leaves the target law undetermined"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The target branch law gives positive mass to the selected history-action "
                        + "pair, while the behavior policy assigns zero mass to its action at "
                        + "that history.")),
                Paragraph(Text(
                    "The first transition mechanism is constant. The second changes only the "
                        + "unsupported selected branch, so the two mechanisms agree at every "
                        + "branch carrying nonzero behavior mass.")),
                Paragraph(Text(
                    "Pushing the target branch law through the mechanisms yields different "
                        + "outcome laws: the positive selected atom reaches the distinct second "
                        + "outcome only under the second mechanism."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula behavior = F.Id("mu");
        Formula target = F.Id("pi");
        Formula history = F.Id("h");
        Formula action = F.Id("a");
        Formula nextHistory = F.Id("hPrime");
        Formula nextAction = F.Id("aPrime");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula firstOutcome = F.Id("yZero");
        Formula secondOutcome = F.Id("yOne");
        Formula targetMass = Apply("TargetBranchMass", target, history, action);
        Formula behaviorMass = Apply("BehaviorMass", behavior, history, action);
        Formula nextBehaviorMass =
            Apply("BehaviorMass", behavior, nextHistory, nextAction);
        Formula selectedFirst = Apply("Transition", firstModel, history, action);
        Formula selectedSecond = Apply("Transition", secondModel, history, action);
        Formula supportedAgreement = Seq(
            Forall, Sp, nextHistory, Comma, Sp, nextAction, Comma, Sp,
            nextBehaviorMass, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Apply("Transition", firstModel, nextHistory, nextAction), Sp, Eq, Sp,
            Apply("Transition", secondModel, nextHistory, nextAction));
        Formula differentLaws = Seq(
            Apply("TargetOutcomeLaw", target, firstModel), Sp, Neq, Sp,
            Apply("TargetOutcomeLaw", target, secondModel));

        return Disp(Seq(
            targetMass, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            behaviorMass, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            firstOutcome, Sp, Neq, Sp, secondOutcome, Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Sp, firstModel, Comma, Sp, secondModel, Comma,
            RowBreak, Grp(),
            selectedFirst, Sp, Neq, Sp, selectedSecond, Sp, Land,
            RowBreak, Grp(),
            Open, supportedAgreement, Close, Sp, Land,
            RowBreak, Grp(),
            differentLaws, Dot));
    }
}
