using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class NoGuaranteedRemedyOutsideWinningRegionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/NoGuaranteedRemedyOutsideWinningRegion."
            + "no_guaranteed_remedy_outside_winning_region";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Outside every finite winning stage, no bounded strategy guarantees a remedy.",
        H("No Guaranteed Remedy Outside the Winning Region"),
        Blocks(Describe.Lean(
            DescribeId.Create("no-guaranteed-remedy-outside-winning-region"),
            DeclarationHandle.Create(Declaration),
            H("Outside the winning region there is no guaranteed remedy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The control system, goal set, actual state, finite winning stages, and "
                        + "bounded reach strategies are the canonical control-family objects.")),
                Paragraph(Text(
                    "If the actual state belongs to no finite winning stage, the finite-horizon "
                        + "reachability equivalence excludes every bounded strategy that "
                        + "guarantees reaching the goal.")),
                Paragraph(Text(
                    "The second public clause quantifies an exhibited counterfactual state in "
                        + "the same goal. Its existence does not produce a strategy from the "
                        + "actual state."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
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
        Formula stateCarrier = F.Id("X");
        Formula system = F.Id("S");
        Formula goal = F.Id("G");
        Formula state = F.Id("x");
        Formula counterfactual = F.Id("xPrime");
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula winning = Call("winningRegion", system, goal, horizon);
        Formula strategy = Call(
            "BoundedReachStrategy", system, goal, horizon, state);
        Formula outside = Seq(
            Neg, Sp, Exists, Sp, horizon, Sp, InMacro, Sp, naturals, Comma, Sp,
            state, Sp, InMacro, Sp, winning);
        Formula noRemedy = Seq(
            Neg, Sp, Exists, Sp, horizon, Sp, InMacro, Sp, naturals, Comma, Sp,
            strategy);
        Formula counterfactualClause = Seq(
            Forall, Sp, counterfactual, Colon, Sp, stateCarrier, Comma, Sp,
            counterfactual, Sp, InMacro, Sp, goal, Sp, Rightarrow, Sp,
            noRemedy);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateCarrier, Colon, Sp, type, Comma, RowBreak, Grp(),
            system, Colon, Sp, Call("ControlSystem", stateCarrier), Comma, Sp,
            goal, Colon, Sp, Call("Set", stateCarrier), Comma, Sp,
            state, Colon, Sp, stateCarrier, Comma, RowBreak, Grp(),
            outside, Sp, Rightarrow, RowBreak, Grp(),
            Open, noRemedy, Close, Sp, Land, RowBreak, Grp(),
            Open, counterfactualClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
