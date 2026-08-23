using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class AgendaPowerDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Aggregation/AgendaPower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Changing only the order of sequential pairwise comparisons can make any candidate "
            + "win the fixed three-voter majority cycle.",
        H("Agenda Power in a Majority Cycle"),
        Blocks(Describe.Lean(
            DescribeId.Create("every-candidate-wins-under-a-suitable-valid-agenda"),
            DeclarationHandle.Create(DeclarationPrefix + "agenda_power"),
            H("Every candidate wins under a suitable valid agenda"),
            StatementSource.FromAuthor(AgendaPowerFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The preference profile and pairwise-majority rule are inherited unchanged "
                        + "from the canonical three-voter cycle. An agenda merely chooses which "
                        + "two distinct candidates meet first and which candidate remains for "
                        + "the final comparison.")),
                Paragraph(Text(
                    "The orders 0-then-1 with 2 remaining, 1-then-2 with 0 remaining, and "
                        + "2-then-0 with 1 remaining yield 2, 0, and 1 respectively. Thus every "
                        + "candidate is attainable, while two valid orders demonstrably return "
                        + "different winners under the same rule."))),
            DescribeRole.Theorem))));

    private static Formula AgendaPowerFormula()
    {
        Formula candidate = Call("Fin", Num(3));
        Formula agenda = F.Id("Agenda");
        Formula desired = F.Id("w");
        Formula firstAgenda = F.Id("g");
        Formula secondAgenda = F.Id("h");
        Formula valid(Formula value) => Call("ValidAgenda", value);
        Formula winner(Formula value) =>
            Call("sequentialWinner", F.Id("majorityPrefers"), value);
        Formula attainable = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("w"),
            candidate,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("g"),
                agenda,
                new Formula.Logic(
                    valid(firstAgenda),
                    FormulaLogicOperator.And,
                    Equal(winner(firstAgenda), desired))));
        Formula changedOutcome = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("g"), agenda),
                new Formula.BoundVariable(FormulaIdentifier.Create("h"), agenda),
            ],
            new Formula.Logic(
                valid(firstAgenda),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    valid(secondAgenda),
                    FormulaLogicOperator.And,
                    new Formula.Logic(
                        new Formula.Not(Equal(firstAgenda, secondAgenda)),
                        FormulaLogicOperator.And,
                        new Formula.Not(Equal(
                            winner(firstAgenda),
                            winner(secondAgenda)))))));

        return Disp(new Formula.Logic(
            attainable,
            FormulaLogicOperator.And,
            changedOutcome));
    }
}
