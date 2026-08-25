using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.History;

internal sealed class AppendOnlyAnswerabilityMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/History/AppendOnlyAnswerabilityMonotonicity."
            + "append_only_answerability_monotone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending records preserves every target answerable from the old history.",
        H("Append-Only Answerability Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("append-only-answerability-monotone"),
            DeclarationHandle.Create(Declaration),
            H("Answerable historical targets persist after appending records"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The old and new logs are concepts on the same history-index carrier. "
                        + "Appending records supplies a projection from the new log values "
                        + "to the old values, and the displayed equation states that the "
                        + "old log is recovered by this projection.")),
                Paragraph(Text(
                    "AnswerableTargets is the canonical set of target concepts whose "
                        + "readouts factor through a history concept. Composing the append "
                        + "projection with each old recovery map gives the required new-log "
                        + "recovery map."))),
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula historyIndex = F.Id("Gamma");
        Formula oldValue = F.Id("Bn");
        Formula newValue = F.Id("Bnext");
        Formula targetValue = F.Id("Y");
        Formula oldLog = F.Id("Ln");
        Formula newLog = F.Id("Lnext");
        Formula projection = F.Id("pn");

        Formula concept(Formula value) => Arrow(historyIndex, value);
        Formula premise = new Formula.Relation(
            oldLog,
            FormulaRelationOperator.Equal,
            Call("compose", projection, newLog));
        Formula conclusion = new Formula.Relation(
            Call("AnswerableTargets", oldLog, targetValue),
            FormulaRelationOperator.SubsetOf,
            Call("AnswerableTargets", newLog, targetValue));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Gamma"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Bn"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Bnext"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Ln"), concept(oldValue)),
                new Formula.BoundVariable(FormulaIdentifier.Create("Lnext"), concept(newValue)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("pn"), Arrow(newValue, oldValue)),
            ],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion)));
    }
}
