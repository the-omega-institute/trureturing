using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class HistorySensitiveOutcomeReductionObstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paths with one outcome and different evaluations obstruct outcome-only representation.",
        H("History-Sensitive Outcome Reduction Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("history-sensitive-evaluation-not-outcome-reducible"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/"
                        + "HistorySensitiveOutcomeReductionObstruction."
                        + "history_sensitive_evaluation_not_outcome_reducible"),
                H("History sensitivity obstructs outcome reduction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The path type, endpoint readout, and normative evaluation are independent "
                            + "source primitives on the canonical concept carrier.")),
                    Paragraph(Text(
                        "History sensitivity is stated publicly by two paths with the same endpoint "
                            + "and different evaluations. Outcome reducibility is stated publicly "
                            + "as an endpoint function through which the evaluation factors.")),
                    Paragraph(Text(
                        "The exact whole-codomain factorization criterion makes every represented "
                            + "evaluation constant on endpoint fibers. Applying it to the two "
                            + "witness paths contradicts their different evaluations.")),
                    Paragraph(Text(
                        "The witness supplies an evaluation value, so the nonempty codomain needed "
                            + "by the exact extension theorem is derived rather than imposed as an "
                            + "additional source restriction.")),
                    Paragraph(Text(
                        "No result function, endpoint, or evaluation is defined from the theorem's "
                            + "nonexistence target."))),
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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula pathType = F.Id("Gamma");
        Formula outcomeType = F.Id("X");
        Formula evaluationType = F.Id("L");
        Formula endpoint = F.Id("e");
        Formula evaluation = F.Id("J");
        Formula first = F.Id("gamma");
        Formula second = F.Id("gammaPrime");
        Formula outcomeEvaluation = Seq(Overline, Grp(evaluation));
        Formula sameOutcome = Seq(
            Apply(endpoint, first), Sp, Eq, Sp, Apply(endpoint, second));
        Formula differentEvaluation = Seq(
            Apply(evaluation, first), Sp, Neq, Sp, Apply(evaluation, second));
        Formula historyWitness = Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, pathType, Comma, Sp,
            sameOutcome, Sp, Land, Sp, differentEvaluation);
        Formula reduction = Seq(
            Exists, Sp, outcomeEvaluation, Colon, Sp,
            Arrow(outcomeType, evaluationType), Comma, Sp,
            evaluation, Sp, Eq, Sp,
            Call("compose", outcomeEvaluation, endpoint));
        Formula types = Seq(
            pathType, Comma, Sp, outcomeType, Comma, Sp, evaluationType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")));
        Formula readouts = Seq(
            endpoint, Colon, Sp, Arrow(pathType, outcomeType), Comma, Sp,
            evaluation, Colon, Sp, Arrow(pathType, evaluationType));

        return Disp(Seq(
            Forall, Sp, types, Comma, RowBreak, Grp(),
            readouts, Comma, RowBreak, Grp(),
            Grp(historyWitness), Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Grp(reduction), Dot));
    }
}
