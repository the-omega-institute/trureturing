using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class HistorySensitiveOutcomeReductionCompleteDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "History sensitivity obstructs outcome reduction and identifies the kernel defect.",
        H("Complete History-Sensitive Outcome Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("history-sensitive-evaluation-not-outcome-reducible-with-defect"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/"
                        + "HistorySensitiveOutcomeReductionComplete."
                        + "history_sensitive_evaluation_not_outcome_reducible_with_defect"),
                H("History sensitivity obstructs reduction and exposes its defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The path type, endpoint readout, and normative evaluation are independent "
                            + "source primitives on the canonical concept carrier.")),
                    Paragraph(Text(
                        "The first public conjunct is the frozen obstruction theorem: two paths "
                            + "with one endpoint and different evaluations preclude an endpoint-only "
                            + "factorization.")),
                    Paragraph(Text(
                        "The second conjunct identifies the canonical defect relation with the set "
                            + "difference of the endpoint and evaluation equality kernels. The "
                            + "repository's defectRelation primitive is imported rather than "
                            + "redeclared.")),
                    Paragraph(Text(
                        "The source's normative list and its informal interpretation are qualitative "
                            + "remarks without an in-scope predicate; they are outside the displayed "
                            + "formal theorem."))),
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
        Formula endpointKernel = Seq(Ker, Sp, endpoint);
        Formula evaluationKernel = Seq(Ker, Sp, evaluation);
        Formula kernelDifference = Seq(endpointKernel, Sp, Setminus, Sp, evaluationKernel);
        Formula defect = Call("defectRelation", endpoint, evaluation);
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
            Open, Neg, Sp, Grp(reduction), Close, Sp, Land, RowBreak, Grp(),
            defect, Sp, Eq, Sp, kernelDifference, Dot));
    }
}
