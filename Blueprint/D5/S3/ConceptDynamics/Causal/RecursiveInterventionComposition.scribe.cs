using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class RecursiveInterventionCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recursively realized node value makes its additional intervention redundant.",
        H("Recursive Intervention Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recursive-intervention-composition"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/RecursiveInterventionComposition."
                        + "recursive_intervention_composition"),
                H("A realized intervention composes without changing the outcome"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both worlds use the repository's parent-ordered structural model, "
                            + "the same external state, and the same assignment. The second "
                            + "world additionally intervenes at one node.")),
                    Paragraph(Text(
                        "When the first evaluation already realizes the value assigned at that "
                            + "node, the inserted intervention performs the same update. "
                            + "Determinism of all later recursive updates then gives the same "
                            + "value at every queried outcome node."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula x = F.Id("X");
        Formula uType = F.Id("U");
        Formula model = F.Id("model");
        Formula intervention = F.Id("intervention");
        Formula assigned = F.Id("assigned");
        Formula external = F.Id("u");
        Formula baseResult = F.Id("baseResult");
        Formula expandedResult = F.Id("expandedResult");
        Formula realizedNode = F.Id("w");
        Formula outcomeNode = F.Id("y");
        Formula nodes = Apply("Fin", n);
        Formula modelType = Apply("StructuralModel", n, x, uType);
        Formula interventionType = Apply("Finset", nodes);
        Formula assignmentType = Seq(nodes, Sp, To, Sp, x);
        Formula baseEvaluation = Apply(
            "EvaluationWitness", model, intervention, assigned, external,
            Apply("order", model), Apply("initial", model, external), baseResult);
        Formula expandedEvaluation = Apply(
            "EvaluationWitness", model, Apply("insert", realizedNode, intervention),
            assigned, external, Apply("order", model), Apply("initial", model, external),
            expandedResult);
        Formula realized = Equal(
            Seq(baseResult, Open, realizedNode, Close),
            Seq(assigned, Open, realizedNode, Close));
        Formula conclusion = Equal(
            Seq(expandedResult, Open, outcomeNode, Close),
            Seq(baseResult, Open, outcomeNode, Close));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            x, Comma, Sp, uType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            model, Colon, Sp, modelType, Comma, Sp,
            intervention, Colon, Sp, interventionType, Comma, Sp,
            assigned, Colon, Sp, assignmentType, Comma, Sp,
            external, Colon, Sp, uType, Comma, Esc,
            baseResult, Comma, Sp, expandedResult, Colon, Sp, assignmentType, Comma, Sp,
            realizedNode, Comma, Sp, outcomeNode, Colon, Sp, nodes, Comma, Esc,
            baseEvaluation, Sp, Land, Sp, expandedEvaluation, Sp, Land, Sp, realized,
            Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
