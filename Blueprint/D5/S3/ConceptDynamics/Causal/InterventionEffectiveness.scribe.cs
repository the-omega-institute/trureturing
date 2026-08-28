using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class InterventionEffectivenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A structural intervention fixes every selected coordinate at its assigned value.",
        H("Intervention Effectiveness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intervention-effectiveness"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/InterventionEffectiveness."
                        + "intervention_effectiveness"),
                H("Intervened coordinates equal their assigned values"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The model uses the repository's parent-ordered structural semantics. "
                            + "An intervention replaces each selected structural equation by its "
                            + "assigned value, and the evaluation witness records the resulting "
                            + "updates through the complete node order.")),
                    Paragraph(Text(
                        "The selected node is updated exactly once because the model order is "
                            + "complete and duplicate-free. All later updates occur at distinct "
                            + "nodes, so the selected coordinate retains its assigned value in "
                            + "the final result."))),
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
        Formula result = F.Id("result");
        Formula node = F.Id("v");
        Formula nodes = Apply("Fin", n);
        Formula modelType = Apply("StructuralModel", n, x, uType);
        Formula interventionType = Apply("Finset", nodes);
        Formula assignmentType = Seq(nodes, Sp, To, Sp, x);
        Formula evaluation = Apply(
            "EvaluationWitness", model, intervention, assigned, external,
            Apply("order", model), Apply("initial", model, external), result);
        Formula selected = new Formula.Relation(
            node, FormulaRelationOperator.MemberOf, intervention);
        Formula conclusion = Equal(
            Seq(result, Open, node, Close),
            Seq(assigned, Open, node, Close));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            x, Comma, Sp, uType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            model, Colon, Sp, modelType, Comma, Sp,
            intervention, Colon, Sp, interventionType, Comma, Sp,
            assigned, Colon, Sp, assignmentType, Comma, Sp,
            external, Colon, Sp, uType, Comma, Sp,
            result, Colon, Sp, assignmentType, Comma, Sp,
            node, Colon, Sp, nodes, Comma, Esc,
            evaluation, Sp, Land, Sp, selected, Sp, Rightarrow, Sp,
            conclusion, Dot));
    }
}
