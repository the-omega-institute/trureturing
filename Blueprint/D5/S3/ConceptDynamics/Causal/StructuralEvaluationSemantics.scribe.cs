using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class StructuralEvaluationSemanticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite parent-ordered structural model has a unique post-intervention evaluation trace.",
        H("Structural Evaluation Semantics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intervened-equation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics."
                        + "intervenedEquation"),
                H("Intervention replaces exactly the selected structural equations"),
                StatementSource.FromAuthor(IntervenedEquationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Given a finite-node structural model, an intervention set, and an "
                            + "assignment, the equation at node v returns the assigned value "
                            + "when v belongs to the intervention.")),
                    Paragraph(Text(
                        "At every node outside the intervention it evaluates the model's "
                            + "original structural equation on the current state and external "
                            + "state. The displayed equality preserves both branches."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("post-intervention-structural-evaluation-is-unique"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics."
                        + "structure_evaluation_semantics"),
                H("Post-intervention structural evaluation is unique"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The model carries finite nodes, parent sets, structural equations, "
                            + "and an external-state initialization. A supplied topological-order "
                            + "certificate places every parent before its child.")),
                    Paragraph(Text(
                        "An intervention replaces the equations at its selected nodes by the "
                            + "assigned values. The displayed evaluation witness is the recursive "
                            + "state update along the supplied order, and the theorem proves a "
                            + "unique final assignment for every external state."))),
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
        Formula topological = F.Id("topological");
        Formula intervention = F.Id("intervention");
        Formula assigned = F.Id("assigned");
        Formula external = F.Id("u");
        Formula result = F.Id("result");
        Formula nodes = Apply("Fin", n);
        Formula modelType = Apply("StructuralModel", n, x, uType);
        Formula topologicalType = Apply("TopologicalOrder", model);
        Formula interventionType = Apply("Finset", nodes);
        Formula assignmentType = Seq(nodes, Sp, To, Sp, x);
        Formula evaluation = Apply(
            "EvaluationWitness", model, intervention, assigned, external,
            Apply("order", model), Apply("initial", model, external), result);

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            x, Comma, Sp, uType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            model, Colon, Sp, modelType, Comma, Sp,
            topological, Colon, Sp, topologicalType, Comma, Sp,
            intervention, Colon, Sp, interventionType, Comma, Sp,
            assigned, Colon, Sp, assignmentType, Comma, Sp,
            external, Colon, Sp, uType, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, result, Colon, Sp, assignmentType, Comma, Sp,
            evaluation, Dot));
    }

    private static Formula IntervenedEquationFormula()
    {
        Formula n = F.Id("n");
        Formula x = F.Id("X");
        Formula uType = F.Id("U");
        Formula model = F.Id("model");
        Formula intervention = F.Id("intervention");
        Formula assigned = F.Id("assigned");
        Formula node = F.Id("v");
        Formula state = F.Id("state");
        Formula external = F.Id("u");
        Formula nodes = Apply("Fin", n);
        Formula modelType = Apply("StructuralModel", n, x, uType);
        Formula assignmentType = Seq(nodes, Sp, To, Sp, x);
        Formula branch = Apply(
            "if",
            Seq(node, Sp, InMacro, Sp, intervention),
            Apply("assigned", node),
            Apply("equation", model, node, state, external));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            x, Comma, Sp, uType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            model, Colon, Sp, modelType, Comma, Sp,
            intervention, Colon, Sp, Apply("Finset", nodes), Comma, RowBreak, Grp(),
            assigned, Colon, Sp, assignmentType, Comma, Sp,
            node, Colon, Sp, nodes, Comma, Sp,
            state, Colon, Sp, assignmentType, Comma, Sp,
            external, Colon, Sp, uType, Comma, RowBreak, Grp(),
            Apply("intervenedEquation", model, intervention, assigned, node, state, external),
            Sp, Eq, Sp, branch, Dot));
    }
}
