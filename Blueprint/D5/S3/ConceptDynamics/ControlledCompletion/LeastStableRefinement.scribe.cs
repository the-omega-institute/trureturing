using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ControlledCompletion;

internal sealed class LeastStableRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Action-word completion is the least interface stable under every generating action.",
        H("Least Stable Controlled Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-completion-is-least-stable-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement."
                        + "controlled_completion_is_least_stable_refinement"),
                H("Controlled completion is the least stable refinement"),
                StatementSource.FromAuthor(LeastStableRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an interface q and a family of generating actions, the canonical "
                            + "dynamic closure records q after every finite action word.")),
                    Paragraph(Text(
                        "Its empty-word coordinate recovers q, prefixing a generator preserves "
                            + "all closure fibers, and every other action-stable refinement "
                            + "determines every finite-word coordinate. These are the three "
                            + "public clauses of the least-interface claim.")),
                    Paragraph(Text(
                        "The theorem imports the existing dynamic-closure construction and applies "
                            + "its three frozen component theorems directly. Repository and pinned-"
                            + "Mathlib searches found no theorem already bundling the clauses."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        F.Seq(F.Operatorname, F.Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula DynamicClosure(Formula concept, Formula intervene) =>
        Call("DynClosure", concept, intervene);

    private static Formula Closed(Formula concept, Formula intervene) =>
        Call("InterventionClosed", concept, intervene);

    private static Formula LeastStableRefinementFormula()
    {
        Formula state = F.Id("X");
        Formula value = F.Id("A");
        Formula intervention = F.Id("U");
        Formula candidateValue = F.Id("B");
        Formula concept = F.Id("q");
        Formula intervene = F.Id("intervene");
        Formula candidate = F.Id("candidate");
        Formula closure = DynamicClosure(concept, intervene);

        Formula candidateMinimality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("B", TypeUniverse()),
                Bound("candidate", Arrow(state, candidateValue)),
            ],
            Implies(
                And(
                    Refines(concept, candidate),
                    Closed(candidate, intervene)),
                Refines(closure, candidate)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("q", Arrow(state, value)),
                Bound("intervene", Arrow(intervention, Arrow(state, state))),
            ],
            And(
                Refines(concept, closure),
                And(
                    Closed(closure, intervene),
                    candidateMinimality))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
