using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class CounterfactualKernelStrictlyFinerDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counterfactual equality determines interventional equality for deterministic "
            + "Boolean models, but interventional equality does not determine the "
            + "counterfactual table.",
        H("Counterfactual Kernel Is Strictly Finer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interventional-table-is-counterfactual-collapse"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "intervention_eq_collapse_counterfactual"),
                H("The interventional table is the counterfactual collapse"),
                StatementSource.FromAuthor(InterventionCollapseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The counterfactual table retains the exogenous unit, the factual "
                            + "treatment, and the alternate treatment. Collapsing it sums over "
                            + "the two exogenous units for each imposed treatment and outcome.")),
                    Paragraph(Text(
                        "For tables produced by a deterministic Boolean causal model, the "
                            + "factual-treatment coordinate does not affect this aggregate. "
                            + "The resulting counts are exactly the model's interventional "
                            + "table, so the interventional readout factors through the "
                            + "counterfactual readout."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("counterfactual-equality-forces-interventional-equality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "counterfactual_eq_implies_interventional_eq"),
                H("Counterfactual equality forces interventional equality"),
                StatementSource.FromAuthor(CounterfactualImplicationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two deterministic Boolean causal models with the same counterfactual "
                            + "table have the same image under the collapse map. Since that "
                            + "image is each model's interventional table, their interventional "
                            + "readouts must agree.")),
                    Paragraph(Text(
                        "Thus counterfactual indistinguishability is stronger than "
                            + "interventional indistinguishability: every equality in the "
                            + "counterfactual kernel descends to one in the interventional "
                            + "kernel."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("counterfactual-kernel-is-strictly-finer"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "counterfactual_kernel_strictly_finer"),
                H("The counterfactual kernel is strictly finer"),
                StatementSource.FromAuthor(StrictlyFinerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Counterfactual equality always implies interventional equality by "
                            + "the collapse factorization. This establishes inclusion of the "
                            + "counterfactual kernel in the interventional kernel.")),
                    Paragraph(Text(
                        "The strictness witness consists of two deterministic Boolean models "
                            + "whose outcome counts agree under every intervention while their "
                            + "unit-level counterfactual tables differ. Hence the converse "
                            + "kernel inclusion fails."))),
                DescribeRole.Theorem))));

    private static Formula InterventionCollapseFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula model = F.Id("M");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType)],
            Equal(
                Call("Int", model),
                Call("collapse", Call("CF", model)))));
    }

    private static Formula CounterfactualImplicationFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType), Bound("N", modelType)],
            Implies(
                Equal(
                    Call("CF", firstModel),
                    Call("CF", secondModel)),
                Equal(
                    Call("Int", firstModel),
                    Call("Int", secondModel)))));
    }

    private static Formula StrictlyFinerFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula counterfactualEquality = Equal(
            Call("CF", firstModel),
            Call("CF", secondModel));
        Formula interventionalEquality = Equal(
            Call("Int", firstModel),
            Call("Int", secondModel));

        return F.Disp(And(
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("M", modelType), Bound("N", modelType)],
                Implies(counterfactualEquality, interventionalEquality)),
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("M", modelType), Bound("N", modelType)],
                And(
                    interventionalEquality,
                    NotEqual(
                        Call("CF", firstModel),
                        Call("CF", secondModel))))));
    }

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
