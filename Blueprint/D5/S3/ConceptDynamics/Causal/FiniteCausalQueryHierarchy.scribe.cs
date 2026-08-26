using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class FiniteCausalQueryHierarchyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Causal/FiniteCausalQueryHierarchy."
            + "finite_causal_query_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One finite Boolean SCM class carries genuine observational, interventional, "
            + "and counterfactual query profiles with both hierarchy links strict.",
        H("Finite Causal Query Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-causal-query-hierarchy"),
            DeclarationHandle.Create(Declaration),
            H("The finite causal query hierarchy is strict"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The common carrier is a two-node recursive Boolean structural model. "
                        + "Its exogenous state has two coordinates, so the same class includes "
                        + "both reverse causal direction and independent outcome noise.")),
                Paragraph(Text(
                    "The interventional profile contains the empty intervention. Its empty "
                        + "component is the passive joint law, while the counterfactual profile "
                        + "retains the response of each exogenous state under every regime.")),
                Paragraph(Text(
                    "The forward and reverse direction models have the same passive law but "
                        + "different intervention laws. The stable and flip coupling models "
                        + "have the same complete single-world profile but different "
                        + "unit-preserving response profiles."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula modelType = F.Id("FiniteBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");

        Formula cfToInt = QuantifiedImplication(
            modelType,
            Equal(Call("CF", firstModel), Call("CF", secondModel)),
            Equal(Call("Int", firstModel), Call("Int", secondModel)));
        Formula intToObs = QuantifiedImplication(
            modelType,
            Equal(Call("Int", firstModel), Call("Int", secondModel)),
            Equal(Call("Obs", firstModel), Call("Obs", secondModel)));

        Formula observationWitness = And(
            Equal(
                Call("Obs", F.Id("observationalForwardModel")),
                Call("Obs", F.Id("observationalReverseModel"))),
            NotEqual(
                Call("Int", F.Id("observationalForwardModel")),
                Call("Int", F.Id("observationalReverseModel"))));
        Formula counterfactualWitness = And(
            Equal(
                Call("Int", F.Id("stableCouplingModel")),
                Call("Int", F.Id("flipCouplingModel"))),
            NotEqual(
                Call("CF", F.Id("stableCouplingModel")),
                Call("CF", F.Id("flipCouplingModel"))));

        return F.Disp(And(cfToInt, And(intToObs,
            And(observationWitness, counterfactualWitness))));
    }

    private static Formula QuantifiedImplication(
        Formula modelType,
        Formula hypothesis,
        Formula conclusion) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("M"),
            modelType,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("N"),
                modelType,
                new Formula.Logic(
                    hypothesis,
                    FormulaLogicOperator.Implies,
                    conclusion)));

    private static Formula Call(string function, params Formula[] arguments) =>
        new Formula.Apply(F.Id(function), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

}
