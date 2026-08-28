using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class ThreeLayerCausalObservationLanguageDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Causal/ThreeLayerCausalObservationLanguage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observational, interventional, and counterfactual profiles induce a strict "
            + "kernel hierarchy under exactly the two stated family-membership premises.",
        H("Three-Layer Causal Observation Language"),
        Blocks(
            Definition(
                "observational-profile",
                "observationalProfile",
                "Observational profile",
                "The passive profile is the joint visible-variable law with no mechanism "
                    + "replacement."),
            Definition(
                "interventional-profile",
                "interventionalProfile",
                "Interventional profile",
                "The interventional profile restricts the single-world law family to the "
                    + "declared set of allowed interventions."),
            Definition(
                "counterfactual-profile",
                "counterfactualProfile",
                "Counterfactual profile",
                "The counterfactual profile restricts query laws to the declared query set."),
            Definition(
                "three-layer-equivalence",
                "threeLayerEquivalence",
                "Three-layer equivalence",
                "The three equivalence relations are the Setoid kernels of the three "
                    + "profile maps."),
            Theorem(
                "causal-hierarchy-direction",
                "causal_hierarchy_direction",
                "The causal profile kernels form the stated chain",
                HierarchyFormula(),
                "The empty-intervention law recovers observation, while each selected "
                    + "single-world counterfactual law recovers its intervention law."),
            Theorem(
                "intervention-kernel-not-below-counterfactual",
                "intervention_kernel_not_below_counterfactual",
                "The intervention kernel is not below the counterfactual kernel",
                InterventionStrictnessFormula(),
                "The stable and flip Boolean SCMs agree on every single-world regime law "
                    + "but disagree on the unit-preserving counterfactual response."),
            Theorem(
                "observation-kernel-not-below-intervention",
                "observation_kernel_not_below_intervention",
                "The observation kernel is not below the intervention kernel",
                ObservationStrictnessFormula(),
                "The forward and reverse Boolean SCMs have one passive joint law but are "
                    + "separated by a perfect intervention on X."),
            Theorem(
                "empty-intervention-is-necessary",
                "empty_intervention_is_necessary",
                "The empty-intervention premise is necessary",
                EmptyPremiseFormula(),
                "A concrete Boolean profile omits its null action. The selected intervention "
                    + "profile is constant although observation still separates the models."),
            Theorem(
                "single-world-query-is-necessary",
                "single_world_query_is_necessary",
                "The single-world-query premise is necessary",
                SingleWorldPremiseFormula(),
                "An empty counterfactual query family has a universal kernel while the sole "
                    + "intervention query retains the Boolean model value."),
            Theorem(
                "singleton-query-families-collapse",
                "singleton_query_families_collapse",
                "Singleton query families collapse the hierarchy",
                SingletonCollapseFormula(),
                "When the only intervention is empty and the only counterfactual query is its "
                    + "single-world result, the two law bridges identify all three kernels."),
            Theorem(
                "unit-law-space-collapses",
                "unit_law_space_collapses",
                "A one-point law space collapses the hierarchy",
                UnitCollapseFormula(),
                "Every profile into Unit is constant, independently of the model, action, "
                    + "or query carriers."))));

    private static DocumentBlock.Describe Definition(
        string id,
        string declaration,
        string heading,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Theorem);

    private static Formula HierarchyFormula()
    {
        Formula cfKernel = Kernel(F.Id("cfQ"));
        Formula intKernel = Kernel(F.Id("intA"));
        Formula obsKernel = Kernel(F.Id("Obs"));
        Formula premises = And(F.Id("emptyAllowed"), F.Id("singleWorldQueried"));
        Formula chain = And(Le(cfKernel, intKernel), Le(intKernel, obsKernel));
        return F.Disp(Implies(premises, chain));
    }

    private static Formula InterventionStrictnessFormula() =>
        F.Disp(Not(Le(Kernel(F.Id("Int")), Kernel(F.Id("CF")))));

    private static Formula ObservationStrictnessFormula() =>
        F.Disp(Not(Le(Kernel(F.Id("Obs")), Kernel(F.Id("Int")))));

    private static Formula EmptyPremiseFormula() => F.Disp(And(
        Not(Member(F.Id("empty"), F.Id("A"))),
        Not(Le(Kernel(F.Id("intA")), Kernel(F.Id("Obs"))))));

    private static Formula SingleWorldPremiseFormula() => F.Disp(And(
        Equal(F.Id("Q"), F.Id("emptySet")),
        Not(Le(Kernel(F.Id("cfQ")), Kernel(F.Id("intA"))))));

    private static Formula SingletonCollapseFormula() => F.Disp(And(
        Equal(Kernel(F.Id("cfQ")), Kernel(F.Id("intA"))),
        Equal(Kernel(F.Id("intA")), Kernel(F.Id("Obs")))));

    private static Formula UnitCollapseFormula() => F.Disp(And(
        Equal(Kernel(F.Id("cfUnit")), Kernel(F.Id("intUnit"))),
        Equal(Kernel(F.Id("intUnit")), Kernel(F.Id("obsUnit")))));

    private static Formula Kernel(Formula profile) =>
        new Formula.Apply(F.Id("ker"), [profile]);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Not(Formula proposition) => new Formula.Not(proposition);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
