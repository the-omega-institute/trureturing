using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class ObservationInterventionCounterfactualChainDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Causal/"
            + "ObservationInterventionCounterfactualChain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counterfactual, interventional, and observational query kernels form a chain, "
            + "and each inclusion can be strict.",
        H("Observation-Intervention-Counterfactual Kernel Chain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interventional-equality-forces-observational-equality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "interventional_eq_implies_observational_eq"),
                H("Interventional equality forces observational equality"),
                StatementSource.FromAuthor(InterventionToObservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported Boolean model has no treatment-assignment mechanism. "
                            + "Its observational law is therefore the outcome margin at the "
                            + "known factual treatment false.")),
                    Paragraph(Text(
                        "This margin is one slice of the full interventional table. Equal "
                            + "interventional tables have equal false-treatment slices, so "
                            + "interventional indistinguishability implies observational "
                            + "indistinguishability."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("observation-kernel-strictness-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "observation_kernel_strictness_witness"),
                H("The observation kernel inclusion can be strict"),
                StatementSource.FromAuthor(ObservationStrictnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One witness model always returns false, while the other copies the "
                            + "treatment. At factual treatment false their observed outcome "
                            + "counts agree.")),
                    Paragraph(Text(
                        "At treatment true the first model still returns false and the second "
                            + "returns true. Their interventional tables differ, proving that "
                            + "the observational kernel can be strictly coarser."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-intervention-counterfactual-kernel-chain"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "observation_intervention_counterfactual_chain"),
                H("The three query kernels form a strictness-capable chain"),
                StatementSource.FromAuthor(ChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The counterfactual-to-interventional inclusion and its strict witness "
                            + "are imported directly from the established Boolean SCM result. "
                            + "The observational inclusion follows by taking a table slice.")),
                    Paragraph(Text(
                        "The imported strict witness separates counterfactual from "
                            + "interventional queries. The constant and treatment-copying "
                            + "models separately witness strictness between intervention and "
                            + "observation."))),
                DescribeRole.Theorem))));

    private static Formula InterventionToObservationFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType), Bound("N", modelType)],
            Implies(
                Equal(
                    Apply(F.Id("Int"), firstModel),
                    Apply(F.Id("Int"), secondModel)),
                Equal(
                    Apply(F.Id("Obs"), firstModel),
                    Apply(F.Id("Obs"), secondModel)))));
    }

    private static Formula ObservationStrictnessFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("M", modelType), Bound("N", modelType)],
            And(
                Equal(
                    Apply(F.Id("Obs"), firstModel),
                    Apply(F.Id("Obs"), secondModel)),
                NotEqual(
                    Apply(F.Id("Int"), firstModel),
                    Apply(F.Id("Int"), secondModel)))));
    }

    private static Formula ChainFormula()
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula cfEquality = Equal(
            Apply(F.Id("CF"), firstModel),
            Apply(F.Id("CF"), secondModel));
        Formula intEquality = Equal(
            Apply(F.Id("Int"), firstModel),
            Apply(F.Id("Int"), secondModel));
        Formula obsEquality = Equal(
            Apply(F.Id("Obs"), firstModel),
            Apply(F.Id("Obs"), secondModel));

        Formula cfToInt = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType), Bound("N", modelType)],
            Implies(cfEquality, intEquality));
        Formula intToObs = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("M", modelType), Bound("N", modelType)],
            Implies(intEquality, obsEquality));
        Formula cfStrictness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("M", modelType), Bound("N", modelType)],
            And(intEquality, NotEqual(
                Apply(F.Id("CF"), firstModel),
                Apply(F.Id("CF"), secondModel))));
        Formula obsStrictness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("M", modelType), Bound("N", modelType)],
            And(obsEquality, NotEqual(
                Apply(F.Id("Int"), firstModel),
                Apply(F.Id("Int"), secondModel))));

        return F.Disp(And(cfToInt, And(intToObs, And(cfStrictness, obsStrictness))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
