using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class UnifiedCausalAlignmentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two frozen Boolean causal separations align faithfully on one cumulative 48-state coproduct.",
        H("Unified Causal Alignment"),
        Blocks(
            Definition("unified-causal-arena", "unifiedArena", "Unified causal arena",
                "The canonical arena is the coproduct of the landed intervention-counterfactual and observation-intervention model carriers."),
            Definition("unified-observation-intervention-signature", "unifiedObservationInterventionSignature", "Unified observation-intervention signature",
                "Two optional branch-local CUT readouts realize observation and intervention on the right coproduct branch."),
            Definition("observation-intervention-unified-realization", "observationInterventionUnifiedRealization", "Observation-intervention realization",
                "The OI readouts are injected faithfully while the opposite branch returns none."),
            Definition("unified-intervention-counterfactual-signature", "unifiedInterventionCounterfactualSignature", "Unified intervention-counterfactual signature",
                "Two optional branch-local CUT readouts realize intervention and counterfactual information on the left branch."),
            Definition("intervention-counterfactual-unified-realization", "interventionCounterfactualUnifiedRealization", "Intervention-counterfactual realization",
                "The IC readouts are injected faithfully while the opposite branch returns none."),
            Definition("unified-observation-readout", "ObsU", "Cumulative observation readout",
                "The coarse readout combines one IC intervention slice with OI observation."),
            Definition("unified-intervention-readout", "IntU", "Cumulative intervention readout",
                "The middle readout combines full IC intervention with paired OI observation and intervention."),
            Definition("unified-counterfactual-readout", "CfU", "Cumulative counterfactual readout",
                "The finest readout uses IC counterfactual tables and the literal OI model identity."),
            Node("observation-factorization", "obsU_factorization", "Observation factors through intervention",
                Factorization(F.Id("ObsU"), F.Id("obsFromInt"), F.Id("IntU")),
                "For each coproduct branch, forgetting intervention data computes exactly the cumulative observation readout."),
            Node("intervention-factorization", "intU_factorization", "Intervention factors through counterfactual",
                Factorization(F.Id("IntU"), F.Id("intFromCf"), F.Id("CfU")),
                "Counterfactual collapse on the IC branch and direct restriction on the OI branch recover intervention data."),
            Node("unified-observation-positive-witness", "unified_observation_positive_witness", "Observation captures an explicit pair",
                ObservationPositiveWitness(),
                "A constant-false OI model is off diagonal from the named X-causes-Y model and has a different observation readout."),
            Node("causal-ie-one", "unified_observation_intervention_strict_refinement", "Intervention strictly refines observation",
                ObservationInterventionStrictRefinement(),
                "The factorization implication is paired with the injected opposite-direction OI witness."),
            Node("causal-ie-two", "unified_intervention_counterfactual_strict_refinement", "Counterfactual strictly refines intervention",
                InterventionCounterfactualStrictRefinement(),
                "The factorization implication is paired with the injected IC no-effect and flip-effect witness."),
            Definition("observation-intervention-law-arena", "observationInterventionLawArena", "Observation-intervention law arena",
                "The frozen OI law is interpreted only on the right branch of the shared arena."),
            Definition("intervention-counterfactual-law-arena", "interventionCounterfactualLawArena", "Intervention-counterfactual law arena",
                "The frozen IC law is interpreted only on the left branch of the shared arena."),
            Node("faithful-observation-intervention-realization", "observation_intervention_unified_realization", "Faithful OI transport",
                FaithfulObservationInterventionRealization(),
                "Forward injection and reverse restriction both use their supplied equality and inequality witnesses."),
            Node("faithful-intervention-counterfactual-realization", "intervention_counterfactual_unified_realization", "Faithful IC transport",
                FaithfulInterventionCounterfactualRealization(),
                "Forward injection and reverse restriction both use their supplied equality and inequality witnesses."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula Equality(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Parenthesize(Formula formula) =>
        Seq(Open, formula, Close);

    private static Formula Qualified(string owner, string member) =>
        Seq(F.Id(owner), Dot, F.Id(member));

    private static Formula ApplyExact(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Inject(string constructor, Formula model) =>
        ApplyExact(Qualified("Sum", constructor), model);

    private static Formula Readout(string name, Formula model) =>
        ApplyExact(F.Id(name), model);

    private static Formula Factorization(Formula result, Formula forget, Formula source) =>
        Equality(result, Seq(forget, Sp, Circ, Sp, source));

    private static Formula ObservationPositiveWitness()
    {
        Formula named = Inject("inr", Qualified("OI", "xCausesYModel"));
        Formula distinct = Inject("inr", F.Id("observationDistinctModel"));
        return Seq(
            Parenthesize(Seq(named, Sp, Colon, Sp, F.Id("UnifiedBoolSCM"))),
            Sp, Neq, Sp, distinct, Sp, Land, Sp,
            NotEqual(Readout("ObsU", named), Readout("ObsU", distinct)));
    }

    private static Formula TypedForallImplication(
        string premiseReadout, string conclusionReadout)
    {
        Formula left = F.Id("M");
        Formula right = F.Id("N");
        return Seq(
            Forall, Sp, left, Sp, right, Colon, Sp, F.Id("UnifiedBoolSCM"), Comma, Sp,
            Equality(Readout(premiseReadout, left), Readout(premiseReadout, right)),
            Sp, Rightarrow, Sp,
            Equality(Readout(conclusionReadout, left), Readout(conclusionReadout, right)));
    }

    private static Formula ObservationInterventionStrictRefinement()
    {
        Formula left = Inject("inr", Qualified("OI", "xCausesYModel"));
        Formula right = Inject("inr", Qualified("OI", "yCausesXModel"));
        return Seq(
            Parenthesize(TypedForallImplication("IntU", "ObsU")), Sp, Land, Sp,
            Parenthesize(Seq(
                Equality(Readout("ObsU", left), Readout("ObsU", right)),
                Sp, Land, Sp,
                NotEqual(Readout("IntU", left), Readout("IntU", right)))));
    }

    private static Formula InterventionCounterfactualStrictRefinement()
    {
        Formula left = Inject("inl", Qualified("IC", "noEffectModel"));
        Formula right = Inject("inl", Qualified("IC", "flipEffectModel"));
        return Seq(
            Parenthesize(TypedForallImplication("CfU", "IntU")), Sp, Land, Sp,
            Parenthesize(Seq(
                Equality(Readout("IntU", left), Readout("IntU", right)),
                Sp, Land, Sp,
                NotEqual(Readout("CfU", left), Readout("CfU", right)))));
    }

    private static Formula ExistentialSeparation(string owner, string coarse, string fine)
    {
        Formula left = F.Id("M");
        Formula right = F.Id("N");
        return Seq(
            Exists, Sp, left, Sp, right, Colon, Sp, Qualified(owner, "Model"), Comma, Sp,
            Equality(
                ApplyExact(Qualified(owner, coarse), left),
                ApplyExact(Qualified(owner, coarse), right)),
            Sp, Land, Sp,
            NotEqual(
                ApplyExact(Qualified(owner, fine), left),
                ApplyExact(Qualified(owner, fine), right)));
    }

    private static Formula FaithfulObservationInterventionRealization() =>
        ApplyExact(
            F.Id("LegacyPrimitiveRealization"),
            F.Id("observationInterventionLawArena"),
            Parenthesize(ExistentialSeparation("OI", "Obs", "Int")),
            F.Id("observationInterventionUnifiedRealization"));

    private static Formula FaithfulInterventionCounterfactualRealization() =>
        ApplyExact(
            F.Id("LegacyPrimitiveRealization"),
            F.Id("interventionCounterfactualLawArena"),
            Parenthesize(ExistentialSeparation("IC", "Int", "CF")),
            F.Id("interventionCounterfactualUnifiedRealization"));
}
