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
                Equality(F.Id("ObsU"), Compose(F.Id("obsFromInt"), F.Id("IntU"))),
                "For each coproduct branch, forgetting intervention data computes exactly the cumulative observation readout."),
            Node("intervention-factorization", "intU_factorization", "Intervention factors through counterfactual",
                Equality(F.Id("IntU"), Compose(F.Id("intFromCf"), F.Id("CfU"))),
                "Counterfactual collapse on the IC branch and direct restriction on the OI branch recover intervention data."),
            Node("unified-observation-positive-witness", "unified_observation_positive_witness", "Observation captures an explicit pair",
                PositiveWitness(),
                "A constant-false OI model is off diagonal from the named X-causes-Y model and has a different observation readout."),
            Node("causal-ie-one", "unified_observation_intervention_strict_refinement", "Intervention strictly refines observation",
                StrictRefinement(F.Id("IntU"), F.Id("ObsU"), F.Id("OI")),
                "The factorization implication is paired with the injected opposite-direction OI witness."),
            Node("causal-ie-two", "unified_intervention_counterfactual_strict_refinement", "Counterfactual strictly refines intervention",
                StrictRefinement(F.Id("CfU"), F.Id("IntU"), F.Id("IC")),
                "The factorization implication is paired with the injected IC no-effect and flip-effect witness."),
            Definition("observation-intervention-law-arena", "observationInterventionLawArena", "Observation-intervention law arena",
                "The frozen OI law is interpreted only on the right branch of the shared arena."),
            Definition("intervention-counterfactual-law-arena", "interventionCounterfactualLawArena", "Intervention-counterfactual law arena",
                "The frozen IC law is interpreted only on the left branch of the shared arena."),
            Node("faithful-observation-intervention-realization", "observation_intervention_unified_realization", "Faithful OI transport",
                Call("LegacyPrimitiveRealization", F.Id("observationInterventionLawArena"), F.Id("OIStatement"), F.Id("observationInterventionUnifiedRealization")),
                "Forward injection and reverse restriction both use their supplied equality and inequality witnesses."),
            Node("faithful-intervention-counterfactual-realization", "intervention_counterfactual_unified_realization", "Faithful IC transport",
                Call("LegacyPrimitiveRealization", F.Id("interventionCounterfactualLawArena"), F.Id("ICStatement"), F.Id("interventionCounterfactualUnifiedRealization")),
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

    private static Formula Compose(Formula left, Formula right) =>
        Call("compose", left, right);

    private static Formula PositiveWitness() => Seq(
        F.Id("inrX"), Sp, Neq, Sp, F.Id("inrDistinct"), Sp, Land, Sp,
        Call("ObsU", F.Id("inrX")), Sp, Neq, Sp, Call("ObsU", F.Id("inrDistinct")));

    private static Formula StrictRefinement(Formula finer, Formula coarser, Formula branch) =>
        Seq(Call("factorsKernel", finer, coarser), Sp, Land, Sp,
            Call("strictWitness", branch, finer, coarser));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
