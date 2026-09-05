using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class UnifiedCausalCatalogDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unified causal catalogs expose cumulative kernels and layered captures without census dependencies.",
        H("Unified Causal Catalog"),
        Blocks(
            Definition("unified-observation-unit", "unifiedObservationUnit",
                "Observation analysis unit", "A singleton CUT bundle carries exactly the cumulative observation kernel."),
            Definition("unified-intervention-unit", "unifiedInterventionUnit",
                "Intervention analysis unit", "A singleton CUT bundle carries exactly the cumulative intervention kernel."),
            Definition("unified-counterfactual-unit", "unifiedCounterfactualUnit",
                "Counterfactual analysis unit", "A singleton CUT bundle carries exactly the cumulative counterfactual kernel."),
            Definition("unified-cumulative-catalog", "unifiedCumulativeCatalog",
                "Cumulative analysis catalog", "The flat analysis view contains observation, intervention, and counterfactual readouts."),
            Definition("unified-observation-intervention-unit", "unifiedObservationInterventionUnit",
                "Unified OI theorem unit", "The frozen observation-intervention theorem is transported to the shared arena."),
            Definition("unified-intervention-counterfactual-unit", "unifiedInterventionCounterfactualUnit",
                "Unified IC theorem unit", "The frozen intervention-counterfactual theorem is transported to the shared arena."),
            Definition("unified-frozen-transition-catalog", "unifiedFrozenTransitionCatalog",
                "Frozen transition catalog", "The canonical theorem catalog contains exactly the two faithful frozen occurrences."),
            Node("causal-ie-three", "unified_frozen_transition_catalog_irredundant",
                "The frozen transition catalog is irredundant",
                Call("CatalogIrredundant", F.Id("unifiedFrozenTransitionCatalog")),
                "The two named branch-local witnesses each separate one occurrence while remaining invisible to the other."),
            Definition("unified-off-diagonal-pairs", "unifiedOffDiagonalPairs",
                "Unified off-diagonal pairs", "All ordered pairs of distinct states form the 2,256-pair denominator."),
            Definition("cumulative-observation-escapes", "E_obs",
                "Observation escape set", "These off-diagonal pairs have equal cumulative observation readouts."),
            Definition("cumulative-intervention-escapes", "E_int",
                "Intervention escape set", "These off-diagonal pairs have equal cumulative intervention readouts."),
            Definition("cumulative-counterfactual-escapes", "E_cf",
                "Counterfactual escape set", "These off-diagonal pairs have equal cumulative counterfactual readouts."),
            Definition("observation-layer-capture", "L_obs",
                "Observation layer", "The first layer captures pairs already separated by observation."),
            Definition("intervention-layer-capture", "L_int",
                "Intervention layer", "The middle layer captures observation collisions separated by intervention."),
            Definition("counterfactual-layer-capture", "L_cf",
                "Counterfactual layer", "The final layer captures intervention collisions separated by counterfactual data."),
            Definition("captured-by-counterfactual", "capturedByCounterfactual",
                "Counterfactual capture set", "This is the complement of the finest escape kernel inside the denominator."),
            Node("unified-layered-increments-pairwise-disjoint",
                "unified_layered_increments_pairwise_disjoint",
                "Layered increments are pairwise disjoint", PairwiseDisjoint(),
                "Nested factorization prevents any ordered pair from first appearing in two layers."),
            Node("unified-layered-increments-partition",
                "unified_layered_increments_partition",
                "Layered increments partition counterfactual capture", Partition(),
                "Every pair outside the counterfactual kernel appears in exactly one cumulative layer."))));

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

    private static Formula Layer(string name) =>
        Seq(F.Id("L"), Underscore, Grp(F.Id(name)));

    private static Formula PairwiseDisjoint() => Seq(
        Call("Disjoint", Layer("obs"), Layer("int")), Sp, Land, Sp,
        Call("Disjoint", Layer("obs"), Layer("cf")), Sp, Land, Sp,
        Call("Disjoint", Layer("int"), Layer("cf")));

    private static Formula Partition() => Seq(
        Call("union", Call("union", Layer("obs"), Layer("int")), Layer("cf")),
        Sp, Eq, Sp, F.Id("capturedByCounterfactual"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
