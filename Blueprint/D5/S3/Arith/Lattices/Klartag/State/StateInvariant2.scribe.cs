using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class StateInvariant2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("State Invariant2"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate state invariant2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "failure_le2", "failure le2",
                "The union-bound cost at N = ⌈16 n⁷ log n⌉ — Discharge.failure_le's successor at the new N (Discharge.failure_le is stated for ChainWiring.numStepsAdopted, which is frozen).", DescribeRole.Theorem),
            Node("claim-2", "norm_liftStep_le", "norm lift Step le",
                "The lift at one step is at most the number of newly broken constraints times the step's own increment. The coefficient bound is ChainWiring.coeff_le — 1 − ⟪A + B, q i⟫ ≤ −⟪B, q i⟫ because A already satisfies the constraint — and then Cauchy–Schwarz.", DescribeRole.Theorem),
            Node("claim-3", "scaled_map_isometry", "scaled map isometry",
                "A linear isometry preserves N(0, c²·Id), not just the standard Gaussian.", DescribeRole.Theorem),
            Node("claim-4", "map_prod_isometry_scaled", "map prod isometry scaled",
                "The frozen rotation at the level of joint laws, for N(0, c²·Id).", DescribeRole.Theorem),
            Node("claim-6", "map_frozen_isometry_scaled", "map frozen isometry scaled",
                "The frozen rotation preserves the law, at scale c.", DescribeRole.Theorem),
            Node("claim-7", "indepFun_frozen_isometry_scaled", "indep Fun frozen isometry scaled",
                "…and it stays independent of the past, at scale c.", DescribeRole.Theorem),
            Node("claim-8", "chain_congr", "chain congr",
                "The chain at step k reads only ξ j for j < k.", DescribeRole.Theorem),
            Node("claim-9", "past", "past",
                "The past of the increments, truncated at k.", DescribeRole.Definition),
            Node("claim-10", "chainU", "chain U",
                "The chain read as a function of the past sequence.", DescribeRole.Definition),
            Node("claim-12", "reflOf", "refl Of",
                "The frozen reflection attached to an active set.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
