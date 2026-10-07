using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainWalkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Walk"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain walk to the stochastic ellipsoid construction.")),
            Node("claim-1", "pureWalk", "pure Walk",
                "The pure constraint walk: ⟪A₀, q j⟫ plus the martingale increments only, with the one-sided lift dropped.", DescribeRole.Definition),
            Node("claim-2", "constraint_walk_eq", "constraint walk eq",
                "The chain's defining equation. Along one step the constraint value ⟪A_k, q j⟫ moves by the martingale increment ⟪π_k ξ_k, q j⟫ plus the one-sided lift term.", DescribeRole.Theorem),
            Node("claim-3", "lift_term_nonneg", "lift term nonneg",
                "The lift is one-sided. Every summand is non-negative, because a violated constraint has ⟪A', q i⟫ < 1 and the constraint vectors are non-negatively correlated.", DescribeRole.Theorem),
            Node("claim-4", "pureWalk_le", "pure Walk le",
                "The pure walk is below the constraint value. The lift only pushes constraints up.", DescribeRole.Theorem),
            Node("claim-5", "pureWalk_le_one_of_mem", "pure Walk le one of mem",
                "The containment. If j is active at step k, the *pure* walk has already reached the boundary 1 by step k — so the contact event sits inside the padded walk's hitting event.", DescribeRole.Theorem),
            Node("claim-6", "pureWalk_succ_sub", "pure Walk succ sub",
                "The pure walk's increment, read against the increment: the projection is self-adjoint, so the martingale increment is ⟪ξ_k, π_k (q j)⟫ — an inner product against a past-measurable vector, which is what PaddingMap.padInc consumes.", DescribeRole.Theorem),
            Node("claim-7", "constraintM", "constraint M",
                "The chain's scalar martingale for a window point, normalised so that the constraint's boundary is 0. M_0 = ⟪A₀, q j⟫ − 1 is Klartag's initial gap, eq. (61).", DescribeRole.Definition),
            Node("claim-9", "chain_hhit", "chain hhit",
                "The containment, in TailTransport.tail_at_step_μ's shape.", DescribeRole.Theorem),
            Node("claim-11", "contactSet", "contact Set",
                "Abbreviation: the chain's accumulated contact set.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
