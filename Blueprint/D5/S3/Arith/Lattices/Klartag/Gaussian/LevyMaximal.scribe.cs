using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class LevyMaximalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("Levy Maximal"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate levy maximal to the stochastic ellipsoid construction.")),
            Node("claim-1", "measure_le_two_mul_of_reflection", "measure le two mul of reflection",
                "The reflection step. If R preserves P, fixes E, and pulls F back to G, and F ∪ G covers E, then P E ≤ 2 · P (E ∩ F). This is the entire content of the reflection principle, with no probability theory in it.", DescribeRole.Theorem),
            Node("claim-2", "measure_le_two_mul_of_reflection_family", "measure le two mul of reflection family",
                "First-passage decomposition plus reflection. E k is {τ = k}, a disjoint family; R k is the reflection attached to time k; target absorbs every E k ∩ F k. Then the hitting event has measure at most 2 · P target. Both hlevy (here) and hsym (Padding.lean) are instances of this one lemma.", DescribeRole.Theorem),
            Node("claim-3", "flipCoords", "flip Coords",
                "Flip the sign of the coordinates satisfying p.", DescribeRole.Definition),
            Node("claim-4", "measurePreserving_flipCoords", "measure Preserving flip Coords",
                "A product of symmetric laws is invariant under flipping any set of coordinates.", DescribeRole.Theorem),
            Node("claim-5", "walkSum", "walk Sum",
                "walkSum k ω = ∑_{i < k} ω i, the partial sums of the coordinate increments.", DescribeRole.Definition),
            Node("claim-7", "walkSum_total", "walk Sum total",
                "walkSum N is the total sum.", DescribeRole.Theorem),
            Node("claim-8", "flipTail", "flip Tail",
                "The reflection attached to time k: flip every increment of index ≥ k.", DescribeRole.Definition),
            Node("claim-9", "walkSum_flipTail_le", "walk Sum flip Tail le",
                "flipTail k does not move the partial sums up to time k.", DescribeRole.Theorem),
            Node("claim-10", "walkSum_flipTail_total", "walk Sum flip Tail total",
                "flipTail k reflects the increment from k to N.", DescribeRole.Theorem),
            Node("claim-11", "tail_flipTail", "tail flip Tail",
                "The reflected tail increment is the negative of the original.", DescribeRole.Theorem),
            Node("claim-12", "firstHit", "first Hit",
                "{τ = k}: the walk first reaches r at time k.", DescribeRole.Definition),
            Node("claim-15", "biUnion_firstIdx", "bi Union first Idx",
                "First-passage decomposition, for an arbitrary family of predicates: the events \"p first holds at time k\", k ≤ N, partition {∃ k ≤ N, p k x}. Used for both hlevy (here) and hsym (Padding.lean).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
