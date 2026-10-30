using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class AncestralSourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ancestral labels reconstruct the synchronous noisy voter opinions and bound source collisions.",
        H("Ancestral sources of synchronous noisy voter opinions"),
        Blocks(
            Node("Label", "Disjoint opinion labels", DescribeRole.Definition,
                "The left summand labels initial opinions. The right summand labels fresh opinions by a positive natural birth time and a vertex. An initial label can never equal a fresh label."),
            Node("source", "The terminated backward history", DescribeRole.Definition,
                "At time zero the history ends at the initial coordinate. A refresh ends it at the corresponding fresh coordinate. Otherwise it follows the selected actual neighbour to the preceding time layer. This uses the synchronous recursion on the original graph, including infinite locally finite graphs."),
            Node("native_source", "Reconstruction of the actual opinion", DescribeRole.Theorem,
                "For every coordinate assignment, vertex, natural time and sample point, the native opinion equals the opinion coin at its source label. The identity is pathwise and does not require stationarity or a replacement probability space."),
            Node("source_birth_le", "Sources are born no later than their observations", DescribeRole.Theorem,
                "The birth time of every selected source is at most the observation time. Initial sources have birth time zero."),
            Node("survives_iff_old_source", "Survival through a time window", DescribeRole.Theorem,
                "A history starting at time i+k has no refresh in its final k layers exactly when its source was born by time i. A zero-length window always survives."),
            Node("collision_requires_survival", "A collision cannot cross a fresh birth", DescribeRole.Theorem,
                "If the sources at u at times i and i+d coincide, the later history survives all d intervening layers. A refresh in those layers would have birth time greater than i."),
            Node("source_measurable", "Measurability on the original sample space", DescribeRole.Theorem,
                "Measurable input coordinates give measurable source labels at each finite time. The inductive copy step ranges over the actual finite neighbour set, without restricting the vertex set to a finite graph."),
            Node("source_past", "Dependence only on controls and choices", DescribeRole.Theorem,
                "Assignments on possibly different sample spaces have the same source through time N when all refresh controls and neighbour choices through N agree. Initial and fresh opinion values need not agree."),
            Node("possibleSources", "A deterministic finite source set", DescribeRole.Definition,
                "At time zero the possible-source set contains the initial vertex. At the next layer it contains the current fresh label and the union of the preceding possible-source sets over all actual neighbours."),
            Node("source_mem_possible", "Finite-time source support", DescribeRole.Theorem,
                "Every actual source lies in the deterministic finite set of possible sources. This retains initial labels and all possible positive-time refresh labels."),
            Node("survival_probability", "The exact survival probability", DescribeRole.Theorem,
                "For every realization of the full independent-coordinate model, every vertex and all natural i,k, the probability of surviving the final k layers is (1-epsilon)^k. The induction separates the new control and neighbour choice from the earlier coordinate family, and sums over the actual finite neighbour set."),
            Node("collision_probability_le", "The universal source collision bound", DescribeRole.Theorem,
                "The probability that the sources at u at times i and i+d coincide is at most (1-epsilon)^d. This holds also for i=0 and d=0, for every graph and original probability-space realization allowed by the model."),
            Node("sources_independent_coins", "Sources and opinion coins are independent", DescribeRole.Theorem,
                "The entire source field is independent of the entire initial-and-fresh opinion-coin field. Sources depend only on refresh controls and choices; the two coordinate classes are disjoint in the original mutually independent family."),
            Node("coins_independent", "The source-indexed opinion family", DescribeRole.Theorem,
                "Relabelling the original initial and positive-time fresh coordinates preserves mutual independence. Distinct labels correspond to distinct original coordinates."),
            Node("coin_hasLaw", "Fairness of each labelled opinion", DescribeRole.Theorem,
                "Every labelled opinion coin has the fair Bernoulli law inherited from the full model.")), []));

    private static DocumentBlock Node(string declaration, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("voter-source-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
