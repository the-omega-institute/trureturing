using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundReplicationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A hub with one pendant leaf connects replicated graph copies at a prescribed vertex set.",
        H("One-leaf replication of partial dominating families"),
        Blocks(
            Node("partial-dominating", "Partial domination", "PartialDominating",
                "For a finite simple graph H on V, a finite subset U of V, and S⊆V, "
                    + "PartialDominating(H,U,S) means that every x outside U either belongs to S "
                    + "or has an H-neighbor in S.", DescribeRole.Definition),
            Node("partial-sets", "The partial dominating family", "partialSets",
                "The family partialSets(H,U) contains exactly the finite vertex subsets partially "
                    + "dominating outside U. Every dominating set of H belongs to this family. "
                    + "The full vertex set belongs to both families, including when V is empty.",
                DescribeRole.Definition),
            Node("replicated-graph", "The one-leaf hub graph", "replicated",
                "For any nonnegative integer r, the vertex type is (Fin(r)×V)⊕Fin(2). "
                    + "Two copied vertices (i,x),(j,y) are adjacent exactly when i=j and H has edge xy. "
                    + "The hub z is the right vertex 0, its pendant w is the right vertex 1, "
                    + "and z is joined to (i,u) exactly for u∈U. The right vertices are adjacent. "
                    + "There are rh+2 vertices, where h is the order of H.", DescribeRole.Definition),
            Node("replicated-no-isolates", "Absence of isolated vertices", "replicated_no_isolates",
                "For every finite V, graph H with decidable adjacency, subset U, and r≥0, "
                    + "if every vertex of H has positive degree, every vertex of the replicated "
                    + "graph has positive degree. Copied vertices retain an H-neighbor; z and w "
                    + "are neighbors of each other.", DescribeRole.Theorem),
            Node("hub-decomposition", "Domination with the hub selected", "dominating_with_hub_iff",
                "For every finite V, graph H, subset U, r≥0, and subset S of the replicated vertices "
                    + "containing z, S dominates the replicated graph if and only if each slice "
                    + "{x:(i,x)∈S} partially dominates H outside U. The pendant can be freely selected.",
                DescribeRole.Theorem),
            Node("omitted-decomposition", "Domination with the hub omitted", "dominating_without_hub_iff",
                "For every finite V, graph H, subset U, r≥0, and subset S of the replicated vertices "
                    + "omitting z, S dominates the replicated graph if and only if w∈S and each slice "
                    + "{x:(i,x)∈S} dominates H internally.", DescribeRole.Theorem),
            Node("hub-count", "Count with the hub selected", "hubSets_card",
                "For every finite V, graph H, U⊆V and r≥0, write a=|partialSets(H,U)|. "
                    + "The number of dominating sets of the replicated graph containing z equals 2a^r.",
                DescribeRole.Theorem),
            Node("omitted-count", "Count with the hub omitted", "omittedSets_card",
                "For every finite V, graph H, U⊆V and r≥0, write b=|domSets(H)|. "
                    + "The number of dominating sets of the replicated graph omitting z equals b^r.",
                DescribeRole.Theorem),
            Node("hub-size-sum", "Cardinality sum with the hub selected", "hubSets_sum",
                "For every finite V, graph H, U⊆V and r≥0, write a=|partialSets(H,U)| and "
                    + "α=familyAverage(partialSets(H,U)). The sum of |S| over the replicated "
                    + "dominating sets containing z equals 2a^r(3/2+rα). The hub contributes one, "
                    + "the free pendant contributes one half on average, and the r slices contribute rα.",
                DescribeRole.Theorem),
            Node("omitted-size-sum", "Cardinality sum with the hub omitted", "omittedSets_sum",
                "For every finite V, graph H, U⊆V and r≥0, write b=|domSets(H)| and β=avd(H). "
                    + "The sum of |S| over the replicated dominating sets omitting z equals b^r(1+rβ).",
                DescribeRole.Theorem),
            Node("exact-average", "Exact replicated average", "replicated_average",
                "For every finite V, graph H, U⊆V and r≥0, with a=|partialSets(H,U)|, "
                    + "b=|domSets(H)|, α=familyAverage(partialSets(H,U)) and β=avd(H), "
                    + "the average order of the replicated graph equals "
                    + "[2a^r(3/2+rα)+b^r(1+rβ)]/[2a^r+b^r]. All averages and divisions are rational.",
                DescribeRole.Theorem),
            Node("replication-inequality", "The global bound rearranged", "replication_inequality",
                "For every finite V, graph H and U⊆V, suppose every replicated graph has "
                    + "average at most two thirds of its order. Put h=|V| and c=2h/3. "
                    + "For every r≥0, a^r[1+6r(α−c)]≤b^r[1+3r(c−β)].",
                DescribeRole.Theorem),
            Node("relaxed-average-bound", "Bound and equality for the partial family", "relaxed_average_le",
                "For every finite V, graph H and U⊆V, suppose avd(H)≤2|V|/3 and "
                    + "every replicated graph has average at most two thirds of its order. "
                    + "Then familyAverage(partialSets(H,U))≤2|V|/3. If equality holds, "
                    + "partialSets(H,U)=domSets(H). If the first family is larger, the finite "
                    + "quadratic replication estimate gives strict inequality.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
