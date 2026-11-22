using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FoldedIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant incidence under a coordinate projection",
        H("Equivariant incidence under a coordinate projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-equivariant-fibre-incidence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence.equivariant_fibre_incidence"),
                H("Labelled incidence sums transport along an equivariant projection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a finite family of permutations on the source and base commute with a projection. For a source set S, count incoming labels at each point. The total incidence in a fibre is the sum of S-counts over the inverse images of the base pattern under the labelled permutations.")),
                    Paragraph(Text("If the degree is three on T and even off T, each covered point accounts for at least two incidences and a point of T accounts for one extra. The selected count in any fibre is bounded by the total incidence divided by three and has the same parity as that total."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-folded-coordinate-incidence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence.folded_coordinate_incidence"),
                H("Coordinate translations give explicit bounds on the opposite parity counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In Q8, retain k axes. The identity and the lost-axis translations fix each base pattern. The retained translations send it to its k neighbors. Consequently the fibre incidence is (9−k) times the source count at the pattern plus the sum of source counts at its neighbors. Fibre capacity is 2^(8−k).")),
                    Paragraph(Text("This determines an interval for the companion count from a lower bound on the number of covered points. Checking the interval on every projected axis set uses information from the opposite parity before the full support is known."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-folded-degree-balanced-cubic"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence.folded_degree_of_balanced_cubic"),
                H("Balanced cubic supports supply the degree hypotheses after folding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fold opposite parity classes in Q9 by deleting any one axis. Cross-parity adjacency transports to the identity and eight coordinate flips. Cubicity supplies degree three on the folded target class and the Huang exterior equation supplies even degree elsewhere.")),
                    Paragraph(Text("The resulting constraints apply to the separated 72+186 branch of Hong, Wu and Xia's Problem 2. Integer enumeration uses them to exclude small folded neighborhoods. The published question asks whether 258 vertices of Q9 can induce maximum degree three. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
