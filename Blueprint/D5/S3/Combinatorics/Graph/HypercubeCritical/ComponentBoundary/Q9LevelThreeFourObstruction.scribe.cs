using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9LevelThreeFourObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The level-three and level-four obstruction in Q9",
        H("The level-three and level-four obstruction in Q9"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-missing-triples-obstruction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_missing_triples"),
                H("The missing triples cannot have the prescribed degrees"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let M be a family of thirty distinct triples of nine axes. The degree of a pair is the number of members of M containing it, and the degree of a four-set is the number of members of M it contains. Every pair having odd degree is incompatible with exactly fifty-four four-sets having degree one and no four-set having degree three.")),
                    Paragraph(Text("Count ordered pairs of distinct missing triples meeting in two axes. Their union is a unique four-set and their intersection is a unique pair. In either count, a fibre of degree b contributes b(b−1). Each missing triple extends to six four-sets, so the sum of four-set degrees is 180. The four-set degrees are 0, 1, 2 or 4, and b(b−1) plus the indicator for b = 1 is congruent to b modulo eight. The ordered count is therefore congruent to 180 − 54 = 126, or 6 modulo eight.")),
                    Paragraph(Text("Each missing triple contains three pairs, so the pair degrees sum to 90. Write each odd pair degree as b = 2t + 1. There are 36 pairs, giving a total of 27 for the t values. The identity b(b−1) = 6t + 4t(t−1) makes the ordered count congruent to 162, or 2 modulo eight. The two residues contradict each other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-level-three-and-four-exclusion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_balanced_cubic_support"),
                H("A 108-vertex balanced cubic support cannot occupy only levels three and four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let C be a 108-vertex subset of Q9 whose induced graph is cubic and whose signing satisfies BalancedCriticalSpectrum.IsBalanced. If every vertex of C has Boolean weight three or four, the degree sum across the two layers gives 54 vertices on each side.")),
                    Paragraph(Text("The complement of the selected triples has thirty members among the 84 triples. A pair lies outside C, so exterior Huang cancellation leaves an even number of selected triple extensions among its seven extensions. Its missing degree is odd. A selected four-set has three selected triple neighbors by cubicity, hence missing degree one. An exterior four-set has even selected triple degree and therefore even missing degree. This gives exactly fifty-four four-sets of missing degree one and none of missing degree three.")),
                    Paragraph(Text("This excludes a restricted component shape in Hong, Wu and Xia’s Problem 2. The full 258-vertex question remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
