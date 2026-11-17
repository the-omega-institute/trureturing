using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HammingSevenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every pair in an actual Huang-balanced cubic 54-vertex support in Q9 has Hamming distance at most seven.",
        H("Hamming diameter seven for balanced cubic 54-vertex supports"),
        Blocks(
            Paragraph(Text(
                "Let C be a finite set of functions Fin 9 to Bool. Adjacency is the actual "
                    + "cube adjacency, meaning that exactly one coordinate differs, restricted "
                    + "to C. Assume that this induced graph is regular of degree three, that "
                    + "C is balanced for the original FALSE-prefix Huang signing, and that "
                    + "C has 54 vertices. Then every x and y in C differ in at most seven "
                    + "coordinates. These are the complete assumptions: connectivity, girth, "
                    + "layer sizes, path injections and forbidden distances are derived or "
                    + "unneeded, rather than supplied as premises.")),
            Paragraph(Text(
                "BalancedCubeGirth.eight_le_egirth supplies extended girth at least eight "
                    + "from the actual balance assumption. Cube parity supplies the actual "
                    + "bipartition. The private second and third layers and their path-counting "
                    + "lemmas are reused from TwentyFourLayerRegularity. Their endpoint "
                    + "uniqueness comes from the actual short-path cycle argument in "
                    + "GirthSliceCounting. At each root the layers of lengths zero, one, two "
                    + "and three have 1, 3, 6 and 12 vertices. Their disjoint union has 22 "
                    + "vertices, each equipped with an actual walk of length at most three.")),
            Paragraph(Text(
                "Every third-layer vertex has exactly one neighbor inside its own ball. "
                    + "Bipartition excludes neighbors in the odd layers; a neighbor equal to "
                    + "the root would place this vertex in the first layer; short-path "
                    + "uniqueness makes its second-layer parent unique. Cubicity therefore "
                    + "leaves exactly two outward neighbors at each of the twelve third-layer "
                    + "vertices, giving 24 actual outward incidences per root. This proof "
                    + "counts those incidences directly, without requiring a separate "
                    + "internal-edge enumeration.")),
            Paragraph(Text(
                "If two roots admitted no walk of length at most seven, their two "
                    + "22-vertex neighborhoods would be disjoint: a common vertex would "
                    + "concatenate two walks into one of length at most six. No edge could "
                    + "join the neighborhoods, since it would give a walk of length at most "
                    + "seven. Thus the union of the two third layers has 24 vertices, each "
                    + "with two neighbors among the remaining 54-44=10 vertices. Each of "
                    + "those ten vertices has degree three. The actual adjacency double "
                    + "count gives 24*2 at most 10*3, a contradiction. In particular the "
                    + "short walks, and hence connectivity, follow without a connectivity "
                    + "hypothesis. Along an actual cube walk, the Hamming triangle inequality "
                    + "and the one-coordinate adjacency equation bound Hamming distance by "
                    + "walk length. This supplies the exact coordinate-filter conclusion.")),
            Paragraph(Text(
                "The Moore neighborhood counting method is classical graph theory; see "
                    + "Noga Alon, Shlomo Hoory and Nathan Linial, The Moore Bound for Irregular "
                    + "Graphs, Graphs and Combinatorics 18 (2002), 53-57, "
                    + "https://doi.org/10.1007/s003730200002, for the broader Moore-bound "
                    + "context. No new general Moore bound or worldwide novelty is claimed. "
                    + "The repository-derived result here is the exact application to the "
                    + "unchanged actual Huang-balanced induced support. The external anchor "
                    + "is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with "
                    + "Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2, "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 .")),
            Paragraph(Text(
                "The geometric conclusion excludes actual support pairs of Hamming "
                    + "distances eight and nine. It therefore supplies the absence of such "
                    + "pairs required by the grade-eight and grade-nine terms of the paper's "
                    + "Clifford expansion; no Clifford-algebra theorem is declared here. "
                    + "The grade-four and grade-five reductions, purity, arbitrary 54-vertex "
                    + "classification, f2(Q9), and the 258-vertex obstruction remain open.")),
            Describe.Lean(
                DescribeId.Create("balanced-cubic-hamming-seven"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/HammingSeven.hamming_distance_le_seven"),
                H("The actual support has pairwise Hamming distance at most seven"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite C in the nine-dimensional Boolean cube, if its "
                        + "actual induced cube graph is regular of degree three, IsBalanced C "
                        + "holds for Huang's fixed signing, and C.card=54, then for every "
                        + "x in C and y in C the cardinality of {i in Fin 9 | x i differs "
                        + "from y i} is at most seven. The proof constructs the short walks "
                        + "by the two-neighborhood capacity contradiction and then bounds "
                        + "the coordinate difference by walk length."))),
                DescribeRole.Theorem))));
}
