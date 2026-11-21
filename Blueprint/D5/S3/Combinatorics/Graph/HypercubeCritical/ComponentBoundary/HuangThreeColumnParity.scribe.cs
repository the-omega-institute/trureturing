using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class HuangThreeColumnParityDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity weights of three cube columns",
        H("Parity weights of three cube columns"),
        Blocks(
            Paragraph(Text("Problem 2 in Section 7 of Hong, Wu and Xia's Graph Sensitivity of Cartesian Products with Matched Bridges asks whether the two-neighbor sensitivity of the nine-cube is 3 or 4. The 18+3 folded case has three minority columns on a common set of empty rows. The binary weight bound applies when each of these columns has exactly four retained neighbors. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("cube-column-parity-weight-definition"),
                DeclarationHandle.Create(Module + ".cubeColumnParityWeight"),
                H("Weight of a selected set of columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any cube dimension, each vertex is a finite set of coordinates. Given a finite row set and three distinct centers indexed by 0, 1 and 2, the support of a column is the set of rows differing from that column's center in exactly one coordinate. The parity weight of a subset of the indices is the size of the symmetric difference of the selected supports, with empty symmetric difference equal to the empty set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cube-column-parity-weight"),
                DeclarationHandle.Create(Module + ".cube_column_parity_weight"),
                H("Every nonempty selection has even weight from four through twelve"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the support of each of the three columns has exactly four rows on the common row set. For every nonempty subset of the three column indices, the parity weight belongs to {4, 6, 8, 10, 12}. Each single column has weight four. Two distinct centers have at most two common neighbors, so the symmetric difference of two supports has even size at least four.")),
                    Paragraph(Text("If every pair of full neighborhoods intersects, translate the first center to the empty set by symmetric difference. The other centers become two-element sets whose symmetric difference has size two. A coordinate they share gives a neighbor of all three centers in the full cube. For each center, the overlaps with the other two neighborhoods therefore cover at most three neighbors. Each retained support supplies a distinct row private to that column, yielding at least three rows in the symmetric difference. If two full neighborhoods are disjoint, each of their retained supports contributes at least two private rows because the third neighborhood can cover at most two of its rows.")),
                    Paragraph(Text("The symmetric difference of two sets has cardinality equal to the sum of their cardinalities minus twice their intersection size. Applying this identity twice shows that the three-column weight is even and at most twelve. Thus the three private rows in the pairwise-intersecting case already force weight at least four. In the folded axial equation this bound constrains any nonzero lowest-order binary syndrome obtained by reducing a normalized integral column combination modulo two."))),
                DescribeRole.Theorem)),
        []));
}
