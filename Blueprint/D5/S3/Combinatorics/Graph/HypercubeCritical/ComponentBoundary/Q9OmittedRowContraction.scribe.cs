using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9OmittedRowContractionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OmittedRowContraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted pair equations and all residual linear rows reduce to one variable per connected component.",
        H("Exact contraction of weighted two-contact rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-component-row-coefficient"),
                DeclarationHandle.Create(Module + ".compressedRows"),
                H("The coefficient of a component in a residual row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V be a finite set of columns, R any set of row indices, K a field, and G a simple graph on V. For reference weights p and a row matrix B over K, the coefficient of a connected component C in row r is the sum of B(r,v) p(v) over the columns v in C."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pair-and-residual-rows-iff"),
                DeclarationHandle.Create(Module + ".pair_and_residual_rows_iff"),
                H("The full and contracted systems have the same solutions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume p(v) is nonzero at every column. A column vector x satisfies p(u)x(v) = p(v)x(u) on every edge and has zero sum in every row of B if and only if there is a unique component vector z with x(v) = p(v) z([v]), zero sum in every compressed row, and the following equivalence. All coordinates of x are nonzero exactly when all coordinates of z are nonzero. Here [v] denotes the component containing v.")),
                    Paragraph(Text("Cancellation on an edge gives equality of x(v)/p(v) at its endpoints. Induction along a walk propagates equality, so these quotients define z on the connected components. Every component has a vertex, so the quotient there determines z uniquely. Substitution recovers each edge equation, and partitioning each residual row sum by component proves that its compressed sum equals its original sum."))),
                DescribeRole.Theorem),
            Paragraph(Text("In the weighted omitted-row matrix for the nine-cube, a mixed two-contact row has signed coefficients a at u and b at v. Suppose both coefficients are nonzero and a common nowhere-zero reference vector satisfies a p(u) + b p(v) = 0. Multiplying the raw row sum a x(u) + b x(v) by p(u) gives b times the difference p(u)x(v) − p(v)x(u). The raw row vanishes exactly when the two terms of that difference agree. Use the contacted pair as an edge. Repeated rows on the same pair impose the same edge equation when they share the reference vector. All other omitted rows enter B with their original signed coordinate weights. Thus every higher-contact row is retained through its component sums.")),
            Paragraph(Text("The order-126 grid-projection archive records 141 observed supports and seven persistent weighted omitted-row rank exceptions. This contraction supplies the linear reduction used in the archive. Hong, Wu and Xia's Problem 2 asks whether f₂(Q₉) = 3 and remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
            []));
}
