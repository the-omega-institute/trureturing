using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9DominantAxisBoundaryDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Owner = Cube + "CoordinateHalves/Q9DominantAxisBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired and empty coordinate fibres in subcubic nine-cube supports",
        H("A rank obstruction on deleting a coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empty-fibre-kernel-from-signed-boundary"),
                DeclarationHandle.Create(Owner + "exists_emptyFibreBoundary_kernel"),
                H("The empty-fibre boundary has a nonzero kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the signed exterior boundary on the retained parity has a nonzero kernel for every real coordinate weighting. Fix a coordinate. Each retained vertex either has its partner along the chosen coordinate in the support or is the sole selected vertex of its fibre. Each opposite-parity exterior vertex belongs either to an empty fibre or to a fibre with a retained singleton.")),
                    Paragraph(Text("Put weight one on the chosen coordinate and multiply the other prescribed weights by a real parameter. On an empty-fibre row every entry is divisible by that parameter. Divide these rows by the parameter before taking the determinant of the column Gram matrix. The determinant vanishes for every positive parameter, so the polynomial determinant also vanishes at zero.")),
                    Paragraph(Text("At zero, a row with a retained singleton partner isolates its singleton column with coefficient one or minus one. Thus the nonzero kernel survives on paired columns and satisfies all empty-fibre equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-actual-components-with-empty-fibre-kernels"),
                DeclarationHandle.Create(Owner + "exists_two_components_with_emptyFibre_kernels"),
                H("Two actual components satisfy every coordinate test"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each retained parity, choose two distinct actual connected components of an induced subcubic 258-point support before choosing the deleted axis or the transverse weights. Each component has the required signed boundary kernel by its universally singular Huang Gram defect.")),
                    Paragraph(Text("The reduced kernel is nonzero for every real transverse weighting, including sparse masks. The rows and columns each record a single fibre, so the condition constrains the projected occupancy when searching for a witness for f₂(Q₉)=3. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-projected-parity-for-transverse-masks"),
                DeclarationHandle.Create(Owner + "exists_two_components_with_fixed_projectedParity_emptyFibre_kernels"),
                H("Each component has a fixed projected parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix the retained parity and the deleted axis. The two possible bits on the deleted axis give two blocks of the paired-column Gram matrix. Polynomial evaluation recovers the real weighted matrices, including every coordinate mask. The product of the two block determinants is the zero polynomial, so one block is singular before the weights are chosen.")),
                    Paragraph(Text("The retained parity is the sum of the deleted bit and the projected parity. This identifies a single projected parity for each component and axis. Any family of sparse masks can therefore be tested against that same projected parity."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "ComponentBoundary/Q9WeightedBoundaryGram")),
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "ComponentBoundary/Q9ComponentSaturation")),
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "Translation/Q9TranslationAperiodicity"))
        ]));
}
