using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeMatterGhostCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact matter anomaly after shifted finite cancellation",
        H("The exact matter anomaly after shifted finite cancellation"), Blocks(
            Paragraph(Text("Assume only that H is a two-sided inverse of the complex lattice Gram matrix. The original matter Virasoro theorem and original ghost weight-minus-one Ward identity determine the two commutators. The construction remains on the algebraic tensor product and uses no completion or tensor commutant assumption.")),
            Describe.Lean(
                DescribeId.Create("latticematterghostcovariance-paired"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCovariance.paired"),
                H("The shifted original-operator action family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,H and integers r,k, paired D H r k is the tensor map sugawaraMode D H k tensor BcGhostFock.c (r-k). Its statewise support is finite. Translating the finite captures by m maps to m+r supplies the actual noncentral cancellation."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcovariance-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCovariance.covariance"),
                H("Original-operator covariance with the rank anomaly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,H with H G=G H=1 and every integer r, [T,M_r+G_r]=-(rank(D)/12)(r^3-r) C_r. For a simple tensor choose U=U(v), V=U(sugawaraMode r v), d=max(0,-r), J=[r-A,U] and I=[min(-A-d,-r),max(V,U+d)]. I captures x, M_r x and G_r x, contains J and J-r, and contains the central index -r. A finite bijection m maps to m+r converts the matter noncentral coefficient into k-2r; it cancels the ghost coefficient 2r-k. At m=-r the central cubic is the negative of r^3-r. The statement neither constructs the total BRST charge nor proves nilpotence. The cubic ghost supplier, its composition with this matter term and later physical interpretation remain separate obligations."))), DescribeRole.Theorem))));
}
