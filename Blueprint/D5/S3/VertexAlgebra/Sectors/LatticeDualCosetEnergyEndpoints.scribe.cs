using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetEnergyEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Bottom Eigenvectors and All Complex Energy Eigenspaces",
        H("Actual Bottom Eigenvectors and All Complex Energy Eigenspaces"),
        Blocks(
            Paragraph(Text("Under positive original real Gram, original two-sided complex inverse H, integral beta and rational mu with G_Q mu=beta, the minimum constructed from finite sublevels is an ACTUAL eigenvalue of the original-omega moduleL_0 in every rank. Its witness is the original carrier basis at a minimizing charge and zero oscillator exponent. Every complex eigenspace is finite dimensional: any nonzero vector forces its complex eigenvalue into cast(h+N), where finite exact energy fibers apply; outside that image the eigenspace is zero. These are algebraic eigenspaces on the actual carrier, without a Hilbert completion or analytic spectral claim.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergyendpoints-bottom-eigenvector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergyEndpoints.bottom_eigenvector"),
                H("bottom eigenvector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed nonnegative attained minimum has a nonzero actual eigenvector in every rank, including rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergyendpoints-all-eigenspaces-finitedimensional"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergyEndpoints.all_eigenspaces_finiteDimensional"),
                H("all eigenspaces finite dimensional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For EVERY complex lambda, the actual original-omega L_0 eigenspace is finite dimensional. Outside cast(h+N) it equals zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergyendpoints-half-shift-actual-bottom-multiplicity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetEnergyEndpoints.half_shift_actual_bottom_multiplicity"),
                H("half shift actual bottom multiplicity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Gram [2] and mu=1/2, every charge weight is at least 1/4, and the ACTUAL original-omega L_0 eigenspace at 1/4 contains two linearly independent vectors from distinct minimizing charges."))),
                DescribeRole.Theorem))));
}
