using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockBranchClearingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral Gram pairings give exact clearing and reciprocity for both half-contraction branches.",
        H("Integer Gram Branch Clearing"),
        Blocks(
            Paragraph(Text("Write g=bilinear D left right, p=g.toNat, n=(-g).toNat and N=g.natAbs=p+n. "
                + "The inherited halfContraction is the product of the rescaled binomial series of g "
                + "and the binomial series of -g. The cleared polynomial is "
                + "P_g(t)=(1-t)^(2*p)*(1+t)^(2*n). All signed pairings, including g=0, remain in scope; "
                + "no determinant-unit or positivity premise is used in this module.")),
            Describe.Lean(
                DescribeId.Create("half-fock-two-branch-clearing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing"),
                H("The two binomial branches clear with opposite exponents"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication of halfContraction by (1-t)^n*(1+t)^p gives "
                    + "(1-t)^p*(1+t)^n in PowerSeries C. Binomial-series addition, rescaling by -1 "
                    + "and the integer identities n+g=p and p-g=n prove the equality."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-physical-branch-clearing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing"),
                H("The physical factor clears to the explicit polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by (1-t^2)^N gives P_g.toPowerSeries. "
                    + "Factoring 1-t^2 into the two linear factors converts two-branch clearing "
                    + "into this identity, consumed by native_cleared_kernel_expansion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-cleared-polynomial-degree"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_degree"),
                H("The cleared degree is at most twice the absolute pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer gram, clearedPolynomial gram has natDegree "
                    + "at most 2*gram.natAbs. ClearedKernel uses this upper bound to replace its "
                    + "coefficient expansion by the finite range from 0 through 2*N."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-cleared-polynomial-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity"),
                H("Reflection at twice the absolute pairing preserves the polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P_g.reflect(2*N)=P_g. Reflection negates the factor 1-t, "
                    + "preserves 1+t, and the even exponent 2*p removes the sign. The proof uses "
                    + "degree bounds and polynomial reflection, uniformly in the sign of g."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-cleared-coefficient-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity"),
                H("Complementary coefficients agree inside the cleared range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For degree at most 2*N, coefficient 2*N-degree of P_g equals "
                    + "coefficient degree. ClearedKernel consumes this coefficient consequence when "
                    + "reflecting the finite sum and exchanging the two branches."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-physical-clearing-sign"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.physical_clearing_sign"),
                H("The clearing sign is the integral pairing parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer gram, (-1:C)^gram.natAbs=paritySign gram. "
                    + "PhysicalLocality consumes this parity identity to cancel the actual "
                    + "ground-action exchange sign."))), DescribeRole.Theorem),
            Paragraph(Text("These are repository-derived consequences of the existing half-contraction "
                + "definition and polynomial/binomial-series APIs. They supply algebraic clearing and "
                + "reciprocity, without asserting analytic branch convergence, a new literature theorem "
                + "or the charged tensor locality endpoint on their own.")))));
}
