using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockBivariateConvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite polynomial convolutions supply the coefficient shifts of native half-Fock products.",
        H("Finite Coefficient Convolutions"),
        Blocks(
            Paragraph(Text("For any commutative ring Ring and arbitrary integer-indexed creation sequences, "
                + "coefficientConvolution sums over the finite support of a univariate polynomial. "
                + "bivariateCoefficientConvolution sums over the finite monomial support of an "
                + "MvPolynomial (Fin 2) Ring, multiplying each coefficient by the two creation values "
                + "at first+exponent(0) and second+exponent(1). These are Ring-linear maps. "
                + "No support or convergence assumption on the creation sequences is required.")),
            Describe.Lean(
                DescribeId.Create("half-fock-convolution-monomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_monomial"),
                H("A univariate monomial selects one creation coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural degree and coefficient in Ring, the monomial maps "
                    + "to coefficient * creation(shift+degree). The constant case is consumed by the "
                    + "oscillator constant calculation in OrderedProducts."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-convolution-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.coefficientConvolution_expansion"),
                H("The univariate convolution is its polynomial support sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every polynomial, coefficientConvolution equals the sum of "
                    + "polynomial.coeff(degree) * creation(shift+degree) over polynomial.support. "
                    + "OrderedProducts uses this identity to identify the actual oscillator coefficient."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-bivariate-convolution-monomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_monomial"),
                H("A bivariate monomial selects two creation coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A monomial with exponent : Fin 2 to finite-support N maps to "
                    + "coefficient * (left(first+exponent(0)) * right(second+exponent(1))). "
                    + "ProductKernel specializes this to the two half-creation sequences."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-bivariate-convolution-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_C_mul"),
                H("A constant polynomial factor leaves the convolution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication of the input polynomial by C coefficient multiplies "
                    + "the output by coefficient. ProductKernel consumes this linearity specialization "
                    + "in its creator recurrence; it is an algebraic helper."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-bivariate-convolution-first-shift"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_zero"),
                H("The first variable shifts the first creation index"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural degree, multiplying by X 0 ^ degree changes "
                    + "first to first+degree and leaves second fixed. Polynomial induction proves the "
                    + "identity for arbitrary input polynomials."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-bivariate-convolution-second-shift"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution.bivariateCoefficientConvolution_X_one"),
                H("The second variable shifts the second creation index"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural degree, multiplying by X 1 ^ degree changes "
                    + "second to second+degree and leaves first fixed. Together the two shift laws "
                    + "supply the independent oscillator shifts in ProductKernel."))), DescribeRole.Theorem),
            Paragraph(Text("These repository-derived finite polynomial identities reuse the existing "
                + "Finsupp linear-sum and polynomial coefficient interfaces. Their declarations are "
                + "owned by this module in the LatticeActualProductKernel namespace. Finiteness here "
                + "belongs to each input polynomial; it gives no finite bivariate or endomorphism "
                + "support for an entire field and establishes no analytic convergence or locality by itself.")))));
}
