using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class FiniteGaussianSewingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite polynomial external rows and absolute convergence of native Gaussian coefficient contractions.",
        H("Finite Gaussian coefficient sewing"),
        Blocks(
            Paragraph(Text("The finite external and shared mode types may be empty. All coefficients are complex bilinear Gaussian coefficients, with no conjugation. The shared occupation weight is the product of coordinate factorials. External coefficients retain their ordinary coefficient normalization; no external factorial is inserted.")),
            Paragraph(Text("This is classical Gaussian/Bargmann-Fock calculus. The actual Gaussian coefficient is extracted from quadratic(K)^(degree/2)/(degree/2)!, using the existing native polynomial definitions. A fixed external row is represented as a finite polynomial times the shared Gaussian. The proof uses the actual Gaussian annihilation equation and induction in external occupation degree. Its base is the existing principal-block polynomial projection. At every positive step the external multiplicity d_i+1 is divided out, external lowerings reduce degree, and a shared lowering is the original creation shift. The resulting polynomial is finite at every fixed external occupation, independently of the size of the external and mixed matrix blocks.")),
            D("polynomialGaussian", "Actual finite polynomial insertion", "A polynomial monomial with coefficient c and occupation alpha contributes c times created(alpha,gaussianCoefficient(A)). This is the ordinary coefficient convolution of that monomial with the actual Gaussian. The map is linear in the polynomial."),
            D("row", "Actual block coefficient row", "At shared occupation n the row with external occupation d is gaussianCoefficient(K,d.sumElim(n))."),
            N("row_polynomial", "Finite polynomial bridge for arbitrary external blocks", "For every symmetric matrix K on X plus H and every external occupation d, a finite shared polynomial p has polynomialGaussian(K_HH,p)=row(K,d). No norm hypothesis occurs in this algebraic identity. Repeated coordinates and empty types remain included."),
            N("polynomial_pair_norm_summable", "Absolute convergence with polynomial insertions", "For symmetric strict Euclidean contractions A and B and arbitrary finite shared polynomials p and q, the norms of weight(n) polynomialGaussian(A,p,n) polynomialGaussian(B,q,n) form a summable sequence. The original created_square_summable theorem is reused. Finite sums preserve the weighted square estimate, and the scalar square inequality yields the exact factorial contraction bound."),
            N("row_pair_norm_summable", "Actual external row contraction converges absolutely", "For symmetric K on X plus H and L on Y plus H, the actual row contraction is absolutely convergent when only K_HH and L_HH are strict Euclidean contractions. The external and mixed blocks are arbitrary. The two finite polynomial witnesses are obtained from row_polynomial, rather than assumed as certificates."),
            Paragraph(Text("Absolute convergence and a finite polynomial row representation do not by themselves identify the contraction with the effective Gaussian kernel. Ordered inverse covariance, finite Wick evaluation with the native trace-log vacuum normalization, and the resulting full coefficient sewing equality remain separate obligations. Full corrected fields, arbitrary Gram transport, countable sewing, conformal field theory, fusion, anomalies, string theory and AdS/CFT are not established here."))),
        []));

    private static DocumentBlock D(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("finite-gaussian-sewing-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("finite-gaussian-sewing-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
