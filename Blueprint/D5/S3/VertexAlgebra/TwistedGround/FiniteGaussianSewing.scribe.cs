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
            N("row_pair_norm_summable", "Actual external row contraction converges absolutely", "For symmetric K on X plus H and L on Y plus H, the actual row contraction is absolutely convergent when only K_HH and L_HH are strict Euclidean contractions. The external and mixed blocks are arbitrary. The two finite polynomial witnesses are obtained from row_polynomial, rather than assumed as certificates."),
            D("bilinearMoment", "Actual two-sided Gaussian insertion moment", "H(alpha,beta) is the original bilinear factorial pairing of created(alpha,c_A) with created(beta,c_B). Its recurrence contains the exact coordinate multiplicity beta_i and the lowered occupation beta-e_i, including the zero-coordinate case."),
            N("bilinearMoment_resolvent_step", "Ordered resolvent for actual insertion moments", "For symmetric strict shared contractions A and B, set U_i=H(alpha+e_i,beta), V_i=H(alpha,beta+e_i), u_i=beta_i H(alpha,beta-e_i), and v_i=alpha_i H(alpha-e_i,beta). Actual factorial adjointness and absolute summability give U=B V+u and V=A U+v. The theorem proves U=(I-B A)^(-1)(B v+u). The inverse is ordered, no commutativity is imposed, and no division by the vacuum scalar occurs."),
            D("covariance", "Ordered joint insertion covariance", "The four blocks are (I-BA)^(-1)B, (I-BA)^(-1), (I-AB)^(-1), and (I-AB)^(-1)A. These are ordered matrix products. The lower cross block is the transpose of the upper one under the stated symmetry hypotheses."),
            N("bilinearMoment_wick_recursion", "Symmetric covariance and both true insertion recurrences", "For symmetric strict contractions A and B, the joint covariance is symmetric. Both insertion-coordinate recurrences have the exact lowering multiplicity alpha_j or beta_j. The matrix identity (I-BA)^(-1)B=B(I-AB)^(-1) is proved by multiplying the two actual ordered inverses. Transposition uses symmetry, with no conjugation or commuting assumption. These are recurrences of the native infinite pairing; no Gaussian moment evaluation is assumed."),
            N("row_pair_moments", "Finite expansion of the actual external contraction", "The polynomial witnesses are constructed from the actual Gaussian rows. Their absolutely convergent shared-occupation contraction equals the finite double sum of their ordinary monomial coefficients times the actual two-sided insertion moments H(alpha,beta). The proof exchanges each finite sum with the infinite pairing using the previously established norm summability. No effective-kernel identity, moment evaluation or vacuum normalization is assumed in this bridge."),
            Paragraph(Text("Absolute convergence, a finite polynomial row representation, its finite insertion-moment expansion and the ordered resolvent equation do not by themselves identify the contraction with the effective Gaussian kernel. Identification with native factorial Gaussian moments, finite Wick evaluation with the native trace-log vacuum normalization, and the resulting full coefficient sewing equality remain separate obligations. Full corrected fields, arbitrary Gram transport, countable sewing, conformal field theory, fusion, anomalies, string theory and AdS/CFT are not established here."))),
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
