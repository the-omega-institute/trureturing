using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalCorrectionGaussianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite Gaussian coefficients of the actual neutral lattice correction",
        H("Actual neutral correction and native Gaussian coefficients"),
        Blocks(
            Paragraph(Text("Let D be lattice data of arbitrary finite rank, with its symmetric integral Gram matrix. Its oscillator index is Fin(D.rank) times the natural numbers. The shift parameter z is any complex number. Every source polynomial and every chosen complex linear form has finite support. Rank zero, degenerate Gram matrices, zero forms, dependent forms and an empty finite family are included.")),
            Paragraph(Text("Formal Gaussian/Wick moment calculus is classical: pair contractions determine centered moments, and factorial-weighted coefficients of the formal exponential of a quadratic encode repeated and mixed occupations. The twisted lattice correction background follows the imported LatticeHalfFockCurrentCorrection Scribe and its Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster (1988), bibliographic note. The FLM full text was not inspected, and no exact theorem from it is quoted here. The repository-specific result proved here identifies the actual finite neutral Corr vacuum functional, after arbitrary finite linear substitution, with the existing native Gaussian coefficients through the derived Stein recurrence. No literature novelty is claimed.")),
            D("sourceVacuum", "Actual vacuum readout", "Apply the original neutral Corr(D,0) to the source polynomial. Sum z^s times the oscillator constant coefficient of its shift-s component. This is a finite linear functional; it is not asserted to preserve products."),
            D("covariance", "Evaluated pair covariance", "For indices a and b, the covariance is pairScalar(a.2+1,b.2+1) times D.G(a.1,b.1) times z^((a.2+1)+(b.2+1)). It is complex bilinear, without conjugation."),
            N("covariance_symm", "Symmetry of the actual covariance", "For every lattice data D, complex shift z and oscillator indices a,b, covariance(D,z,a,b) equals covariance(D,z,b,a). The original correction and the full neutral three-leg source-source kernel both use this bilinear symmetry."),
            D("linearForm", "Arbitrary finite linear form", "A finitely supported coefficient family c gives the actual oscillator polynomial sum_a c(a) X_a."),
            D("covarianceMatrix", "Covariance under finite linear substitution", "For a finite family c_i, A_ij is the finite sum of c_i(a)c_j(b) times the evaluated pair covariance. The symmetry of pairScalar and the Gram matrix makes A symmetric. No positivity or nondegeneracy is required."),
            N("sourceVacuum_eq_evaluation", "Finite reconstruction of the actual Corr readout", "The finite shift sum equals evaluation of correctionLift(D,0,p), with its none variable assigned z and every some oscillator variable assigned zero. The proof passes through optionEquivLeft and reconstructs the finite polynomial from its coefficients."),
            N("sourceVacuum_linearForms", "All occupations with their exact factorials", "For every occupation d on the finite family, sourceVacuum(product_i v_i^(d_i)) equals weight(d) times gaussianCoefficient(A,d). Here weight(d) is the product of the occupation factorials, and gaussianCoefficient is the coefficient of Q_A^(degree(d)/2)/(degree(d)/2)!, with Q_A one half of sum_ij A_ij X_i X_j. The Gaussian expression is the existing native polynomial coefficient, rather than a definition of the source functional."),
            Paragraph(Text("Actual insertion and its source partial derivative identity yield the Stein recurrence. Finite derivation reconstruction and the substitution chain rule retain all repeated and mixed occurrences. The native recurrence is supplied by NativeGaussianMoment.nativeMoment_step, which is also consumed by ElementaryGaussianContraction. It follows from gaussianPiece_coefficient_step. Multiplying it by the factorial weight uses weight(r+e_i)=(r_i+1)weight(r) and weight(r)=r_j weight(r-e_j) when r_j is positive. Zero multiplicities contribute zero. Both sides are one at the empty occupation and vanish at odd total degree; strong induction compares predecessors of degree two less. Recurrence multiplicities belong to r after extracting the first occurrence.")),
            Paragraph(Text("This is a finite algebraic identity for arbitrary complex z. It assumes no Wick identity, summability, Hilbert norm bound, convergence radius, representer, independence or injectivity. It makes no assertion of a full vertex operator algebra, conformal field theory, an entire corrected field, string dynamics, AdS/CFT or a physical realization."))),
        []));

    private static DocumentBlock D(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-correction-gaussian-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-correction-gaussian-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
