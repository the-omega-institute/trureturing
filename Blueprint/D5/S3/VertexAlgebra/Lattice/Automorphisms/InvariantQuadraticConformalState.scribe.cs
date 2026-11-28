// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Automorphisms;

internal sealed class InvariantQuadraticConformalStateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState.";
    private static readonly LibraryNoteRef LatticeSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero proper Gram-orthogonal projector commuting with a family of charge isometries gives two linearly independent fixed weight-two states on the actual lattice carrier.",
        H("Fixed Weight-Two States from an Invariant Quadratic Projector"),
        Blocks(
            Paragraph(Text("Let D be even integral LatticeData and G = gramComplex(D). All matrices are complex square matrices indexed by Fin(D.rank). "
                + "For such a matrix A, conformalPolynomial(D,A) is one half of the sum over i and j of A(i,j) times X(i,0)X(j,0). "
                + "The state omega(D,A) places that polynomial in charge zero on the actual finite-support carrier. "
                + "Here transpose is the ordinary matrix transpose for the complex bilinear Gram form.")),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-omega-injective"),
                DeclarationHandle.Create(Prefix + "omega_injective_of_isSymm"),
                H("Quadratic states determine symmetric matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If A and B are symmetric and omega(D,A) = omega(D,B), then A = B. "
                    + "Read the charge-zero component, differentiate in X(i,0) and X(j,0), and take the constant coefficient. "
                    + "Symmetry cancels the factor one half against the two differentiated terms, recovering the matrix entry even when i = j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-polynomial-substitution"),
                DeclarationHandle.Create(Prefix + "conformalPolynomial_substitution"),
                H("Oscillator substitution acts by matrix congruence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let S be a complex algebra endomorphism of the oscillator algebra. Suppose it sends X(i,0) to the sum over k of M(k,i) times X(k,0) for each i. "
                    + "Expanding the quadratic with those substituted variables gives S(conformalPolynomial(D,A)) = conformalPolynomial(D,M A Mᵀ) for arbitrary A and M. "
                    + "The action on higher oscillator variables is unrestricted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-omega-covariance"),
                DeclarationHandle.Create(Prefix + "omega_covariance"),
                H("Covariance under a vacuum-preserving neutral substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the same substitution law for S and M. Let U be a complex-linear endomorphism of the carrier which sends single(0,p) "
                    + "to z times single(0,S(p)) for a fixed complex scalar z and every oscillator polynomial p. Suppose U fixes the vacuum. Applying the law to p = 1 forces z = 1 "
                    + "because the vacuum is nonzero. The polynomial substitution then gives U(omega(D,A)) = omega(D,M A Mᵀ)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-lift-omega"),
                DeclarationHandle.Create(Prefix + "lift_omega"),
                H("Quadratic covariance for the actual charge lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every additive charge equivalence g and every A, the actual lift(D,g) sends omega(D,A) to omega(D,M A Mᵀ), "
                    + "where column i of M is the complex coordinate vector of g applied to the ith unit charge. "
                    + "The lift fixes the vacuum and acts on charge zero by its oscillator substitution with the neutral phase, so the covariance theorem applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-omega-grade-two"),
                DeclarationHandle.Create(Prefix + "omega_mem_grade_two"),
                H("Every neutral quadratic state belongs to grade two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every A, omega(D,A) belongs to grade(D,2). Each summand is supported in charge zero and its two frequency-one "
                    + "oscillator factors contribute one unit of energy each, including when their indices coincide. The grade is closed under sums and complex scaling."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariantquadratic-projector-fixed-weight-two"),
                DeclarationHandle.Create(Prefix + "projector_fixed_weight_two"),
                H("A Gram-orthogonal projector gives two independent fixed states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(
                    Paragraph(Text("Let g be a family of additive charge equivalences indexed by an arbitrary type ι, each preserving the integral bilinear form. "
                        + "Write M(t) for the mixing matrix of g(t). Suppose H is symmetric with H G = 1. Suppose P² = P, P ≠ 0, P ≠ 1, "
                        + "Pᵀ G = G P, and M(t) P = P M(t) for every t. Then omega(D,H) and omega(D,P H) each belong to grade(D,2). "
                        + "Mode one of Y(D,omega(D,H)) acts on each by the complex scalar 2, and lift(D,g(t)) fixes each for all t. "
                        + "The ordered pair ![omega(D,P H), omega(D,H)] is linearly independent over ℂ.")),
                    Paragraph(Text("The square-matrix inverse identity gives G H = 1. To see that P H is symmetric, transpose it to H Pᵀ "
                        + "and rewrite H Pᵀ = H (Pᵀ G) H = H (G P) H = P H. "
                        + "For M = M(t), preservation of the bilinear form gives Mᵀ G M = G, hence Mᵀ G = G M⁻¹. "
                        + "It follows that M H Mᵀ G = 1 and thus M H Mᵀ = H. Commutation with P gives M (P H) Mᵀ = P H, "
                        + "so congruence covariance fixes both states. Grade membership and actualL0_eigen_iff_grade give the eigenvalue 2. "
                        + "The theorem omega_modes identifies Sugawara index zero with mode one of the stated field.")),
                    Paragraph(Text("Symmetric coefficient recovery shows omega(D,H) is nonzero. Its vanishing would give H = 0 and thus 1 = 0, forcing P = 0. "
                        + "If c times omega(D,H) equalled omega(D,P H), moving the scalar into the coefficient matrix and recovering the symmetric coefficients would give c H = P H. "
                        + "Right multiplication by G gives c times 1 = P. Idempotence then gives c P = P, so P ≠ 0 implies c = 1 and hence P = 1, a contradiction."))),
                DescribeRole.Theorem))));
}
