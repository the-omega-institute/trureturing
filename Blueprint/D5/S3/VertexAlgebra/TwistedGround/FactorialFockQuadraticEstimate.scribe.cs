using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class FactorialFockQuadraticEstimateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An operator-norm and Hilbert-Schmidt bound for all mixed Gaussian degrees in the existing factorial Fock metric.",
        H("Factorial Fock quadratic estimate"),
        Blocks(
            Paragraph(Text("The finite mode type may be empty. The complex matrix A is symmetric, with actual Euclidean operator norm at most q, where 0<=q<1. Set Q_A=(1/2)*sum_ij A_ij X_i X_j and G_n=Q_A^n/n!. The squared norm is the real self-pairing of the existing FactorialFockMetric Hilbert embedding. No Gaussian norm formula, assumed boundedness, Takagi decomposition, finite-degree restriction or summability premise is introduced.")),
            D("mass", "Factorial squared norm", "The mass is the real part of the existing factorial Fock self-pairing."),
            D("quadratic", "Symmetric quadratic creation polynomial", "For any finite complex matrix A, Q_A is one half of the sum of A_ij X_i X_j over both indices."),
            D("gaussianPiece", "Gaussian homogeneous pieces", "The nth piece is Q_A raised to n and divided by n factorial."),
            D("gaussianCoefficient", "Occupation coefficient", "The coefficient at occupation d is selected from G_(degree(d)/2); the homogeneity theorem below handles odd degrees."),
            N("mass_eq_sum", "Exact factorial metric", "The actual squared Fock norm is sum_d weight(d)*|coeff(p,d)|^2. This equality is derived from the existing all-polynomial factorial pairing."),
            N("quadratic_creation_bound", "CCR creation estimate in every degree", "For every polynomial p, sum_i mass((sum_j A_ij X_j)*p) <= HS(A)^2*mass(p)+q^2*sum_j mass(partial_j p). The proof first derives the exact creation/derivative commutator identity, with conjugated coefficients on the derivative vector. The scalar Euclidean matrix norm bound is then applied at each occupation and summed with its factorial weight."),
            N("gradient_mass", "Exact particle-number identity", "For homogeneous p of degree k, sum_i mass(partial_i p)=k*mass(p), using Mathlib Euler identity and the existing creation/pderiv adjoint law."),
            N("gaussianPiece_pderiv", "Exact Gaussian annihilation equation", "Symmetry gives partial_i G_(n+1)=(sum_j A_ij X_j)*G_n. The factor 1/2 and n! are explicitly derived and retained."),
            N("degree_mass_recurrence", "All-degree Gaussian recurrence", "For a_n=mass(G_n), (n+1)*a_(n+1) <= (HS(A)^2/2+q^2*n)*a_n. This is a bound for every particle number, including all mixed and repeated occupations."),
            N("all_degree_partial_bound", "Uniform dimension and particle bound", "Every sum of a_n through N is bounded by exp(HS(A)^2/(2*(1-q^2))). The analytic recurrence theorem supplies the same constant for every N."),
            N("all_degree_summable", "Infinite Gaussian degree sum", "The complete sequence of polynomial Gaussian square masses is summable; the result is not limited to a finite degree."),
            N("gaussianCoefficient_zero", "Vacuum normalization", "The zero occupation has coefficient one, including when the finite mode type is empty."),
            N("gaussianCoefficient_odd", "Odd occupations vanish", "If the total occupation degree is odd, homogeneity forces its Gaussian coefficient to vanish."),
            N("gaussianCoefficient_even", "Even degree selection", "An occupation of total degree 2n has Gaussian coefficient exactly its coefficient in G_n."),
            N("gaussianPiece_coefficient_step", "Mixed coefficient equation with multiplicities", "Coefficient extraction from the annihilation equation gives (d_i+1)*coeff(G_(n+1),d+e_i)=sum_j A_ij*coeff(X_j*G_n,d). This is the exact equation needed for the still-missing labelled Wick comparison, with factorial multiplicities intact."),
            N("finite_occupation_bound", "Arbitrary mixed occupation subsets", "For g_A(d)=coeff(G_(degree(d)/2),d), every finite occupation subset S satisfies sum_(d in S) weight(d)*|g_A(d)|^2 <= exp(HS(A)^2/(2*(1-q^2))). The proof bounds S inside a finite degree rectangle, with a constant independent of that rectangle. Vacuum equals one and odd occupations vanish."),
            N("occupation_summable", "True factorial sum over infinitely many occupations", "For the finite matrix A, the infinite mixed occupation coefficient sequence has summable weight(d)*|g_A(d)|^2. No desired source value is defined to equal g_A."),
            Paragraph(Text("Identifying an actual Corr/Wick source with weight(d)*g_A(d), stabilizing coefficients under finite-mode transport, passing over infinitely many modes, and constructing an actual source representer are separate mathematical obligations. The present results concern the finite-matrix analytic supplier. The determinant norm identity, including the intended -1/2 exponent for A* A, remains open here; no identification with gaussianDet(z) is proved."))),
        []));

    private static DocumentBlock D(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("factorial-fock-quadratic-estimate-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("factorial-fock-quadratic-estimate-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
