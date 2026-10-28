using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class RpowPencilTaylorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/RpowPencilTaylor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual noncommutative CFC cube roots of positive definite Hermitian pencils.",
        H("CFC cube roots and ordered matrix jets"),
        Blocks(
            Entry("cubicLinear_entry", "The cubic linearization in a fixed eigenbasis",
                "For Hermitian P, the map E to P squared E plus P E P plus E P squared "
                + "acts in the fixed eigenbasis of P by multiplication of entry ij by "
                + "p_i squared plus p_i p_j plus p_j squared. Positive definiteness "
                + "makes every divisor positive, including repeated eigenvalues. "
                + "This constructs an invertible derivative on the full real space "
                + "of complex matrices, without restricting perturbations to commute.",
                DescribeRole.Theorem),
            Entry("contDiffAt_cubeRoot", "Smoothness of the actual CFC cube root",
                "In every finite dimension, if Y is positive definite and K Hermitian, "
                + "the actual function t to CFC.rpow(Y+tK,1/3) is C infinity at zero. "
                + "The polynomial map Q to Q cubed has an invertible derivative at "
                + "P=Y^(1/3). The classical smooth inverse function theorem supplies "
                + "a local inverse. CFC continuity and the exact cube identity identify "
                + "that inverse with the actual positive cube root near zero. No "
                + "derivative or Taylor expansion is assumed, and eigenvectors are "
                + "never differentiated.", DescribeRole.Theorem),
            Entry("cubeRoot_jet_recurrences", "Exact ordered cubic jet recurrences",
                "Let C_j be the actual jth derivative at zero of Q(t)=(Y+tK)^(1/3) "
                + "divided by j factorial, and P=C_0. Then A_P(C_1)=K, "
                + "A_P(C_2)=-(P C_1 C_1+C_1 P C_1+C_1 C_1 P), and A_P(C_3) "
                + "is minus the seven ordered cubic terms with indices summing to "
                + "three and each index less than three. These follow by "
                + "differentiating the actual local identity Q(t)^3=Y+tK. "
                + "The coefficients are not free formal variables.", DescribeRole.Theorem),
            Entry("contDiffAt_twoThirds", "Smoothness of the two-thirds CFC power",
                "For the same arbitrary finite complex Hermitian pencil, "
                + "t to CFC.rpow(Y+tK,2/3) is C infinity at zero. The proof "
                + "identifies it locally with the square of the actual cube root.",
                DescribeRole.Theorem),
            Entry("normalized_twoThirds_jet", "The normalized two-thirds jet bridge",
                "For F(t)=P inverse (Y+tK)^(2/3) P inverse and j from zero through "
                + "three, the actual jth derivative divided by j factorial equals "
                + "P inverse times the sum of C_a C_(j-a), for a from zero to j, "
                + "times P inverse. Multiplication order and factorial normalization "
                + "are preserved. No commuting assumption or desired bound occurs "
                + "among the hypotheses.", DescribeRole.Theorem),
            Entry("cubeRoot_jet_spectral", "The fixed-Y spectral coefficient interface",
                "Use the fixed spectral unitary of Y and put p_i=lambda_i^(1/3), "
                + "T=diag(p_i), D_j=U star C_j U. Then D_0=T, and "
                + "(p_i squared+p_i p_j+p_j squared) times entry ij of D_j "
                + "satisfies the explicit first, second and third ordered recurrences "
                + "with P replaced by T. Every divisor is strictly positive, "
                + "including repeated eigenvalues. This exposes the actual CFC "
                + "coefficients to finite spectral certificates.", DescribeRole.Theorem),
            Paragraph(Text("The proof is a repository formalization of classical finite "
                + "dimensional spectral calculus and the inverse function theorem, "
                + "using Mathlib's ContDiffAt.to_localInverse, CFC.continuousOn_rpow "
                + "and Matrix.IsHermitian spectral theorem. No mathematical novelty "
                + "claim is made. The scope is the exponents 1/3 and, through squaring, "
                + "2/3. This calculus supplier does not prove the balanced spectral "
                + "inequality or the full He–Saunderson–Fawzi conjecture for independent "
                + "X,Y and all alpha greater than two (arXiv:2502.05627v1, Conjecture "
                + "6.2; DOI 10.1007/s10107-025-02314-0, Conjecture 1).")),
            Paragraph(Text("The six typed theorem-registration attempts compile, but "
                + "their source-selection bindings remain unfinished. The linked issue "
                + "is https://github.com/the-omega-institute/trureturing/issues/23103; "
                + "registration acceptance is not claimed.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rpow-pencil-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
