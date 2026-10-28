using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfIdentityCubicDerivativesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite dimensional CFC power derivatives at the identity.",
        H("Affine Hermitian power derivatives"),
        Blocks(
            Entry("hasDerivAt_cfc", "Differentiation on a fixed spectrum",
                "For a fixed Hermitian matrix K of arbitrary finite size, the derivative "
                + "of cfc(f(t),K) is cfc(g,K) whenever the scalar derivatives of f(t) at "
                + "each eigenvalue of K equal g there. The proof uses the fixed spectral "
                + "unitary and a finite dimensional continuous linear map.",
                DescribeRole.Theorem),
            Entry("hasDerivAt_affine_rpow", "The actual affine matrix power derivative",
                "For real p,t and Hermitian K, assume 1+t*x>0 for every real spectral "
                + "value x of K. Then the actual CFC function s maps to (I+sK)^p has "
                + "derivative p K (I+tK)^(p-1). Positivity persists in a neighborhood "
                + "because the fixed spectrum is finite. No Taylor premise is used.",
                DescribeRole.Theorem),
            Entry("sandwich_trace_germ", "The original sandwich trace",
                "For arbitrary finite matrices X,H and Hermitian K, the real trace "
                + "of ((I+tK)^(-1/3)(X+tH)(I+tK)^(-1/3))^3 agrees near zero with "
                + "the real trace of ((X+tH)(I+tK)^(-2/3))^3. Powers are actual CFC "
                + "powers. The proof uses scalar powers on the fixed positive spectrum "
                + "and cyclicity of trace, without commuting X,H with K.",
                DescribeRole.Theorem),
            Entry("cubic_trace_derivatives", "Differentiating a cubic trace",
                "If B has nearby actual first and second matrix derivatives B1,B2, "
                + "and B2 has derivative B3 at zero, cyclicity gives the exact second "
                + "and third derivatives of Re Tr(B^3). The second is "
                + "Re Tr(3 B2 B^2+6 B1^2 B), and the third is "
                + "Re Tr(3 B3 B^2+9 B2 B1 B+9 B2 B B1+6 B1^3), all at zero.",
                DescribeRole.Theorem),
            Entry("affine_power_cubic_derivatives", "Actual derivatives of the reduced trace",
                "For arbitrary finite matrices X,H, Hermitian K and any real p, put "
                + "L=H+pXK, M=2pHK+p(p-1)XK^2 and "
                + "N=3p(p-1)HK^2+p(p-1)(p-2)XK^3. The actual reduced trace "
                + "Re Tr(((X+tH)(I+tK)^p)^3) has second derivative "
                + "Re Tr(3M X^2+6L^2 X) and third derivative "
                + "Re Tr(3N X^2+9MLX+9MXL+6L^3) at zero. "
                + "The nearby derivatives are proved from the actual CFC curve.",
                DescribeRole.Theorem),
            Entry("identity_cubic_trace_derivatives", "The original ordered coefficients",
                "For arbitrary finite X,H and Hermitian K, the actual CFC sandwich "
                + "trace with exponent -1/3 has second derivative twice coefficient2 "
                + "and third derivative six times coefficient3 at zero. The coefficients "
                + "are exactly the original ordered trace words of HsfQubitMixedCubic, "
                + "not a renamed jet expression or a Taylor assumption.",
                DescribeRole.Theorem),
            Entry("qubit_cubic_compatibility", "The physical qubit estimate at identity",
                "Let X=diag(a,b) with a,b>0, and let H,K be arbitrary complex Hermitian "
                + "two by two matrices. Assume X+H,X-H,I+K,I-K are PSD. Then for the "
                + "actual CFC function phi(t)=Re Tr(((I+tK)^(-1/3)(X+tH)"
                + "(I+tK)^(-1/3))^3), phi''(0)>=0 and |phi'''(0)|<=5 phi''(0). "
                + "The PSD endpoints may be singular, and no trace or phase constraint "
                + "is imposed on H or K. This is the alpha=3, Y=I, diagonal-X qubit "
                + "restriction, not the arbitrary-denominator or arbitrary-dimension result.",
                DescribeRole.Theorem),
            Entry("qubit_posdef_cubic_compatibility", "Every positive definite qubit numerator",
                "For every positive definite complex Hermitian two by two X, and "
                + "Hermitian H,K satisfying X+H,X-H,I+K,I-K PSD, the same actual "
                + "CFC sandwich trace satisfies phi''(0)>=0 and "
                + "|phi'''(0)|<=5 phi''(0). Unitary diagonalization preserves the "
                + "original ordered trace coefficients and transports all four PSD "
                + "endpoints. The actual derivative bridge is applied to the original "
                + "X,H,K. Repeated eigenvalues and singular endpoints are included. "
                + "The denominator base point remains Y=I and the dimension is two.",
                DescribeRole.Theorem),
            Paragraph(Text("Commuting denominator application. Let X,Y be positive definite, H,K Hermitian, X±H and Y±K PSD, and assume YK=KY. Put Xhat=Y^(-1/3) X Y^(-1/3), Hhat=Y^(-1/3) H Y^(-1/3), Khat=Y^(-1/2) K Y^(-1/2)=Y^(-1)K. Congruence transfers the four endpoints. Commuting functional calculus gives (Y+tK)^(-1/3)=Y^(-1/3)(I+tKhat)^(-1/3) near zero. Thus the original alpha-three sandwich path equals HsfIdentityCubicCompatibility.curve(Xhat,Hhat,Khat), and its identity_cubic_compatibility bound applies. X and H need not commute with Y or K. This is a mathematical application exposition; the displayed commuting CFC factorization and congruence transport are not additional Lean declarations in this module. General noncommuting Y,K remains OPEN: matching a first jet does not identify the actual second and third jets.")),
            Paragraph(Text("The motivating compatibility question is due to "
                + "He, Saunderson and Fawzi: arXiv:2502.05627v1, Conjecture 6.2; "
                + "published DOI 10.1007/s10107-025-02314-0, Conjecture 1. "
                + "No literature-priority claim is made.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-identity-derivatives-"
                + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
