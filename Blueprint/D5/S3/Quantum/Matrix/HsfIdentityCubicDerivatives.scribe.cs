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
            Entry("affine_rpow_derivatives", "Second and third derivatives at identity",
                "For every real p and every finite dimensional Hermitian K, the second "
                + "and third iterated derivatives at zero of the actual CFC function "
                + "t maps to (I+tK)^p are respectively p(p-1)K^2 and "
                + "p(p-1)(p-2)K^3. The proof differentiates actual nearby functions.",
                DescribeRole.Theorem),
            Entry("inverse_two_thirds_derivatives", "The inverse two-thirds jet",
                "The p=-2/3 specialization gives second derivative (10/9)K^2 and "
                + "third derivative -(80/27)K^3. These are suppliers for the HSF "
                + "identity-denominator cubic trace; this declaration alone does not "
                + "identify the trace coefficients or prove the HSF conjecture.",
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
                DescribeRole.Theorem)))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-identity-derivatives-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
