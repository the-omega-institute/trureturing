using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;
internal sealed class HsfIdentityCubicCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cubic HSF compatibility at identity in arbitrary finite complex dimension",
        H("Actual endpoint derivatives"),
        Blocks(
            Entry("positive_direction_bound", "Actual positive-direction inequality",
                "For arbitrary finite complex U,H,K with H,U-H,K,I-K PSD, the original CFC sandwich curve has actual third derivative at zero at most its actual second derivative. This consumes both the four-Gram polynomial certificate and the dimension-free CFC derivative supplier."),
            Entry("signed_derivative_transfer", "Actual signed endpoint transfer",
                "For Hermitian K put Hplus=(U+H)/2, Kplus=(I+K)/2, f=curve(U,H,K), g=curve(U,Hplus,Kplus). The actual derivatives satisfy f_second=4 g_second and f_third=12 g_second+8 g_third. The proof identifies both actual CFC curves with their ordered coefficients and proves the transfer identities there, including every noncommuting term."),
            Entry("identity_cubic_compatibility", "Arbitrary-dimensional actual cubic compatibility at identity",
                "For every finite complex matrix size, Hermitian K and PSD endpoints U+H,U-H,I+K,I-K, the actual function f(t)=Re Tr(((I+tK)^(-1/3)(U+tH)(I+tK)^(-1/3))^3) satisfies f_second(0)>=0 and abs(f_third(0))<=5 f_second(0). This includes every positive definite U and Hermitian H, arbitrary noncommuting U,H,K, singular endpoints and zero Hessian. The derivative inequality also holds for PSD U. The denominator base point is identity."),
            Paragraph(Text("The target is He, Saunderson and Fawzi, arXiv:2502.05627v1 Conjecture 6.2, journal DOI 10.1007/s10107-025-02314-0 Conjecture 1. The formal result has alpha=3 and Y=I; no full-general-Y or literature-priority claim is made.")))));
    private static DocumentBlock Entry(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("hsf-identity-compatibility-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
