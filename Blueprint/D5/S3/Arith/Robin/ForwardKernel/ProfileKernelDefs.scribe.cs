using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ProfileKernelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Robin price ratio and the response of a moving profile.",
        H("Moving profile kernel definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("price-ratio"),
                DeclarationHandle.Create(Prefix + "priceRatio"),
                H("Price ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio rho_x(u) is w(x+u)/w(x), where w(t)=(log(t)+1)/(t^2*log(t)^2) is the Robin price derivative weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-response"),
                DeclarationHandle.Create(Prefix + "profileResponse"),
                H("Moving profile response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H=x^theta, the response is sqrt(x)/H^2 times the oriented integral from 0 to H of g(u/H)*(E(x+u)-E(x))*rho_x(u)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-response-eq-profile-response"),
                DeclarationHandle.Create(Prefix + "forwardResponse_eq_profileResponse"),
                H("The complete Chebyshev response as a constant profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original forward response equals the moving profile response with E(x)=psi(x)-x, theta=4/5, and g identically one, as functions on the real line."))),
                DescribeRole.Theorem))));
}
