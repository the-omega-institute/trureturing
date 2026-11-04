using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class GaussianLaplaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Mills normalization and complete classification.",
        H("The general-parameter Gaussian Laplace identity"),
        Blocks(
            Proof("gaussian-kernel-identity", "gaussian_kernel_identity",
                "General-parameter Gaussian convolution kernel identity",
                "For every real a and t, the source kernel G_a(t) equals "
                + "t^3/4 times the integral from zero to one of "
                + "(1+(2a-1)v^2) exp(-(1+v^2)t^2/4). "
                + "Integrating the derivative of v exp(-(1+v^2)t^2/4) gives "
                + "exp(-t^2/2) as the integral of (1-t^2 v^2/2) times the same exponential. "
                + "Substitution in G and linearity of the integral give the stated identity. "
                + "This is the source's pointwise identity (2.3)."),
            Proof("gaussian-kernel-base", "gaussian_kernel_eq_K",
                "The negative-parameter Gaussian kernel is the original K kernel",
                "A second interval integration by parts gives G_(-1)(t)=K(t), preserving the "
                + "original Gaussian convolution normalization and the exact K supplier."),
            Proof("gaussian-laplace-identity", "gaussian_laplace_identity",
                "The exact general-parameter Gaussian Laplace identity",
                "The original Mills Laplace formula and square convolution are combined with the "
                + "original kernelLaplace identity at parameter -1. A direct integration by parts gives "
                + "the t times Gaussian integral, and linearity in a then yields "
                + "Y_(a,a-2)(x)-(a-1)=integral exp(-xt) G_a(t) for every x>0."))));

    private static DocumentBlock Proof(string id, string name, string title, string narrative) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace." + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))),
            DescribeRole.Theorem);
}
