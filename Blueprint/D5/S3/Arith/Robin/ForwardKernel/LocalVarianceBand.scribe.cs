using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class LocalVarianceBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local variance from the cumulative variance band",
        H("Local variance from the cumulative variance band"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("variance-window-eventually"),
                DeclarationHandle.Create(Prefix + "variance_window_eventually"),
                H("Eventual window bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The uniform cumulative variance asymptotic implies that for every positive epsilon, all sufficiently large X satisfy the relative error bound simultaneously for Y in [X/2,4X] and Y^alpha<=v<=Y^beta. No convergence rate is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-variance-bound"),
                DeclarationHandle.Create(Prefix + "local_variance_bound"),
                H("Local square integral with an interval length term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals, and let 0<alpha<theta<beta<1. Suppose X>=4, R>0, epsilon>=0, [A,B] is contained in [X/2,4X], (4X)^alpha<=R, and 4R<=(X/2)^beta. If the window relative error is at most epsilon, then for every R<=v<=4R the integral of (E(y+v)-E(y))^2 over [A,B] is at most v*log(X)*(3*(B-A)+16*epsilon*X). Subtract the cumulative variances at B and A. The logarithmic inequality log(t)<=t-1 bounds the main difference, while both endpoint errors are bounded using A+B<=8X and log(Y/v)<=2*log(X)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-endpoint-bound"),
                DeclarationHandle.Create(Prefix + "local_endpoint_bound"),
                H("Moving endpoints under a local variance bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two differentiable endpoints in [A,B] whose derivatives are at least m>0 and whose absolute gap is at most R, the window variance bound gives an integral of their squared E-difference at most (20R/m)*log(X)*(3*(B-A)+16*epsilon*X). The interval length remains explicit. Apply the signed endpoint estimate with C=log(X)*(3*(B-A)+16*epsilon*X)."))),
                DescribeRole.Theorem))));
}
