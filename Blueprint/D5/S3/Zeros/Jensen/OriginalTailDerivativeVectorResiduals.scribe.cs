using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class OriginalTailDerivativeVectorResidualsDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Definition(string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted residual budgets for the original primal theta tail.",
        H("The weighted original tail residuals"),
        Blocks(
            Definition("tail-residual", "tailResidual", "The first literal residual",
                "For a natural cutoff N and real A, alpha, x, R(x)=4*A^2*originalTail(N,x) " +
                "minus densityAdjoint(alpha,originalTail(N),x). The adjoint is " +
                "L_alpha(f)=f''+alpha*(f+x*f')."),
            Definition("tail-second-residual", "tailSecondResidual", "The second literal residual",
                "For N,A,alpha,x as above, R2(x)=4*A^2*R(x)-L_alpha(R)(x). " +
                "Alpha is fixed for spatial differentiation. When alpha=t/(2*n), " +
                "R itself depends on t."),
            Describe.Lean(
                DescribeId.Create("first-residual-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.first_residual_64"),
                H("The weighted first residual budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N>=1, A=pi*(N+1)^2>=max(64,a) and 0<=alpha<=a, " +
                    "exp(a*x^2/2)*|R(x)| is integrable over x>0 and its integral is " +
                    "at most 64*originalFlux(N)/A. The full shifted sum is bounded by " +
                    "256*A^2*exp(-A), and the full cubic flux is at least " +
                    "(11/2)*A^3*exp(-A). This estimate supplies the I response in the " +
                    "complete tail derivative vector."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("second-residual-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals.second_residual_1100"),
                H("The second residual with its external square weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N>=1, A=pi*(N+1)^2>=max(64,a) and 0<=alpha<=a, " +
                    "x^2*exp(a*x^2/2)*|R2(x)| is integrable over x>0 and its integral " +
                    "is at most 1100*originalFlux(N)/A. The first omitted mode retains " +
                    "its quartic-jet cancellation before integration and contributes at " +
                    "most 5100*A^2*exp(-A). Each later mode of scale s contributes at " +
                    "most 600*s^3*exp(-s); the complete sum is at most " +
                    "6000*A^2*exp(-A). This bound supplies both second-residual " +
                    "pairings in the D and M2 responses of the complete vector. " +
                    "These residual estimates assert no sign for the full-source head " +
                    "product or either head-tail cross term."))),
                DescribeRole.Lemma)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/OriginalPrimalTailProjection")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/OriginalPrimalTailResponse"))
        ]));
}
