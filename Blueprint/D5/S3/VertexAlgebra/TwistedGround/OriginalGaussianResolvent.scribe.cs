using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianResolventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Operator and Resolvent Moments",
        H("Original Gaussian Operator and Resolvent Moments"),
        Blocks(
            Paragraph(Text("The carrier is the complex square-summable sequence space, with coordinate n representing physical frequency n+1. The operator is the norm-summable series of rank-one maps with the literal OriginalGaussianMatrix.matrixEntry z (n+1) (m+1). Square cutoffs use Fin N, including the empty cutoff. Exact zero extension and restriction identify each cutoff with the existing finite Gaussian matrix; convergence in operator norm transfers its norm(z)^2 bound to the infinite operator on norm(z)<1.")),
            Paragraph(Text("Write b_s=centralBinom(s)/4^s and q=sqrt(r), where 0<r<1. The function F is the real restriction of OriginalHalfBinomialPeriod.period, and its series is sum b_k^2*r^k. Define L_s=sum b_k*b_(k+s)*r^k. The source e_s=halfBinomial(s)*q^s/sqrt(s), weighted source w_s=s*e_s, and candidate U_s=(-1)^s*q^s*L_s/(sqrt(s)*F) are all proved square summable. Frequency multiplication is used on these explicitly proved vectors, without asserting a bounded diagonal operator.")),
            Paragraph(Text("The existing positive half-binomial convolution, inverted by finite power-series multiplication, supplies the shifted finite convolution. Absolute convergence permits regrouping the actual double series. Keeping the t=0 boundary gives s*b_s*sum_(t>=1) b_t*r^t*L_t/(s+t)=L_s-b_s*F. The proved coordinate action then gives (1-M)U=e. The ordinary Neumann-series left inverse is applied only after the operator bound proves norm(M)<1.")),
            Paragraph(Text("The signed resolvent column is immediately consumed in a bilinear scalar contraction. Absolute convergence follows from the proved square-summable weighted source and the resolvent vector; a second absolute double-series regrouping reduces the scalar to (B-F)/F. The coefficient convolution gives B=sum b_k*r^k=1/sqrt(1-r). No complex conjugation occurs in this bilinear contraction.")),
            Paragraph(Text("The frequency-weighted column d_s=s*U_s is proved square summable using the polynomial-geometric majorant sum s^2*r^s. The literal entries obey (s+t)*M_st=w_s*w_t, with the original halfBinomial signs. Every row sum is absolutely convergent before this identity is summed. Combining it with (1-M)U=e gives (1+M)d=(B/F)w=w/(sqrt(1-r)*F). This argument never applies a bounded frequency-diagonal operator.")),
            Paragraph(Text("Define Rplus as the operator-norm Neumann series sum (-M)^k on the same complex square-summable carrier. The actual estimate norm(M)<=norm(z)^2<1 supplies convergence and both inverse laws. Applying the inverse to the weighted equation gives Rplus*w=sqrt(1-r)*F*d. The finite symmetry t<->n-t gives sum_(t=0)^n t*b_t*b_(n-t)=n/2. The binomial recurrence yields sum n*b_n*r^n=r*B/(2*(1-r)). A nonnegative summable double-series majorant permits the Cauchy regrouping, giving w^T*d=r*B/(4*(1-r)*F), and hence w^T*Rplus*w=r/(4*(1-r)). Absolute convergence of the complex bilinear contraction is also proved directly by the square-summable pairing. The transpose notation is bilinear and introduces no conjugates.")),
            Paragraph(Text("This result concerns the original coefficient model and its actual infinite operator. The trace differentiation passage, endpoint asymptotic, nome, occupation attribution, vertex-operator-algebra construction, fusion or anomaly statement, string theory, and AdS/CFT realization remain outside these results.")),
            Describe.Lean(
                DescribeId.Create("resolvent-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.resolvent_column"),
                H("resolvent_column"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every 0<r<1 and every n, the resolvent at sqrt(r) applied to the original source has coordinate (-1)^(n+1)*sqrt(r)^(n+1)*L_(n+1)/(sqrt(n+1)*F). The source-specific infinite residual is derived rather than assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bilinear-resolvent-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_resolvent_scalar"),
                H("bilinear_resolvent_scalar"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every 0<r<1 the bilinear series sum_(s>=1) s*e_s*(R e)_s converges absolutely and one plus its sum equals 1/(sqrt(1-r)*F(r))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn"),
                H("weightedColumn"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with 0<=r<1, this actual element of complex l2 has coordinate (n+1)*columnValue(r,n). Its membership proof uses the polynomial-geometric majorant, retaining the physical frequency n+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("opposite-resolvent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.oppositeResolvent"),
                H("oppositeResolvent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total definition is sum_(k>=0) (-operator(z))^k. Its inverse interpretation uses norm(z)<1, established for z=sqrt(r) in the source-specific results."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-column-equation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.weightedColumn_equation"),
                H("weightedColumn_equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with 0<r<1, (1+operator(sqrt(r))) applied to weightedColumn equals weightedSource multiplied by the complex scalar 1/(sqrt(1-r)*F(r)). This is the actual coordinate anticommutator consequence, with all row sums convergent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("opposite-resolvent-weighted-source"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.opposite_resolvent_weighted_source"),
                H("opposite_resolvent_weighted_source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with 0<r<1, the constructed opposite resolvent at sqrt(r) applied to weightedSource equals sqrt(1-r)*F(r) times weightedColumn. No inverse or source-action identity is supplied as a hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bilinear-opposite-resolvent-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianResolvent.bilinear_opposite_resolvent_scalar"),
                H("bilinear_opposite_resolvent_scalar"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with 0<r<1, the series sum_(n>=0) weightedSource(n)*(oppositeResolvent(sqrt(r))*weightedSource)(n) converges absolutely and equals the complex embedding of r/(4*(1-r)). This scalar consumes the signed weighted column, the finite weighted convolution and the absolute double-series regrouping. It is a coefficient-model result, not a determinant or physical realization theorem."))),
                DescribeRole.Theorem))));
}
