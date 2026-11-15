using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class FiniteAffineGaussianSewingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FiniteAffineGaussianSewing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute convergence and sewing of finite native affine Gaussians with arbitrary complex means.",
        H("Finite affine Gaussian sewing"),
        Blocks(
            Paragraph(Text("Let I be a finite type, possibly empty. Let A and B be complex symmetric matrices for ordinary transpose, with their Euclidean operator norms strictly below one, and let mu and nu be arbitrary complex vectors on I. Write w(d) for the product of occupation factorials and c(A,mu,d,k) for the existing native Gaussian coefficient of affineKernel A mu at d.sumElim(single () k). The existing affineCoefficient is the sum over 0 <= k <= degree(d). No positivity, Hermitian symmetry, or smallness of either mean is assumed.")),
            N("affine_majorant_summable", "Strong auxiliary majorant", "The family w(d)*(sum_{k<=degree(d)} norm(c(A,mu,d,k)))^2 is summable over all occupations d. Zero extension preserves the internal Euclidean operator bound. With a=norm(Aop), M=norm((affineKernel 0 mu)op), choose epsilon=(1-a)/(2*(M+1))>0. The enlarged C=affineKernel A (epsilon*mu) is contractive. Write g_C(e) for its native Gaussian coefficient. Diagonal coefficient scaling gives c(A,mu,d,k)=t^k*g_C(d.sumElim(single () k)), t=epsilon inverse. Weighted finite Cauchy-Schwarz bounds the squared sum of norms by exp(t^2)*sum_k k!*norm(g_C(d.sumElim(single () k)))^2. The injective occupation map (d,k) to d.sumElim(single () k) has weight w(d)*k!, so the centered occupation square sum dominates this bound uniformly in d."),
            N("affine_joint_norm_summable", "Joint absolute convergence", "The joint family indexed by (d,(k,l)), norm(w(d)*c(A,mu,d,k)*c(B,nu,d,l)), is summable. The public elementary Gaussian vanishing theorem proves each coefficient is zero for k>degree(d), using nonzero native occupation weights. Thus every auxiliary fiber has a finite rectangle of support. Its norm sum is w(d)*m_A(d)*m_B(d), where m is the preceding sum of norms. The two strong square majorants dominate this product through 2*x*y <= x^2+y^2. There is exactly one w(d), and no auxiliary k! or l! in the joint family."),
            N("finite_affine_sewing", "Arbitrary-mean sewing evaluation", "The native pairing sum_d w(d)*affineCoefficient A mu d*affineCoefficient B nu d converges absolutely and equals exp((1/2)*sum_{n>=0} trace((A*B)^(n+1))/(n+1))*exp((1/2)*sum_x sum_y E(x,y)). Here E is exactly FiniteGaussianSewing.effectiveKernel with external types Unit and Unit, external blocks P=Q=0, R () i=mu i, and S i ()=nu i. The coefficientwise finite sewing theorem applies after swapping the A-side auxiliary and internal coordinates. Joint absolute convergence permits exchanging internal and auxiliary sums. The exact coordinate equivalence from pairs of natural numbers to occupations of Unit plus Unit reduces the remaining sum to GaussianEntireEvaluation.gaussianCoefficient_tsum for this actual E; no symmetry or contraction of E is needed."),
            Paragraph(Text("These are classical finite Gaussian identities on the native coefficient carrier. The coefficient scaling, centered factorial Fock estimate, elementary vanishing, coefficientwise finite sewing, and entire Gaussian evaluation are reused from their respective modules. No literature novelty is claimed. Infinite-mode limits, identification with the original charged source rows, identityK and C1, and the full Moonshine/string/AdS-CFT construction remain separate mathematical obligations."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("finite-affine-gaussian-sewing-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
