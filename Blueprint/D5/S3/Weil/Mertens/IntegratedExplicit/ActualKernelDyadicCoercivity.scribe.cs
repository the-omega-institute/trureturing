using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelDyadicCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic averaged box energy controls the local Gram matrix of the complete arithmetic kernel.",
        H("Dyadic local conditioning of the actual arithmetic kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-kernel-dyadic-conditioning"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelDyadicCoercivity.exists_window_dyadic_conditioning"),
                H("A logarithmically accumulating local coercivity margin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exist fixed positive delta, eta and r, with eta<=delta<log(2), such that the following holds simultaneously for every n>=2. Let x:Fin(n)->Real have diameter at most delta and pairwise separation at least g>0. For every natural J satisfying 2^J*g<=eta, put lambda=g*(r/2+J/128) and H(i,j)=K(x(i)-x(j)), where K is the literal complete arithmetic kernel from ActualKernelLocalPositivity. Every complex coefficient family c satisfies Re(c* H c)>=lambda*sum_i normSq(c(i)). The real inverse obeys abs(H^(-1)(i,j))<=1/lambda, and q=1+sum_i,j abs(H^(-1)(i,j))<=1+n^2/lambda.")),
                    Paragraph(Text("The original positive representation is retained on its original delta window: K(t)=integral_(0,delta] max(s-abs(t),0)*D2(s) ds+r*max(L-abs(t),0), with r>0 and L>delta. The original limit s*D2(s)->1/2 selects eta<=delta on which D2(s)>=1/(4*s). Only this smaller part of the existing mixing measure is used; no new representation or new numerical value of delta, eta or r is asserted.")),
                    Paragraph(Text("For every band [a,2*a] with g<=a and 2*a<=eta, the uniform averaged box estimate contributes at least (a*g/16)*sum normSq(c). Since D2(s)>=1/(8*a) throughout that band, its weighted contribution is at least (g/128)*sum normSq(c). The J bands are taken half-open at their left endpoints and cover (g,2^J*g]; finite additivity gives J*g/128. The remainder of the original positive mixing measure is discarded only after its quadratic form is identified as nonnegative and integrable. Prefix functions are never integrated separately on the whole line.")),
                    Paragraph(Text("The wide tent contributes (r*g/2)*sum normSq(c). Its exact finite proof uses ordered gap telescoping, centered prefixes P_k-S/2 and the identity Q=(L-D/2)*normSq(S)+2*sum_k gap_k*normSq(P_k-S/2), with sum normSq(c)<=normSq(S)+4*sum_k normSq(P_k-S/2). Sorting is only a reindexing of the full separated configuration. The complex triangle identity is reused from its original owner. Replacing closed interval indicators by half-open ones changes only finitely many endpoints, so the averaged energy has the same integral.")),
                    Paragraph(Text("For the real inverse, set v=H^(-1)e_j. The same lambda bound gives lambda*sum_i v_i^2<=v_j. Each coordinate square is at most that sum, hence lambda*v_j^2<=v_j and v_j<=1/lambda. It follows that lambda*v_i^2<=1/lambda and abs(v_i)<=1/lambda. Summing over the n^2 entries gives the stated q bound. This proof requires only positive definiteness, the existing finite matrix inverse, and coordinate-square inequalities.")),
                    Paragraph(Text("For the separate near-node Schur construction, substituting q<=Q with Q=1+n^2/lambda conservatively replaces (8*q)^(-2) by (8*Q)^(-2) in the radius min(gap/2,exp(-4*(abs(cusp_c)+arithmeticLipschitz+1)),(8*q)^(-2)). The Schur source is not a dependency here, and this substitution is a mathematical correspondence rather than an assertion that the unfinished Schur construction has been compiled. The averaged estimate strengthens the coarse bound in the existing local positivity paper; it is not a claim of academic novelty. Global far-block control, uniform prescribed integer insertion, the signed Robin residual and the Riemann hypothesis remain unresolved by this local theorem."))),
                DescribeRole.Theorem))));
}
