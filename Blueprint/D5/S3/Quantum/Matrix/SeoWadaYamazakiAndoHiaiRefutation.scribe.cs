using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SeoWadaYamazakiAndoHiaiRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/seowadayamazaki2026andohiai");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spectral geometric Ando-Hiai implication fails near an endpoint.",
        H("The spectral geometric Ando-Hiai implication has counterexamples"), Blocks([
            Paragraph(Text("Problem 3.11 asks whether A natural_t B at most I implies A^q natural_t B^q at most I for all strictly positive operators, every t strictly between zero and one other than one half, and every q strictly positive and at most one. The order is the Loewner order. Theorem 3.9 gives the implication when q is at most both t/(1-t) and (1-t)/t. Remark 3.10 discusses the remaining range and the numerical search.")),
            Describe.Lean(DescribeId.Create("spectral-geometric-mean"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.specMean"),
                H("The spectral geometric mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive definite complex matrices and real t, F_t(A,B) = A natural_t B = (A^(-1)#B)^t A (A^(-1)#B)^t, where X#Y = X^(1/2)(X^(-1/2)Y X^(-1/2))^(1/2)X^(1/2). The existing specMean definition is used without replacing the source mean. All powers are spectral real powers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spectral-real-power"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/SpectralPower.mpow"),
                H("The spectral real matrix power"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The existing mpow definition applies the real function x maps to x^q through the real continuous functional calculus. On positive definite matrices this is the source spectral power A^q. The same definition supplies both powers in F_t(A^q,B^q)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal spectral geometric Ando-Hiai assertion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The closed assertion quantifies over all real t and q with zero less than t less than one, t different from one half, and zero less than q at most one. It quantifies over every natural dimension m and every pair of positive definite complex m by m matrices A and B. It requires that specMean A B t at most I implies specMean (mpow A q) (mpow B q) t at most I. The finite dimensional assertion is a necessary restriction of the source operator assertion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The universal assertion is false"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The conclusion is the negation of the closed assertion. For every q strictly between zero and one, the construction supplies one positive definite complex two by two pair for which the implication fails at every sufficiently small positive t. Its inputs are A_u=diag(1,exp(-u/2)) and B_(u,b)=exp(b)/4 times the symmetric matrix with diagonal entries 3 exp(u)+exp(-u) and exp(u)+3 exp(-u), and off-diagonal entry sqrt(3)(exp(u)-exp(-u)). Their spectral q powers are exactly A_(q u) and B_(q u,q b). Normalize by h=exp(-u/4), put p=h^3-h^5, r=1-h^8, W=sqrt(p^2+r^2-p r), Z=sqrt(3+h^2+8h^5+h^8+3h^10), and T=1+h^3+h^5+h^8. Set alpha=(r/2-p)/W and H(u)=alpha(h)(3u/8+log((T+W)/Z)). The exact rationalization alpha(h)-1/2=h^3 E(h), with E continuous at zero, and u exp(-3u/4) tending to zero prove H(u)-3u/16 tends to log(2/sqrt(3))/2. Consequently D=H(q u)-q H(u) is positive for some finite u. An explicit positive symmetric transport P has diagonal numerators T+r/2-p and T-r/2+p, off-diagonal numerator sqrt(3) r/2, and common factor exp(b/2)/(h^2 Z). Direct multiplication gives P A_u P=B_(u,b), so uniqueness of the positive Riccati solution identifies P=A_u^(-1)#B_(u,b). Its two positive spectral values are exp(b/2)(T+W)/(h^2 Z) and exp(b/2)(T-W)/(h^2 Z). Two-point functional calculus differentiates the real entries of P^t A_u P^t at zero; the first entry slope is b+u/4+2H(u). Choosing b=-u/4-2H(u)-D/q makes the original and powered-input first entry slopes -D/q and D. In the original mean, both the first principal minor and determinant of I minus the mean have positive derivatives at zero, so the two by two positive definiteness criterion gives the required order on a positive interval. In the powered-input mean, the first entry exceeds one, which excludes the order by diagonal nonnegativity. Taking q=1/2 and t=min(t_0/2,1/4) refutes the universal assertion. The endpoint symmetry, the source central sufficient range, the diagnosis of the Gan-Tam inverse-eigenvalue step, and the fixed positive t asymptotic are separate paper statements in the accompanying problem discussion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("seo-wada-yamazaki-2026-problem-3-11-spectral-ando-hiai"),
                    ResolutionKind.Refuted))])));
}
