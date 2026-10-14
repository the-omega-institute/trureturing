using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeChargedFockFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native full-charge Hermitian and BPZ generators",
        ArtifactId.Parse("D5/S3/VertexAlgebra/LatticeChargedFockForms"),
        "D5.S3.VertexAlgebra.LatticeChargedFockForms",
        Blocks(
            Paragraph(Text("The carrier is the original finitely supported charge family of finite oscillator polynomials. Coefficient conjugation fixes every charge and oscillator variable and conjugates every complex coefficient. PCT is the original linear lattice reflection composed with that genuine antilinear map; its native lattice phase is one. The linear reflection alone is not PCT.")),
            Paragraph(Text("The Hermitian form sums the unchanged neutral fockForm over equal charge sectors, conjugate-linear in the left slot and linear in the right. BPZ composes its left slot with PCT and is complex bilinear, selecting opposite charges. The coefficient transpose reverses the actual finite creation-translation convolution. The cocycle phase is paritySign of half the integral self-pairing, obtained from integral_cocycle_square; it is distinct from the phase-one PCT covariance.")),
            Paragraph(Text("The charged vertex index reflects to B(alpha,alpha)-n-2, not simply to minus n. With h_alpha=B(alpha,alpha)/2 and the index convention n=m+h_alpha-1, reflection becomes m to minus m. Identifying h_alpha with an actual conformal weight requires the corresponding Sugawara and conformal hypotheses separately. Neutral integer modes transpose with no Hermitian sign and a minus BPZ sign, including their actual charge-dependent zero mode. Mismatched charges vanish on both sides of each identity.")),
            Paragraph(Text("No inverse Gram matrix, positivity, nondegeneracy, invariant-form premise, occupation cutoff or abstract replacement field is used. Degenerate and indefinite integral Gram forms and rank zero remain in scope. These are classical lattice Fock identities, with no novelty claimed. Full descendant opposite modes, L1 local nilpotence, ghost and original-Q adjoints, physical quotient isometry, no-ghost, moonshine, string theory and AdS/CFT remain separate open obligations.")),
            Describe.Lean(
                DescribeId.Create("latticechargedfockforms-hermitian-charged"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargedFockForms.hermitian_charged"),
                H("Actual full-charge charged Hermitian adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alpha, integer n and two full finite-charge states, H(E_alpha[n]u,v)=paritySign(B(alpha,alpha)/2) H(u,E_minus_alpha[B(alpha,alpha)-n-2]v)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargedfockforms-bpz-charged"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargedFockForms.bpz_charged"),
                H("Actual full-charge charged BPZ adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same unrestricted states, B(E_alpha[n]u,v)=paritySign(B(alpha,alpha)/2) B(u,E_alpha[B(alpha,alpha)-n-2]v). The charge on the reflected BPZ generator is alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargedfockforms-hermitian-neutral"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargedFockForms.hermitian_neutral"),
                H("Every integer neutral Hermitian mode adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H(a_i(m)u,v)=H(u,a_i(-m)v), including the actual charge-dependent zero mode."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargedfockforms-bpz-neutral"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargedFockForms.bpz_neutral"),
                H("Every integer neutral BPZ mode adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B(a_i(m)u,v)=-B(u,a_i(-m)v). This uses antilinear coefficient conjugation and the genuine linear theta covariance, not a primary-state assumption."))),
                DescribeRole.Theorem))));
}
