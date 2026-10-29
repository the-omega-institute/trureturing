using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MellinResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MellinResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized Mellin identity.",
        H("The generalized Mellin identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-kernel-mellin-residue"),
                DeclarationHandle.Create(Prefix + "forward_kernel_mellin_residue"),
                H("The generalized Mellin identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let alpha>=0 and assume there are real C and t0 with |psi(t)-t|<=C*t^alpha for every t>=t0. For each x0>=3, the Mellin integral F(s) of the original complete forward response has a remainder R holomorphic on Re(s)>alpha-7/10. On the overlap Re(s)>max(1/2,alpha-3/10), F(s)=-zeta'(s+1/2)/(2*zeta(s+1/2))-1/(2*(s-1/2))+R(s). Absolute Fubini gives the signed adjoint. Its principal term is t^(-s-1/2)/2, and its remainder and time derivative gain t^(-1/5). Partial summation gives the integral of the error against that derivative. The finite initial correction is entire. The original Mellin integral converges absolutely for Re(s)>alpha-3/10."))),
                DescribeRole.Theorem))));
}
