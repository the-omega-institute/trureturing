using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentPaymentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K moment certificate.",
        H("Original full-kernel certificate source"), Blocks(
            Describe.Lean(DescribeId.Create("actual-cutoff-resolvent-payment"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_cutoff_resolvent_payment"),
                H("actual cutoff resolvent payment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal V has abs(V)<=(8+4C+2B)exp(D/2)W. Integrating EACH finite Mangoldt atom gives the inclusive Abel identity sum w_n=exp(-D/2)psi(exp D)+(1/2)integral_[0,D]exp(-t/2)psi(exp t), including a zero tail at equality entries. Global actual psi<=(1+C)exp(t) yields sum w_n<=2(1+C)exp(D/2). Actual S/Z control pays both the continuous resolvent integral and the signed b(D)Z/2 boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-continuum-moment-payment"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentPayments.actual_continuum_moment_payment"),
                H("actual continuum moment payment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For actual G(t)=integral_0^t prefix, mass and the first atomic moment give G(0)=G(D)=0. The retained finite causal Gram/FTC identities, generalized from positive to nonzero lambda, are applied at -1/2 and identified with the actual growing-exponential prefix curvature. Compact-square Fubini identifies the causal triangle with H(G), giving H(A)=-integral norm(G)^2-H(G)/4. The literal growing row is (M_D-1)g(u)+u exp(u/2)+(D-u)exp((D-u)/2), at most (M_D+D-1)g(u). The weighted complex pair integration and retained complex primitive gap therefore pay H(A)>=-((M_D+D+3)/4)delta_q E."))),
                DescribeRole.Theorem))));
}
