using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentMixtureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K moment certificate.",
        H("Original full-kernel certificate source"), Blocks(
            Describe.Lean(DescribeId.Create("complete-positive-mixture-head-gamma"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_head_gamma"),
                H("Finite Gamma head below the complete mixture"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D>0, q>=1, m>=1 and delta_q<=1/m, the first M terms give Re Q_P >= E sum_{n<M} c_n 2lambda_n/(1+lambda_n^2/m), with the literal positive mixture coefficients and rates. Each term consumes the division-free Gamma gap certificate; positive energy permits cancellation inside that branch, while E=0 follows from the nonnegative exponential form. The existing complete-tail theorem keeps every omitted term nonnegative. The small-window endpoints consume M=20 with m=138 and m=1600."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-positive-mixture-logarithmic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_logarithmic"),
                H("complete positive mixture logarithmic"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete actual P(t)=exp(-abs(t)/2)trivialT(abs(t)) has Re Q_P >= (log(q/D)-1)E for q>=1, q/D>=8 and atomic moments 0,...,q zero. The retained compiled exponential-moment supplier is consumed at every actual rate 2k+1/2. Absolute coefficient domination justifies quadratic interchange, and every tail form is nonnegative. For M=floor(q/D), A_M=H_(2M+1)-1 and the exact loss is delta_q(2M^2+3M+A_M/4). Harmonic and log/floor bounds give the coefficient without dividing by E."))),
                DescribeRole.Theorem))));
}
