using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class MSConjectureSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete fourth moments control continuous second and fourth moments throughout every sublinear polynomial band.",
        H("Continuous sampling on sublinear bands"),
        Blocks(
            Paragraph(Text(
                "Let E(x)=psi(x)-x, D(v,x)=E(x+v)-E(x), N=floor(Y), H=floor(v), and L=log Y. "
                + "Fix 0<alpha<beta<1. Assume A>=1 and, uniformly for Y^alpha<=v<=Y^beta and all sufficiently large real Y, "
                + "the discrete fourth moment sum over 1<=n<=N is at most A Y v^2 L^2.")),
            Describe.Lean(
                DescribeId.Create("second-sampling-uniform-of-fourth"),
                DeclarationHandle.Create(Prefix + "second_sampling_uniform_of_fourth"),
                H("Asymptotically exact second moment sampling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every eta>0, the absolute difference between the continuous second moment integral from one to Y "
                    + "and the discrete second moment at N,H is at most eta Y v log(Y/v), uniformly on this band for sufficiently large Y. "
                    + "The pointwise logarithmic replacement error tends to zero after normalization. The exact terminal cell correction is bounded "
                    + "by D(H,N)^2; its square is at most the discrete fourth moment. Thus its relative size is O(sqrt(A/Y)/(1-beta)), "
                    + "which tends to zero for every beta<1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fourth-band-bound-of-discrete"),
                DeclarationHandle.Create(Prefix + "fourth_band_bound_of_discrete"),
                H("Continuous fourth moment band bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exists C4>=0 such that the integral of |D(v,x)|^4 from one to Y is at most C4 Y v^2 log^2(Y/v), "
                    + "uniformly on the exponent band for all sufficiently large Y. This is the predicate FourthMomentBandBoundFor for E=psi-id. "
                    + "The prefix replacement estimate and the discrete fourth bound control the continuous fourth moment. "
                    + "The inequality log(Y/v)>=(1-beta)log Y converts its logarithmic normalizer."))),
                DescribeRole.Theorem))));
}
