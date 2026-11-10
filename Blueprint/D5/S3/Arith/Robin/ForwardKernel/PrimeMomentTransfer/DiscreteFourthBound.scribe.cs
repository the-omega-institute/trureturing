using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class DiscreteFourthBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete interval increments have a uniform fourth moment bound.",
        H("Discrete fourth moment bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-discrete-fourth-bound"),
                DeclarationHandle.Create(Prefix + "uniform_discrete_fourth_bound"),
                H("Uniform discrete fourth power bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume normalized empty and singleton singular series, the four-point mean-square correlation bound, and the interval correlation estimates. "
                    + "For 0<alpha<beta<1/4 and M>=1, there is a nonnegative constant C such that, for all sufficiently large real N, the sum of |S(H,a,b,n)|^4 over N<n<=2N is at most C*N*(H*log N)^2, uniformly for integer lengths in the polynomial band and 0<=a<=b<=M. "
                    + "One can take C=3+3*M^2. The cutoff indicator of [1,2] has supremum plus total variation at most three, equals one at every discrete sample n/N, and has integral one. "
                    + "Applying the uniform fourth asymptotic with four equal intervals and tolerance one gives the bound because 0<=kappa<=1 and the overlap pairing is at most 3*M^2."))),
                DescribeRole.Theorem))));
}
