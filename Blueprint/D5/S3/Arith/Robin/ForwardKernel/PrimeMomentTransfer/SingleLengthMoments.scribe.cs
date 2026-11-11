using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A discrete fourth moment bound controls continuous sampling of the second and fourth moments.",
        H("Cumulative scalar sampling"),
        Blocks(
            Paragraph(Text(
                "Put E(x)=psi(x)-x, D(v,x)=E(x+v)-E(x), N=floor(Y), K=floor(v), "
                + "and L=log(Y). The discrete kth moment is the sum of D(K,n)^k "
                + "over 1<=n<=N; the continuous kth moment is its integral over [1,Y]. "
                + "The fourth moment assumption is sum D(K,n)^4 <= A*Y*v^2*L^2.")),
            Describe.Lean(
                DescribeId.Create("sampling-prefix-estimate"),
                DeclarationHandle.Create(Prefix + "sampling_prefix_estimate"),
                H("Prefix replacement without a terminal correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k equal to two or four, A>=1, Y>=2 and 1<=v<=Y, assume the discrete fourth moment is at most A Y v^2 log^2 Y. "
                    + "The difference between the continuous kth moment and the integral of the floor sampled kth power is at most "
                    + "32(1+A)Y sqrt(v log Y)^k times [10 sqrt(log Y/v)+(10 sqrt(log Y/v))^k]. "
                    + "This estimate keeps the fractional terminal cell inside the integral and applies at every sublinear polynomial length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampling-second"),
                DeclarationHandle.Create(Prefix + "sampling_second"),
                H("Second moment sampling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is an absolute C>0 such that, for A>=1, Y>=2 and 1<=v<=Y, "
                    + "the discrete fourth moment assumption bounds the absolute difference "
                    + "between the continuous and discrete second moments by "
                    + "C*(1+A)*Y*(v*L)*(sqrt(L/v)+L/v+(v*L)/Y)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampling-fourth"),
                DeclarationHandle.Create(Prefix + "sampling_fourth"),
                H("Fourth moment sampling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is an absolute C>0 such that, for A>=1, Y>=2 and 1<=v<=Y, "
                    + "the discrete fourth moment assumption bounds the absolute difference "
                    + "between the continuous and discrete fourth moments by "
                    + "C*(1+A)*Y*(v*L)^2*(sqrt(L/v)+(L/v)^2+(v*L)^2/Y)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Normalize Lebesgue measure on [1,Y] to a probability measure and divide "
                + "the increments by sqrt(v*L). Fourth moments and the L4 triangle inequality "
                + "control the scalar replacement error, whose pointwise size is O(sqrt(L/v)). "
                + "For a lattice function F, its integral minus the right endpoint prefix sum "
                + "is exactly (Y-N-1)*F(N); this correction also applies when Y is an integer. "
                + "A pointwise bound for the terminal lattice increment gives the last rate term.")))));
}
