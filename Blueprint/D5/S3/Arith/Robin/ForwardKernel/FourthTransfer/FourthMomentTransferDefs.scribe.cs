using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FourthMomentTransferDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local fourth energy and interval-weighted fixed-scale mixed moments",
        H("Fourth-moment transfer definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-fourth-energy-window"),
                DeclarationHandle.Create(Prefix + "localFourthEnergyWindow"),
                H("Local fourth energy on a window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every X/2<=A<=B<=4X and (4X)^alpha<=v<=(X/2)^beta, the integral of |E(y+v)-E(y)|^4 over [A,B] is at most C*v^2*log(X)^2*(B-A+epsilon*X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-fourth-energy-for"),
                DeclarationHandle.Create(Prefix + "LocalFourthEnergyFor"),
                H("The local fourth-energy hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant C is nonnegative. There is a nonnegative function epsilon(X) tending to zero such that, for all sufficiently large X, the local fourth-energy window bound holds simultaneously for every admissible A, B, and v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-scale-b"),
                DeclarationHandle.Create(Prefix + "fixedScaleB"),
                H("A fixed-scale normalized increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At position x, divide E(x+c*X^theta)-E(x) by sqrt(X^theta*log(X)). The length coefficient c is fixed independently of x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-block-moment"),
                DeclarationHandle.Create(Prefix + "fixedBlockMoment"),
                H("A mixed moment on a macroscopic interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integrate the product of k fixed-scale normalized increments against dyadic logarithmic probability at scale X, multiplied by the indicator that U_X=x/X lies in the closed interval [u,v]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-scale-mixed-moments"),
                DeclarationHandle.Create(Prefix + "FixedScaleMixedMoments"),
                H("Interval-weighted fixed-scale convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every M>0, every k-tuple c with each coefficient in [0,M], and every 1<=u<v<=2, the fixed block moment tends as X tends to infinity to W(c) times the logarithmic probability of [u,v] at scale one. The interval indicator remains part of the moment being tested."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-b"),
                DeclarationHandle.Create(Prefix + "movingB"),
                H("A moving normalized increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the fixed-scale normalization with the length coefficient a(U_X), where U_X=x/X. The increment length is X^theta*a(x/X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frozen-b"),
                DeclarationHandle.Create(Prefix + "frozenB"),
                H("A normalized increment frozen on cells"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Partition (1,2] into the n disjoint cells (1+j/n,1+(j+1)/n]. On each cell evaluate the fixed-scale normalized increment with coefficient a(1+j/n). The sum is zero outside these cells; for n=0 it is the empty sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourth-k"),
                DeclarationHandle.Create(Prefix + "fourthK"),
                H("The uniform fourth-moment constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For energy constant C and length bound M, define K_M=1312*C*M^2/log(2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("freeze-coefficient"),
                DeclarationHandle.Create(Prefix + "freezeCoefficient"),
                H("The fourth-order freezing constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For energy constant C, derivative bound L, and cell count n, define 1312*C*(1+L)^2/(3*n^2*log(2)). Its use in freezing estimates assumes n>0."))),
                DescribeRole.Definition))));
}
