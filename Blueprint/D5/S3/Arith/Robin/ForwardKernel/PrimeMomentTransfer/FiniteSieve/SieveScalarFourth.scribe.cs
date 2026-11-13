using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveScalarFourthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveScalarFourth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fourth norms of finite sieve interval sums.",
        H("Uniform fourth norms of finite sieve interval sums."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-interval-norm4-bound"),
                DeclarationHandle.Create(Prefix + "sieve_interval_norm4_bound"),
                H("Uniform scalar interval estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume MSFinite and fix B>=1. There is C>=1 such that, for all sufficiently large real H, "
                        + "every positive modulus Q with P<=B log H and every 0<=a<=b satisfy "
                        + "norm4(X_I)<=C*(A_H*sqrt(b-a)+H^(1/4)*sqrt(log H)). "
                        + "The constant and the eventual lower bound for H are independent of Q and the endpoints.")),
                    Paragraph(Text(
                        "Each centered sieve variable has absolute value at most P, giving norm4(X_I)<=K*P. "
                        + "Use this estimate below K0=H^(1/4)/sqrt(log H). Above K0, the normalized MS error "
                        + "K^(-1/28)*(B log H)^18/log(H)^2 is eventually at most one. "
                        + "Indeed K0 is eventually at least H^(1/8), and log(H)^18/H^(1/224) tends to zero. "
                        + "The fourth-moment estimate then gives norm4(X_I)<=C_B*sqrt(K log H). "
                        + "Finally K<=H(b-a)+1 converts cardinality to length; the unit endpoint error is absorbed "
                        + "by H^(1/4)*sqrt(log H). Empty intervals are included."))),
                DescribeRole.Theorem))));
}
