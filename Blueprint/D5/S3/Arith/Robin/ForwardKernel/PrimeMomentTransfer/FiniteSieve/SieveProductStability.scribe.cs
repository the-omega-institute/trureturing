using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveProductStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveProductStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stability of finite sieve products under fourth norm perturbations.",
        H("Stability of finite sieve products under fourth norm perturbations."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-product-moment-replacement"),
                DeclarationHandle.Create(Prefix + "sieve_product_moment_replacement"),
                H("Normalized product replacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two collections of k factors with fourth norms at most K and factorwise difference norms at most D, the absolute difference of their expected products is bounded by k D K^{k−1}, for 1 ≤ k ≤ 4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-wick-pairing-replacement"),
                DeclarationHandle.Create(Prefix + "sieve_wick_pairing_replacement"),
                H("Wick pairing replacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For four factors satisfying the same K and D bounds, the difference between the sums of the three Wick pairing products is at most twelve times D times K cubed. Each covariance replacement costs at most two D K, and each covariance has size at most K squared."))),
                DescribeRole.Theorem))));
}
