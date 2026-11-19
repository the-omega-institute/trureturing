using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class TotientPrimeProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/TotientPrimeProducts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal totient density is a product over the distinct prime divisors.",
        H("The totient prime product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("totient-prime-product"),
                DeclarationHandle.Create(Prefix + "totient_prime_product"),
                H("The totient prime product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive natural n, n/phi(n) is the product of (1-1/p)^(-1) over the distinct prime divisors p of n. This identifies the density factor in the Ramanujan expansion."))),
                DescribeRole.Theorem))));
}
