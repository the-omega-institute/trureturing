using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class SingleChainCofactorBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/SingleChainCofactorBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete saturated prime chain forces its cofactor prime below the chain prime.",
        H("Single-Chain Cofactor Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-chain-cofactor-lt-prime"),
                DeclarationHandle.Create(Prefix + "single_chain_cofactor_lt_prime"),
                H("The cofactor prime is smaller than the chain prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be an actual whole covering system with pairwise distinct "
                        + "odd moduli greater than one, minimal in its number of classes "
                        + "and then in the sum of its moduli. Let p and ell be distinct "
                        + "primes. Assume that every original modulus divisible by p is "
                        + "one of the p ell^j classes for j in Fin p, and that their "
                        + "residues modulo p are injective.")),
                    Paragraph(Text(
                        "Then ell is strictly smaller than p. The proof takes the p class "
                        + "at height zero and one of its private points. This point avoids "
                        + "every p-free original class. The complete-chain residual theorem "
                        + "aligns it with every ell^j coordinate. Sum minimality supplies an "
                        + "actual pure ell class from the ell-divisible chain member.")),
                    Paragraph(Text(
                        "If ell were larger than p, choose an injective assignment from "
                        + "the p roots other than the guard root to ell roots while avoiding "
                        + "the private-point root and the pure-ell donor root. The two "
                        + "root exclusions leave enough ell roots. Chain mixed classes are "
                        + "excluded by the common residual alignment. Any possible collision "
                        + "between an ell u class and a p u class forces u to be an ell-chain "
                        + "power; coprimality then forces u=1, so only the pure-ell donor "
                        + "collision remains. The existing prime-root compression therefore "
                        + "constructs a whole odd distinct cover with fewer classes, contrary "
                        + "to count minimality.")),
                    Paragraph(Text(
                        "This is a conditional structural result for the declared complete "
                        + "chain interface. It does not settle the unrestricted odd covering "
                        + "problem and does not assert that arbitrary prime supports admit "
                        + "such a chain."))),
                DescribeRole.Theorem))));
}
