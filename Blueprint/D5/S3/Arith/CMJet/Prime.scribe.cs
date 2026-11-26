using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/Prime.";

    private static readonly LibraryNoteRef Alpoge =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterating the derivation p times over the field of p elements gives a scalar multiple "
            + "of the original derivation. The scalar vanishes at primes congruent to three modulo "
            + "four.",
        H("The restricted lemniscatic derivation at odd primes"),
        Blocks(
            Paragraph(Text("Alpöge’s CM derivative argument motivates the prime-by-prime analysis. "
                + "The proof uses polynomial pairs and the coefficient support of the square "
                + "of the derivation.")),
            Describe.Lean(
                DescribeId.Create("iter-mul"),
                DeclarationHandle.Create(Prefix + "iter_mul"),
                H("Iterated Leibniz rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At order n, the coefficient of the product of the order n−k and k derivatives is the "
                        + "binomial coefficient n choose k. The induction uses the first-order Leibniz rule and "
                        + "Pascal's identity."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("primeiter"),
                DeclarationHandle.Create(Prefix + "primeIter"),
                H("The restricted derivation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p, each interior binomial coefficient at order p vanishes in the residue "
                        + "field. The two end terms give the derivation law for the actual p-fold iterate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-iter-scalar"),
                DeclarationHandle.Create(Prefix + "prime_iter_scalar"),
                H("The scalar is determined by the derivative of X"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an odd prime p, write D^pX = YF, where F has degree at most p−1. The curve "
                        + "relation and commutation with D force (1 − X⁴)F′ = 0. Thus F is constant, and the "
                        + "action on X and Y determines D^p on all pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inert-iter-zero"),
                DeclarationHandle.Create(Prefix + "inert_iter_zero"),
                H("Vanishing at inert primes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Alpoge),
                Blocks(Paragraph(Text(
                    "When p ≡ 3 modulo 4, the coefficient of X in Q^(p/2)X is zero by the modulo-four "
                        + "support rule. That coefficient gives the scalar of the restricted derivative, so D^p "
                        + "vanishes on every pair over the residue field."))),
                DescribeRole.Theorem)
        )));
}
