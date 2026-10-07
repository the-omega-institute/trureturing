using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class PrimeFactorPureClassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/PrimeFactorPureClass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime divisor of a modulus in a sum-minimal distinct odd covering "
            + "system occurs as a pure prime modulus, and every nonempty such system "
            + "contains a pure prime class.",
        H("Prime Factors and Pure Prime Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-divisor-modulus-is-present"),
                DeclarationHandle.Create(Prefix + "prime_dvd_modulus_is_present"),
                H("Prime divisors occur as pure prime moduli"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a distinct odd covering system with L classes, and "
                        + "suppose that the sum of its moduli is no larger than the sum "
                        + "for every distinct odd covering system with L classes. If p "
                        + "is prime and p divides the modulus of class i, then some "
                        + "class j has modulus p.")),
                    Paragraph(Text(
                        "If no class had modulus p, replace the modulus of class i by p "
                        + "and retain its residue. The old class is contained in the new "
                        + "one because p divides the old modulus, while oddness, the "
                        + "nonunit condition, and pairwise distinctness are preserved. "
                        + "The new modulus is strictly smaller, contradicting minimality "
                        + "of the modulus sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-pure-prime-class"),
                DeclarationHandle.Create(Prefix + "exists_pure_prime_class"),
                H("Nonempty covers contain a pure prime class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the system has at least one class, choose one of its "
                        + "indices. Its modulus is greater than one and therefore has "
                        + "a prime divisor. The preceding result supplies an index whose "
                        + "modulus is exactly that prime."))),
                DescribeRole.Theorem))));
}
