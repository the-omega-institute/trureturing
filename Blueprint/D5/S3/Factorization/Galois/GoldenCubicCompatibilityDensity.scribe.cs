using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicCompatibilityDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual GCC4 unrestricted rational-prime compatibility event has positive Dirichlet density.",
        H("Golden Cubic Compatibility Density"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-compatibility-density"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity.actual_compatibility_density"),
            H("Exact unrestricted rational-prime density"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each unit residue a modulo 80 times 3 to the power j plus 2 with image one "
                    + "modulo three, unrestricted rational primes in that class whose prime above "
                    + "E has the actual character-defined Frobenius have Dirichlet density two "
                    + "divided by the totient of the modulus and 3 to the power twice the earlier "
                    + "support size plus two. This density is positive.")),
                Paragraph(Text(
                    "The proof applies the cited general Chebotarev theorem to the computed "
                    + "two-element class, removes finite modulus and ramification exceptions, "
                    + "and identifies the prime-ideal Dirichlet series with the rational-prime "
                    + "series. Separately, there exists a unit residue b with positive representative "
                    + "that reduces to one modulo three and satisfies the oddness, quadratic-character "
                    + "and stated congruence conditions. Positive density among "
                    + "unrestricted primes does not assert a prime in the finite current block."))),
            DescribeRole.Theorem))));
}
