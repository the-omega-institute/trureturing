using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootErdos985Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/Erdos985.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Erdős #985 under finite-height Dirichlet zero exclusion",
        H("Erdős #985 under finite-height Dirichlet zero exclusion"), Blocks(
            Describe.Lean(DescribeId.Create("erdos985-large-prime"),
                DeclarationHandle.Create(Prefix + "erdos985_large_prime"),
                H("The large-prime range"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let p be prime and p≥5000000. For every " +
                    "nonprincipal complex Dirichlet character modulo p whose order divides " +
                    "the radical of p−1, assume its actual LFunction has no zero at s with " +
                    "Re(s)>1/2 and |Im(s)|≤4sqrt(p). There is a prime q<p whose order " +
                    "modulo p is p−1.")),
                Paragraph(Text(
                    "A nonprincipal character modulo a prime has conductor p: the conductor " +
                    "divides p, and conductor one characterizes the principal character. " +
                    "DirichletTriangleBound.characterTriangle_prime_bound bounds the norm " +
                    "of the actual triangular sum by (165458/111375)sqrt(p)log(p)−1/p. " +
                    "Taking the absolute real part and " +
                    "using DirichletTrianglePerron.characterTriangle_nat supplies exactly " +
                    "the nonprincipal input of " +
                    "SieveThresholdUnconditional.exists_prime_primitiveRoot. " +
                    "PrincipalTriangleLower.principal_smoothedCharacterSum_large supplies the " +
                    "unconditional principal lower bound (23/50)p. No RH premise remains."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("erdos985-compatibility"),
                DeclarationHandle.Create(Prefix + "erdos985_of_GRH"),
                H("The compatible finite-height interface"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "This compatibility name has only the finite-height hL hypothesis " +
                    "for primes at least five million. Its type contains no RH premise. " +
                    "It assembles the large-prime proof and the certified finite range, " +
                    "and is consumed by erdos985_of_finiteHeight. The finite-range " +
                    "checker metadata names this actual proof dependency."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("erdos985-of-finite-height"),
                DeclarationHandle.Create(Prefix + "erdos985_of_finiteHeight"),
                H("The conditional conclusion with a checked finite range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the stated finite-height LFunction exclusion only for " +
                    "primes p≥5000000 and nonprincipal characters of squarefree order " +
                    "dividing rad(p−1). Then every prime p≠2 has a prime primitive root below p. " +
                    "SmallPrimes.FiniteRangeExtended supplies the entire range 3≤p<5000000 from " +
                    "literal certificates checked by the Lean kernel. Positive slots use " +
                    "Lucas order tests with shared certified prime factors; composite " +
                    "slots exhibit a nontrivial divisor. The continuous odd-slot coverage " +
                    "has no omitted interval or final slot.")),
                Paragraph(Text(
                    "This is a finite-height conditional form of Erdős #985, obtained by " +
                    "assembling " +
                    "the repository's analytic chain with unconditional Chebyshev bounds. " +
                    "The finite-height exclusion is weaker than a global Dirichlet GRH " +
                    "assumption. The new principal estimate follows from the elementary " +
                    "Chebyshev factorial comparison. The local Mathlib search found " +
                    "no explicit Dirichlet GRH definition. " +
                    "Provenance is repo-derived; the method is the triangular explicit " +
                    "formula and the primitive-root character sieve. The repository's " +
                    "McGown–Treviño–Trudgian note concerns the sieve method. Literature " +
                    "priority for this exact conditional statement has not been verified " +
                    "offline. This is not a claim of a new solution to the original problem."))),
                DescribeRole.Theorem))));
}
