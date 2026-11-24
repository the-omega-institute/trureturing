using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootErdos985Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/Erdos985.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Erdős #985 in a GRH conditional form",
        H("Erdős #985 in a GRH conditional form"), Blocks(
            Describe.Lean(DescribeId.Create("erdos985-large-prime"),
                DeclarationHandle.Create(Prefix + "erdos985_large_prime"),
                H("The large-prime range"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let p be prime and p≥3483482. Assume RiemannHypothesis. For every " +
                    "nonprincipal complex Dirichlet character modulo p whose order divides " +
                    "the radical of p−1, assume its actual LFunction has no zero at s with " +
                    "Re(s)>1/2 and |Im(s)|≤4sqrt(p). There is a prime q<p whose order " +
                    "modulo p is p−1.")),
                Paragraph(Text(
                    "A nonprincipal character modulo a prime has conductor p: the conductor " +
                    "divides p, and conductor one characterizes the principal character. " +
                    "DirichletTriangleBound.characterTriangle_prime_bound bounds the norm " +
                    "of the actual triangular sum by (165458/111375)sqrt(p)log(p)−1/p. " +
                    "This is below (3/2)sqrt(p)log(p); taking the absolute real part and " +
                    "using DirichletTrianglePerron.characterTriangle_nat supplies exactly " +
                    "the nonprincipal input of SieveThresholdExact.exists_prime_primitiveRoot. " +
                    "TriangleRampZeta.principal_smoothedCharacterSum_lower supplies the " +
                    "principal lower bound p/2−sqrt(p). RH enters only this principal term."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("erdos985-of-grh"),
                DeclarationHandle.Create(Prefix + "erdos985_of_GRH"),
                H("The conditional conclusion with an explicit finite premise"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume RH and the stated finite-height LFunction exclusion only for " +
                    "primes p≥3483482 and nonprincipal characters of squarefree order " +
                    "dividing rad(p−1). Also assume that every prime 3≤p<3483482 has a " +
                    "prime primitive root below p. Then every prime p≠2 has such a root. " +
                    "The small-prime clause is an explicit hypothesis for a separate " +
                    "certificate module; no finite certificate is asserted here.")),
                Paragraph(Text(
                    "This is the GRH conditional form of Erdős #985, obtained by assembling " +
                    "the repository's analytic chain with its exact sieve threshold. " +
                    "The finite-height exclusion is weaker than a global Dirichlet GRH " +
                    "assumption. The pinned Mathlib NumberTheory sources supply RH but " +
                    "no Dirichlet GRH definition was found in the local search. " +
                    "Provenance is repo-derived; the method is the triangular explicit " +
                    "formula and the primitive-root character sieve. The repository's " +
                    "McGown–Treviño–Trudgian note concerns the sieve method. Literature " +
                    "priority for this exact conditional statement has not been verified " +
                    "offline. This is not a claim of a new solution to the original problem."))),
                DescribeRole.Theorem))));
}
