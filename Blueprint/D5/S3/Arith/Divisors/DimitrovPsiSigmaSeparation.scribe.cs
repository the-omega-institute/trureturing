using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPsiSigmaSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n ≥ 2, (ψ(n)+σ(n))/(φ(n)+σ(n)) ≥ (n+1)/n, with equality exactly at the "
            + "primes.",
        H("Prime separation for (ψ+σ)/(φ+σ)"),
        Blocks(
            Describe.Lean(DescribeId.Create("dimitrov-psi-sigma-separation-result"),
                DeclarationHandle.Create(Prefix + "separation"),
                H("The separation inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let n ≥ 2 and put u=φ(n), v=ψ(n) (Dedekind psi) and w=σ(n). Then "
                    + "(v+w)/(u+w) ≥ (n+1)/n, with equality if and only if n is prime; this is "
                    + "the separation used for S. Dimitrov's Conjectures 2 and 7 "
                    + "(arXiv:2606.12484). Cross-multiplying, the claim "
                    + "is (n+1)u+w ≤ nv. For a prime p the three values are p−1, p+1 and p+1, "
                    + "and both sides equal p(p+1). Otherwise write n=pm with p the least prime "
                    + "factor, so 2 ≤ p ≤ m. The m multiples of p below n are not coprime to n, "
                    + "so u ≤ n−m. Every proper divisor d of n has n/d ≥ p, so d ≤ m; there are "
                    + "at most m of them, and w ≤ n+m². With v ≥ n+1 this gives (n+1)u+w ≤ (n+1)(n−m)+n+m², which is "
                    + "n(n+1)−(n−m)(m−1) < n(n+1) ≤ nv."))),
                DescribeRole.Theorem))));
}
