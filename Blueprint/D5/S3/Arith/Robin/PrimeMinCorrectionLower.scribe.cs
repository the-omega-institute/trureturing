using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimeMinCorrectionLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform lower correction from finite geometric prime shells.",
        H("Uniform prime minimum lower correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-prime-minimum-tail-robin-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimeMinCorrectionLower.uniform_min_tail_robin_lower"),
                H("One threshold for the full lower coefficient and original margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every epsilon>0 and fixed c>0, a real A>1 is chosen before "
                        + "the positive natural integer m. Put X=log(m) and P=largestPrime(m). "
                        + "For every such m with the literal initial support equality "
                        + "m.primeFactors=Nat.primesLE(P), theta(P)>1, A<=X and c*X<=P, "
                        + "the correction (2*sqrt(2)-epsilon)/(sqrt(X)*log(X)) is strictly below "
                        + "tail(m)+log(log(X))-log(log(theta(P))). The same integer also satisfies "
                        + "the strict original-margin inequality obtained by adding Mertens.E₃(P) "
                        + "+log(log(theta(P)))-log(log(P)) to that correction.")),
                    Paragraph(Text(
                        "The proof bounds the actual finite minimum sum from below. The head "
                        + "p<=a*sqrt(X), with 0<a<sqrt(2), contributes theta(a*sqrt(X))/(X*log(X)). "
                        + "For fixed b>sqrt(2), r>1 and N>=1, shell k has endpoints "
                        + "b*r^k*sqrt(X) and b*r^(k+1)*sqrt(X). Both entries of the minimum "
                        + "dominate log(p)/(Y^2*log(Y)) at the upper endpoint Y. Nested finite "
                        + "prime sets give disjoint shells, and all omitted terms are nonnegative. "
                        + "Only the existing qualitative theta prime-number limit at the finitely "
                        + "many fixed endpoints and the existing logarithmic scale limit are used.")),
                    Paragraph(Text(
                        "The normalized finite lower sum tends to "
                        + "a+2/(r*b)*(1-r^(-N)). Set e=min(epsilon,1), s=sqrt(2), "
                        + "a=s-e/4, r=1+e/(16*s), and b=s*r. Choose N before X with "
                        + "r^(-N)<e/(8*s). This gives a lower constant above 2*s-e/2; "
                        + "the remaining margin absorbs the finite endpoint approximations. "
                        + "The last endpoint lies below c*X eventually, uniformly in P. "
                        + "The existing finite_min_tail_robin_bound then supplies both conclusions, "
                        + "including its original E₃ identity. No optimizer hypothesis, full layer "
                        + "inventory equality, record existence, RH hypothesis or signed pure-prime "
                        + "bound is introduced. Control of that signed quantity and the full "
                        + "RH/Robin/5040 goal remain separate obligations."))),
                DescribeRole.Theorem)))));
}
