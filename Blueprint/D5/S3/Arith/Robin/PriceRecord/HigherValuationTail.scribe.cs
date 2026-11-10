using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherValuationTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated prime divisors have a uniform quantitative Euler-tail bound at every positive price.",
        H("Repeated Prime Euler Tails"),
        Blocks(Describe.Lean(
            DescribeId.Create("higher-valuation-tail"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherValuationTail.higher_valuation_tail"),
            H("A uniform bound for the complete repeated-prime tail"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let m >= 2 be a natural number and lambda > 0 a real price. Assume the literal full predecessor record: for every natural n with 0 < n < m, goldenResourceObjective(lambda,n) < goldenResourceObjective(lambda,m). Put P = OriginalEndpointPrimeTail.largestPrime(m) and a(p) = m.factorization(p). Then the sum over every prime divisor p of m with a(p) >= 2 of OriginalEndpointPrimeTail.layerTail(m,p) is at most 6/P^(2/3). Here layerTail(m,p) = -log(1-(1/p)^(a(p)+1)), with real casts. The largest prime P is included whenever its valuation is at least two; an empty set of repeated primes contributes zero.")),
                Paragraph(Text("Set u = P^(1/3). Since P >= 2, one has 0 < u < P and u^3 = P. There are at most u positive integer primes p <= u. The missing-layer exchange theorem for the same full record gives layerTail(m,p) < 2/P for each such prime, so their sum is at most 2u/P = 2/u^2.")),
                Paragraph(Text("For every remaining repeated prime p > u, the valuation condition implies layerTail(m,p) <= (1/p)^3/(1-(1/p)^3) <= 2/p^3. The existing finite cubic-tail estimate bounds the sum of 1/p^3 over any finite set of positive integers above u by 2/u^2. Thus this second contribution is at most 4/u^2, including p = P without any missing-layer exchange at P. Adding the contributions gives 6/u^2 = 6/P^(2/3).")),
                Paragraph(Text("This repository derivation reuses the missing-layer exchange and finite cubic-tail estimates. It imposes no price-size restriction, prime-support shape, asymptotic threshold or prime-number theorem. It bounds exactly the repeated-prime contribution, not the entire Euler tail, and makes no RH assertion or claim of literature novelty."))),
            DescribeRole.Theorem))));
}
