using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedLayerRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ratios of fixed prime layers of actual positive-price predecessor records converge uniformly to their layer index.",
        H("Fixed-Layer Rigidity of Actual Price Records"),
        Blocks(Describe.Lean(
            DescribeId.Create("price-record-fixed-layer-rigidity"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity.price_record_fixed_layer_rigidity"),
            H("Uniform fixed-layer ratio"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a natural number j>=2 and a real epsilon>0. There is a real T>0, "
                        + "depending only on j and epsilon, such that every natural m>=2 and "
                        + "every real lambda>0 satisfying the full predecessor record "
                        + "for every positive natural n<m, F_lambda(n)<F_lambda(m), obey "
                        + "that the ratio P_j^j/P tends to j uniformly: once T<=P, where "
                        + "P=largestPrime(m), "
                        + "the absolute difference between P_j^j/P and j is less than epsilon. "
                        + "Here F_lambda(n)=log(sigma(n)/n)-lambda*log(n) on the stated "
                        + "positive-natural domain.")),
                Paragraph(Text(
                    "The fixed-layer quantity P_j is the maximum of 1 and the supremum of "
                        + "the prime factors p of m whose valuation in m is at least j. "
                        + "Thus P_j=1 when that set is empty. The threshold is uniform over "
                        + "all positive prices and all actual predecessor records in the "
                        + "record class. No colossal-abundance or global optimizer premise, "
                        + "price-localization premise, occupied next-layer cutoff, or "
                        + "uniform-in-j error rate is assumed.")),
                Paragraph(Text(
                    "The proof uses a fixed-layer composition rather than an application of a "
                        + "strict-inventory theorem. Prime number theorem "
                        + "limits for Chebyshev theta supply any fixed finite number of primes "
                        + "in a relative window. For every prime p and integer a>=1, "
                        + "gain(p,a)=goldenLayerMarginal(p,a)*log(p) satisfies the two-sided "
                        + "marginal bounds (1-1/p)/p^a <= gain(p,a) <= 1/p^a.")),
                Paragraph(Text(
                    "The exchange step chooses disjoint finite squarefree donor and insertion "
                        + "sets D and U, with every donor in D a prime divisor of m and every "
                        + "insertion in U prime, and forms n=(m/product over D)*product over U. "
                        + "The divisor condition makes the quotient integral, while the product "
                        + "inequality makes n a positive natural number strictly below "
                        + "m. Exact factorization identities give the objective difference, "
                        + "including the signed price term lambda*(log(product D)-log(product U)). "
                        + "The full predecessor record pays the complete block exchange once, "
                        + "so the local gains are summed before the contradiction is taken.")),
                Paragraph(Text(
                    "For the lower barrier, take r large occupied primes near P as donors and "
                        + "s=j*r-1 primes in a fixed relative window "
                        + "(A*P^(1/j),B*P^(1/j)] for insertions. Under the lower-barrier "
                        + "violation this window lies above P_j. For the upper barrier, "
                        + "remove s=j*r+1 primes below P_j and insert r new primes above P. "
                        + "The choices of the finite windows leave strictly positive gain "
                        + "margins. After the product comparison, the relevant window powers "
                        + "carry the negative exponent P^(-1/j), so their ratios vanish at the "
                        + "common cutoff. Raising the resulting lower and upper windows to the "
                        + "jth power yields the two-sided ratio estimate.")),
                Paragraph(Text(
                    "The actual-record interface is supplied by "
                        + "ActualPriceRecordPrimeStructure.price_record_prime_structure: "
                        + "antitone valuations and initial prime support are derived from the "
                        + "same full predecessor record, rather than added as hypotheses. "
                        + "All private lower and upper supplier propositions are discharged "
                        + "on the live public proof path by these structure facts and the "
                        + "finite exchange argument.")),
                Paragraph(Text(
                    "If a family of actual records has P=largestPrime(m) tending to infinity "
                        + "and is eventually beyond the thresholds for adjacent fixed indices "
                        + "j and j+1, applying the theorem at both indices gives the derived "
                        + "relation P_(j+1)^(j+1)/P_j^j -> (j+1)/j along that family. "
                        + "This is only a consequence of combining two fixed-index statements; "
                        + "it is not an additional claim of the fixed-layer theorem.")),
                Paragraph(Text(
                    "Fixed-layer rigidity alone does not prove a full Euler-tail asymptotic, "
                        + "signed prime-error control, Robin's inequality for every n>5040, "
                        + "or the Riemann hypothesis. It is a repository derivation using "
                        + "classical prime-benefit exchanges and the prime number theorem, "
                        + "with no claim of literature novelty. The paper-only exponent "
                        + "envelope and leading Robin correction are not part of the Lean "
                        + "theorem claim."))),
            DescribeRole.Theorem))));
}
