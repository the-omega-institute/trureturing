using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CollectivePrimeInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/CollectivePrimeInsertion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collective insertion barriers at the original Robin minimum.",
        H("Collective prime insertion"),
        Blocks(
            Paragraph(Text("For L>1 and an integer k>=1, define B(L,k,x)=L+k log x-L^((1+1/x)^k). Its root is above L and is unique on the full real domain x>1. The barrier is negative below its root and positive above it. For k=1 the formula is the existing insertionBarrier, with no change to its endpoint convention.")),
            Describe.Lean(
                DescribeId.Create("collective-insertion-root-exists-unique"),
                DeclarationHandle.Create(Prefix + "collective_insertion_root_exists_unique"),
                H("Unique all-k nonlinear root and exact signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real L>1 and every natural k>=1 there exists beta>L with B(L,k,beta)=0. Every zero at x>1 equals beta; for every x>1, B(L,k,x)<0 if and only if x<beta, and 0<B(L,k,x) if and only if beta<x. Bernoulli's inequality and the strict exponential tangent give the negative value at L. A positive value occurs at exp(L^(2^k)); continuity and strict monotonicity give existence and the full sign characterization. This is a necessary-comparison construction and asserts no Robin or Riemann-hypothesis conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collective-insertion-strict-root-order"),
                DeclarationHandle.Create(Prefix + "collective_insertion_roots_strict_order"),
                H("Strict ordering in the number of insertions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let L>1 and k>=1. If beta>L is a zero of B(L,k,.) and gamma>L is a zero of B(L,k+1,.), then beta<gamma. The strict concavity of u mapsto log(log u) on u>1 makes its secant slope based at L strictly decrease between L+k log beta and L+(k+1) log beta. The k-root equality therefore makes the next barrier strictly negative at beta; strict monotonicity places its zero to the right."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-minimum-finite-fresh-insertion"),
                DeclarationHandle.Create(Prefix + "minimum_finite_fresh_insertion"),
                H("Actual finite insertion at the original minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume N>5040, log N>1 and robinLogMargin N<=robinLogMargin m for every integer m>5040. For any finite set S of prime numbers not dividing N, put L=log N, s=sum over S of log p, and P=product over S of (1+1/p). Then L^P<=L+s. This includes the empty set. The compared integer is exactly M=N times the product of S. Distinctness ensures that each next inserted prime remains absent from the intermediate integer. The existing first-layer W increment telescopes to W(M)-W(N)=sum over S of log(1+1/p), while log M=L+s and M>5040. The original minimum comparison gives the inequality after two order-preserving logarithmic transports. No other integer is assumed to minimize the margin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fresh-distinct-prime-mean-strict-root"),
                DeclarationHandle.Create(Prefix + "fresh_tuple_mean_gt_root"),
                H("Strict geometric-mean restriction for distinct primes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same original-minimum hypotheses, let S be a finite set of at least two fresh primes and beta>log N a zero of B(log N,card S,.). Then exp((sum over S of log p)/(card S))>beta. The function t mapsto log(1+exp(-t)) is strictly convex: its derivative is -1/(1+exp t), a strictly increasing function. The logarithms of two distinct positive primes differ. Strict Jensen with equal positive weights gives a strict lower comparison for the tuple payoff at its geometric mean. The actual finite insertion inequality then makes B strictly positive at that mean. The singleton case uses no strict Jensen step and retains its weak endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fresh-prime-right-closed-cutoff-cardinality"),
                DeclarationHandle.Create(Prefix + "fresh_prime_closed_cutoff_card_lt"),
                H("Fewer than k primes in the right-closed interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In addition assume z>=0 and the exact support identity N.primeFactors=primesLE(floorNat z). For k>=2 and a root beta>log N of B(log N,k,.), fewer than k actual prime numbers lie in (z,beta]. The finite set is (primesLE(floorNat beta)).filter(p mapsto z<p); the upper endpoint is inclusive. If it had at least k elements, a k-element subset would consist of distinct fresh primes all at most beta. Its geometric mean would be at most beta, contradicting the strict mean restriction. This argument does not exclude a prime equal to the singleton root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-original-failure-collective-prime-restrictions"),
                DeclarationHandle.Create(Prefix + "failure_has_collective_prime_restrictions"),
                H("The sole original failure retains the whole bundle and adds collective restrictions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sole premise is an integer n>5040 with robinLogMargin(n)<=0, including equality. The conclusion retains the SAME N and z from failure_has_nonlinear_prime_gap: N>55440, nonpositive original margin, attained global minimum over all m>5040, positive own price below boundaryPrice, golden-resource optimality, strict fixed-price advantage over every other positive integer, both strictInteger and maximalInteger identities, absence of all prime/layer activation ties, z>11, 0<log N-z<1/2, the first-layer price equation and its uniqueness on all real t>1, and the exact inclusive prime-support identity. It retains alpha,beta and every component of NonlinearPrimeGap, including full-domain uniqueness and the all-prime weak endpoint implication.")),
                    Paragraph(Text("At these same N,z, CollectivePrimeRestrictions supplies a function b of the natural number k. Its value b(1) equals the existing beta. For every k>=1, b(k)>log N is the unique zero on x>1 with exact negative and positive sign equivalences. Also b(k)<b(k+1). Every finite set of actual distinct fresh primes satisfies the literal power insertion comparison. Every such set of at least two members has geometric mean strictly greater than b(card S). For each k>=2, fewer than k actual primes lie in (z,b(k)]. The original open singleton endpoint is preserved by b(1)=beta.")),
                    Paragraph(Text("The proof uses the original Robin margin and the same attained minimum throughout. It supplies necessary arithmetic restrictions; it supplies no opposite lower bound for the complete signed Chebyshev tail, no annihilation hypothesis for a moment kernel, and no Robin or Riemann-hypothesis conclusion. No literature-priority claim is made."))),
                DescribeRole.Theorem))));
}
