using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualCriticalChainNearbyGlobalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform logarithmic proximity to a true least fixed-price optimizer over all positive integers, constructed from the same original strict record.",
        H("Nearby least global optimizers from actual critical chains"),
        Blocks(
            Paragraph(Text("Use F_t(n)=goldenResourceObjective(t,n) on positive integers and P=largestPrime(m). A node selects the SMALLEST minimum-secant predecessor using Nat.find. At its critical price the predecessor is the least tied optimizer on the node prefix. The explicit price-change inequality in support_step extends support and leastness to the ORIGINAL prefix through m. The finite descending chain terminates at 1 and preserves the original mu-record condition at every nonterminal node.")),
            Paragraph(Text("first_crossing chooses the first chain node with log(m/q)>=log(8P). The incoming gap stays below that budget, and the last edge obeys the actual minimum-secant bound. The existing full-record mass limit is made uniform over the subtype of ALL pairs (integer, original positive price). It bounds node primes and places the last edge in its uniform regime. Quantitative real-variable estimates choose the constants once before all records.")),
            Paragraph(Text("The resulting actual q has enough multiplicative budget for every prime through the first prime after largestPrime(q), using Bertrand. Larger primes are absent and their first-layer marginal decreases. budget_to_global derives the existing global layer-threshold criterion. Least prefix support rules out occupied zero-margin layers. budget_to_least_global proves that this SAME q has the strictInteger layer counts and then uses its divisibility leastness. Global maximality and tie leastness therefore hold over ALL positive integers, not only n<=m.")),
            Paragraph(Text("The conclusion simultaneously retains 1<r<m, t>mu, log(8P)<=log(m/r), and log(m/r)<=C log(P) log(log(P)), with C,T before every original m and mu. It supplies a nearby optimizer, not the original bank or its paid exchanges. The original denominator h is not identified with log(m/r). Full modes 2,3,4,5,6,8,9,12 in both directions, the removed-2 tail J2/h2, prescribed b/delta, every fee and Robin/5040/RH remain open.")),
            Paragraph(Text("The original source argument is fallible; Erdos--Nicolas (1975), pp. 69--71, supplies mature support-geometry context, with no novelty claim and no formal six-exponentials supplier.")),
            Describe.Lean(
                DescribeId.Create("actualcriticalchainnearbyglobal-actual-record-nearby-least-global-optimizer"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualCriticalChainNearbyGlobal.actual_record_nearby_least_global_optimizer"),
                H("Uniform nearby least global optimizer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Absolute positive C,T precede every natural m>=2, every original real mu>0 and its full strict positive-predecessor record. For P>=T there exist r,t with both logarithmic bounds, 1<r<m and mu<t. For EVERY positive natural n, F_t(n)<=F_t(r), and equality implies r<=n. No globality, theta-power, BHP or extra six-exponentials assumption is added.")),
                    Paragraph(Text("Exact full statement: theorem actual_record_nearby_least_global_optimizer : ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → (∀ n : ℕ, 0 < n → n < m → goldenResourceObjective mu n < goldenResourceObjective mu m) → T ≤ (largestPrime m : ℝ) → ∃ r : ℕ, ∃ t : ℝ, 1 < r ∧ r < m ∧ mu < t ∧ Real.log (8 * (largestPrime m : ℝ)) ≤ Real.log ((m : ℝ) / r) ∧ Real.log ((m : ℝ) / r) ≤ C * Real.log (largestPrime m : ℝ) * Real.log (Real.log (largestPrime m : ℝ)) ∧ (∀ n : ℕ, 0 < n → goldenResourceObjective t n ≤ goldenResourceObjective t r) ∧ (∀ n : ℕ, 0 < n → goldenResourceObjective t n = goldenResourceObjective t r → r ≤ n)"))),
                DescribeRole.Theorem)
        )));
}
