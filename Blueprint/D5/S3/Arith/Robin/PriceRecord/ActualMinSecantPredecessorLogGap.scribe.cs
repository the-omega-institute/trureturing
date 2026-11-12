using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualMinSecantPredecessorLogGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform logarithmic gap bound for every minimizing predecessor of an arbitrary original positive-price full record.",
        H("Actual minimum-secant predecessor gaps"),
        Blocks(
            Paragraph(Text("Put ell(n)=log(sigma(n)/n), F_t(n)=goldenResourceObjective(t,n)=ell(n)-t log(n) for positive integers n, and P=largestPrime(m). A strict record means F_mu(n)<F_mu(m) for EVERY positive n<m. The minimizing secant is taken over ALL positive predecessors; no tie choice, q>1 restriction, global-optimality hypothesis or divisibility premise is imposed.")),
            Paragraph(Text("The proof first obtains a supporting price nu, a tie F_nu(q)=F_nu(m), and support on the full prefix through m. If log(m/q)<log(P) the bound is immediate. Otherwise every prime p dividing m is affordable for insertion into q. For an excess valuation, actual insertion and deletion, together with strict layer decrease, force v_p(m)=v_p(q)+1 and marginal(p,v_p(m))=nu. At a fixed positive layer the actual marginal strictly decreases with the prime, so excess primes have distinct occupied valuations. This is not a pairwise irrationality assertion.")),
            Paragraph(Text("The original-record prime-power envelope bounds j log(p) by B=log(4P^2), and j by N=floor(B/log(2)). Summing over the excess primes gives log(m/q)<=B H_N, with the smaller-gap branch retained as max(log(P),B H_N). The live harmonic estimate converts this to 32 log(P) log(log(P)) for P>=exp(4). This new finite affordable-insertion and harmonic estimate supplies the endpoint content; the public support and occupied-price helpers are consumed proof components.")),
            Paragraph(Text("The ordinary source arguments are fallible inputs. Their support geometry is part of the mature superabundant and colossally-abundant support geometry of Erdos--Nicolas, Repartition des nombres superabondants (1975), pp. 69--71. No novelty or formal six-exponentials supplier is claimed. These logarithmic ratios are not identified with the original denominator h. The full bank, prescribed b/delta, every fee, Robin/5040 and RH remain open.")),
            Paragraph(Text("The retained Reg mirror checks full-source laws and definitional equivalence for all three public targets. Compiler occurrence/source binding, dependent realization, intervention, variation, sensitivity and observational dependence are unfinished under issue 29429; these are not declared_validated four-slot registrations.")),
            Describe.Lean(
                DescribeId.Create("actualminsecantpredecessorloggap-secant-support"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualMinSecantPredecessorLogGap.secant_support"),
                H("Supporting price on the full original prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural m,q with 0<q<m, arbitrary real mu, the full strict record and the complete minimum-secant condition imply mu<nu, equality at q and m, and F_nu(r)<=F_nu(m) for every 0<r<=m. This helper has no mu>0 assumption. finite_log_gap and the nearby chain consume it.")),
                    Paragraph(Text("Exact full statement: theorem secant_support {m q : ℕ} (hq : 0 < q) (hqm : q < m) {mu : ℝ} (hrecord : ∀ n : ℕ, 0 < n → n < m → goldenResourceObjective mu n < goldenResourceObjective mu m) (hmin : ∀ r : ℕ, 0 < r → r < m → (goldenResourceObjective 0 m - goldenResourceObjective 0 q) / Real.log ((m : ℝ) / q) ≤ (goldenResourceObjective 0 m - goldenResourceObjective 0 r) / Real.log ((m : ℝ) / r)) : let nu := (goldenResourceObjective 0 m - goldenResourceObjective 0 q) / Real.log ((m : ℝ) / q); mu < nu ∧ goldenResourceObjective nu q = goldenResourceObjective nu m ∧ ∀ r : ℕ, 0 < r → r ≤ m → goldenResourceObjective nu r ≤ goldenResourceObjective nu m"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualminsecantpredecessorloggap-occupied-top-price"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualMinSecantPredecessorLogGap.occupied_top_price"),
                H("Actual occupied-layer deletion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For m>0, prime p, arbitrary real nu, support over every 0<r<=m and v_p(m)>=1 imply nu<=goldenLayerMarginal(p,v_p(m)). Equality is allowed. Deleting p gives an actual positive integer m/p; affordable_excess and the nearby occupied_price consumer use this helper.")),
                    Paragraph(Text("Exact full statement: theorem occupied_top_price {m p : ℕ} (hm : 0 < m) (hp : p.Prime) {nu : ℝ} (hmax : ∀ r : ℕ, 0 < r → r ≤ m → goldenResourceObjective nu r ≤ goldenResourceObjective nu m) (ha : 1 ≤ m.factorization p) : nu ≤ goldenLayerMarginal p (m.factorization p)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualminsecantpredecessorloggap-actual-min-secant-predecessor-eventual-log-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualMinSecantPredecessorLogGap.actual_min_secant_predecessor_eventual_log_gap"),
                H("Uniform bound for every minimizing predecessor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exist absolute positive C,T BEFORE every natural m>=2, every original mu>0 and its full strict record, and every positive q<m minimizing the literal ell-secants. Whenever P>=T, 0<log(m/q)<=C log(P) log(log(P)). The proof supplies C=32 and T=exp(4). q=1 and every tied minimizer remain in the domain.")),
                    Paragraph(Text("Exact full statement: theorem actual_min_secant_predecessor_eventual_log_gap : ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → (∀ n : ℕ, 0 < n → n < m → goldenResourceObjective mu n < goldenResourceObjective mu m) → ∀ q : ℕ, 0 < q → q < m → (∀ r : ℕ, 0 < r → r < m → (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) - Real.log ((ArithmeticFunction.sigma 1 q : ℝ) / q)) / Real.log ((m : ℝ) / q) ≤ (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) - Real.log ((ArithmeticFunction.sigma 1 r : ℝ) / r)) / Real.log ((m : ℝ) / r)) → T ≤ (largestPrime m : ℝ) → 0 < Real.log ((m : ℝ) / q) ∧ Real.log ((m : ℝ) / q) ≤ C * Real.log (largestPrime m : ℝ) * Real.log (Real.log (largestPrime m : ℝ))"))),
                DescribeRole.Theorem)
        )));
}
