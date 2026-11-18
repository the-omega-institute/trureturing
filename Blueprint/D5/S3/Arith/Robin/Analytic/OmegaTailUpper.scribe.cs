using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class OmegaTailUpperDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/lucapomerancesole2025robin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The upper tail of the number of distinct prime factors has an optimized Rankin exponent and a vanishing exponent at its second-order endpoint.",
        H("Distinct-prime tail upper bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scale"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale"),
                H("Logarithmic scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scale y(x) is log(x)/log(log(x)). It is positive and tends to infinity for sufficiently large positive x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.threshold"),
                H("Second-order threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The threshold T(lambda,x) equals y(x)+lambda*y(x)/log(log(x)). The parameter lambda is fixed before x tends to infinity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("count"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount"),
                H("Counting distinct-prime tails"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The finite count includes exactly the positive natural numbers n not exceeding the real cutoff x whose number of distinct prime divisors exceeds T(lambda,x). The statistic is cardDistinctFactors, rather than the number of prime factors with multiplicity. The cited correction uses the distinct-prime tail at lambda=0 as a necessary condition on Robin exceptions. The second-order threshold and estimates here are repository-derived; the source is not claimed to prove them."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimizer"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a"),
                H("Optimizing root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s>1, a(s)=s*sin(pi/s)/pi is positive. The optimizing Rankin parameter is c=a(s)^s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rate"),
                H("Optimized rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rate F(lambda,s) is s*(1-lambda-log(a(s))). It arises from I(s,c)-log(c)-s*lambda, where I(s,c)=pi*c^(1/s)/sin(pi/s), upon setting c=a(s)^s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reuse-scale-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_pos"),
                H("Positive scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If x>exp(1), then scale(x)>0. This positivity is used to transfer normalized inequalities back to counting and logarithmic product costs."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reuse-scale-tendsto"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.scale_tendsto"),
                H("Growing scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The logarithmic counting scale tends to positive infinity as x tends to positive infinity. It is reused for exact bin cardinalities and entropy asymptotics."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reuse-a-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.a_pos"),
                H("Positive optimizing root"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, a(s)>0. The density normalization and the minimum-rate argument use this same optimizing root."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reuse-power-kernel-integral"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.power_kernel_integral"),
                H("Power kernel integral"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s>1 and c>0, the function s*c/(u^s+c) is integrable on u>0 and its integral is pi*c^(1/s)/sin(pi/s). This evaluates the mass of the lower-bound density."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reuse-log-weight"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight"),
                H("Logarithmic weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The logarithmic weight at s,z,t is log(1+z/t^s)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reuse-abel-kernel"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.abelKernel"),
                H("Abel kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Abel kernel at s,z,t is s*z/(t*(t^s+z))."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reuse-log-weight-deriv"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.logWeight_deriv"),
                H("Logarithmic weight derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For z>0 and t>0, the logarithmic weight has derivative minus the Abel kernel. The entropy integral uses this derivative with its endpoint limits."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rankin-exponential-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.rankin_exponential_bound"),
                H("Finite Rankin exponential bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s>1, z>=1 and x>0, the count of integers 1<=n<=x whose number of distinct prime divisors strictly exceeds any real T is at most exp(s*log(x)-T*log(z)+log(1+sum over natural n of n^(-s))+sum over primes p<=x of log(1+z*p^(-s))). Every displayed cost and the entire finite prime sum lie inside the exponential. The same finite formula supports parameters depending on x when its hypotheses are verified at each x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abel-kernel-continuous"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.abelKernel_continuousOn"),
                H("Continuity of the Abel kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For z>0 and a>0, the Abel kernel is continuous on every closed real interval [a,b], for every real s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.upper_bound"),
                H("Rankin upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every fixed real lambda<=1, s>1 and epsilon>0, eventually N(lambda,x)<=exp((F(lambda,s)+epsilon)*y(x)). No parameter s depending on x is used.")),
                    Paragraph(Text("The finite-support Euler expansion bounds the weighted integer sum by a product over primes at most x. The inverse unweighted factors are bounded by a convergent positive Dirichlet series. At z=c*log(x)^s, the logarithmic prefactor divided by y(x) tends to -log(c)-s*lambda.")),
                    Paragraph(Text("For each fixed alpha in (0,1), primes up to log(x)^alpha contribute o(y(x)). Above that cutoff, the prime number theorem gives a uniform linear bound for prime counting. Abel summation compares the remaining weighted sum with the positive integral of s*c/(u^s+c). A power substitution and the existing Beta normalizer evaluate that integral exactly. Choosing alpha sufficiently close to one preserves the stated coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.result"),
                H("Vanishing exponent at the endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At lambda=1, log(1+N(1,x))/y(x) tends to zero. The quotient is eventually nonnegative. For fixed s at least pi, the cubic sine bound and an elementary logarithm inequality give 0<=F(1,s)<=pi^2/(3*s). First apply the upper bound with this fixed s, then choose s sufficiently large. The additive log(2)/y(x) tends to zero. This is an unconditional counting statement and does not decide any pointwise Robin inequality. The matching lower bound at lambda=0 is proved separately in OmegaTail.Asymptotic."))),
                DescribeRole.Theorem))));
}
