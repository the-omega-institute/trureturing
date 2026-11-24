using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootSieveThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/SieveThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform parameters for the signed character sieve",
        H("Uniform parameters for the signed character sieve"), Blocks(
            Describe.Lean(DescribeId.Create("margin-mono"),
                DeclarationHandle.Create(
                    Prefix + "margin_mono"),
                H("Propagation of a strict logarithmic margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "If exp(2) ≤ x ≤ y and 2+3A log(x) < sqrt(x), then the same strict "
                    + "margin holds at y. No sign condition on A is required. For nonnegative A "
                    + "one applies the antitonicity of log(x)/sqrt(x); negative A gives the "
                    + "conclusion directly from sqrt(y)>2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-two-le"),
                DeclarationHandle.Create(
                    Prefix + "exp_two_le"),
                H("A reusable exponential threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Whenever 7.4 ≤ x, exp(2) ≤ x. The numerical bound is the existing "
                    + "ThetaIntegrated99.exp_two_le theorem; transitivity transfers it to x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("split-support"),
                DeclarationHandle.Create(
                    Prefix + "split_support"),
                H("Splitting a prime support at an arbitrary rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For x>1 with r+s distinct prime factors in x-1, there are a nonzero divisor "
                    + "e of x-1 and a finite set T. Each prime divisor of x-1 divides e or lies "
                    + "in T. The support of e has r factors, T has s factors, and the sieve set "
                    + "is exactly T. The witnesses are normalized: e is the product of the "
                    + "first r ordered prime factors and T is the image of the last s factors. "
                    + "Its margin "
                    + "is one minus the reciprocal sum of the last s ordered prime factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-margin"),
                DeclarationHandle.Create(
                    Prefix + "signed_margin"),
                H("Converting a scalar margin to the signed sieve inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Assume x≥1, d>0, K≤dA and 2+3A log(x)<sqrt(x). Then "
                    + "K times (3/2)sqrt(x)log(x) is strictly less than d times (x/2-sqrt(x)). "
                    + "The nonnegative logarithmic error term preserves the coefficient bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coarse-sieve-feasible"),
                DeclarationHandle.Create(
                    Prefix + "Feasible"),
                H("Feasibility of the coarse signed sieve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Feasibility means that there are a nonzero parameter e and a finite "
                    + "set T covering every prime factor of x-1 absent from e, with a "
                    + "positive sieve margin. Writing U=sievePrimes(x,e,T), the signed error "
                    + "coefficient at gcd(e,x-1) times (3/2) sqrt(x) log(x) must be strictly "
                    + "less than delta(U) times (x/2-sqrt(x)). This is an arithmetic "
                    + "condition for arbitrary natural x."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("covering-parameters"),
                DeclarationHandle.Create(Prefix + "covering_parameters"),
                H("A covering construction independent of the analytic main term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every x>1, numerical margin rules for supports with at most seven " +
                    "factors and for supports with eight or more factors supply covering " +
                    "parameters for arbitrary real error M and main term N. The latter rule " +
                    "retains delta≥610847/1616615 and the exact coefficient " +
                    "delta(2^(m+2)−1)+(5+delta)2^(m+2), with " +
                    "9699690 times 16^m at most x. The original coarse threshold and the " +
                    "unconditional linear principal term consume this same construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-sieve-tail"),
                DeclarationHandle.Create(
                    Prefix + "feasible_of_ge_4100000"),
                H("Uniform feasibility above 4100000"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every natural integer x at least 4100000 is feasible. No primality or "
                    + "GRH hypothesis occurs. With at most two distinct prime factors the "
                    + "sieve set is empty; with three through seven factors the prefix "
                    + "consists of the smallest two; above seven the largest six form the "
                    + "sieve set. The geometric radical lower bound and logarithmic "
                    + "monotonicity preserve strict positive margins for arbitrarily many "
                    + "factors. The companion theorem SieveThresholdExact.feasible_iff "
                    + "supplies the complete arithmetic classification from 3483481 onward: "
                    + "precisely 3483481 and 3573571 are infeasible. The number 4100000 "
                    + "is the start of this uniform tail argument."))),
                DescribeRole.Theorem))));
}
