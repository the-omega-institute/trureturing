using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PrimePowerExceptionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered von Mangoldt function satisfies a quadratic relation outside a sparse set of proper prime powers.",
        H("Prime-power exceptions and logarithmic shifts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("von-mangoldt-sub-one-quadratic"),
                DeclarationHandle.Create(Prefix + "vonMangoldt_sub_one_quadratic"),
                H("The quadratic relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural m that is not a prime power other than a prime, Y=Lambda(m)-1 satisfies Y squared=(log m-2)Y+log m-1. At primes Lambda(m)=log m, and at numbers that are not prime powers Lambda(m)=0. These two values give the relation, including m=0 and m=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("proper-prime-power-count-le-sqrt"),
                DeclarationHandle.Create(Prefix + "proper_prime_power_count_le_sqrt"),
                H("Counting the exceptions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a nonnegative real constant C such that for every real x at least two, the number of natural m with 0<m<=x that are prime powers and are not primes is at most C times sqrt x. Each such m contributes at least log 2 to the sum of Lambda over nonprimes. This sum equals psi(x)-theta(x), which is bounded by a constant times sqrt x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-shift-bound"),
                DeclarationHandle.Create(Prefix + "log_shift_bound"),
                H("Replacing a shifted logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let N>0, H>=0, M>=0 and let n,d be natural numbers with N<=n and d<=MH. Then the absolute difference between log(n+d) and log n is at most MH/N. Monotonicity makes the difference nonnegative; the inequality log(n+d)<=log n+d/n bounds it by d/n, and the scale and shift bounds give the stated estimate."))),
                DescribeRole.Theorem))));
}
