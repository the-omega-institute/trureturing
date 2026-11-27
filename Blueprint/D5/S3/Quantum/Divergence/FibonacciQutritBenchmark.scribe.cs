using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FibonacciQutritBenchmarkDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The attained classical benchmark forces strict improvement of a full-rank Fibonacci qutrit contender.",
        H("Fibonacci qutrit benchmark comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("classical-benchmark-attained"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/FibonacciQutritBenchmark.classical_benchmark_attained"),
                H("Classical preparation attaining the benchmark"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
                Blocks(Paragraph(Text(
                    "The classes with likelihood ratios 4/3 and 5/3 share the first coordinate "
                    + "ray. The 7/3 class and the null class occupy the second and third rays, "
                    + "respectively. The output reference is positive definite for positive "
                    + "weights. Taking the trace of the diagonal log difference gives "
                    + "(4a/3 + 5b/3) log((4a/3 + 5b/3)/(a+b)) + (7c/3) log(7/3)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-rank-benchmark-comparison"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/FibonacciQutritBenchmark.full_rank_benchmark_comparison"),
                H("Benchmark loss bound and strict improvement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
                Blocks(
                    Paragraph(Text(
                        "On the three positive classes use diagonal input states with probability "
                        + "laws p = (4a/3, 5b/3, 7c/3) and q = (a,b,c)/s, where s = a+b+c. The "
                        + "finite preparation channel sends them to A and C/s. Positive definiteness "
                        + "of the two references permits the finite trace-log branch of channel "
                        + "data processing. The same normalization term appears on each side "
                        + "because the comparison has trace one.")),
                    Paragraph(Text(
                        "The loss from merging the first two positive classes is bounded above "
                        + "by b times ((5/3) log(5/4) − 1/3), using the tangent inequality for "
                        + "x log x. Apply the scalar logarithm series upper bound at 1/9 to obtain "
                        + "log(5/4) ≤ 9/40. Together with b ≤ e/2 ≤ 4/19 this gives the cap 1/114.")),
                    Paragraph(Text(
                        "At or above the benchmark the null-class log loss is at most 1/114. "
                        + "Strict spectral transport then gives a common linear transformation of "
                        + "the original three positive outputs and a trace-one null preparation "
                        + "on the freed ray. The original class weights give a rank-at-most-two "
                        + "positive reference and a strictly greater trace-log divergence."))),
                DescribeRole.Theorem))));
}
