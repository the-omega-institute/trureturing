using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail;

internal sealed class SharpFactorialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factorial remainder uniform in floor phase.",
        H("A factorial remainder uniform in floor phase"),
        Blocks(
            Paragraph(Text("The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-log-factorial-remainder"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.log_factorial_remainder"),
                H("A quantitative logarithmic Stirling remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive natural n, the difference between log(n!) and n*log(n)-n+log(n)/2+log(2*pi)/2 is between zero and 1/(12*n). The upper estimate is supplied by the reusable Grid logarithmic factorial envelope, whose proof telescopes Mathlib's Robbins step to its certified Stirling limit; the lower estimate is the public logarithmic Stirling inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-eta-phase-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Factorial.eta_phase_bound"),
                H("The literal factorial error at every real cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, abs(eta(x)-((1/2-fract(x))*log(x)+log(2*pi)/2))<=4/x. Here eta is the existing literal factorial residual. This estimate includes x=1, all integer cutoffs, and every point inside each floor cell."))),
                DescribeRole.Theorem))));
}
