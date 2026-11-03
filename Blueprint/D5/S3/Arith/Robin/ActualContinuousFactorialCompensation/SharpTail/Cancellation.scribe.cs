using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail;

internal sealed class SharpCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cancellation in the actual harmonic tail.",
        H("Cancellation in the actual harmonic tail"),
        Blocks(
            Paragraph(Text("The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-t-epsilon-quadratic-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Cancellation.T_epsilon_quadratic_bound"),
                H("A quadratic tail bound from genuine cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, abs(T_epsilon(x))<=8/x^2. Abel summation identifies the integral of (1/2-fract(t))/t^2 with -harmonicPrimitive(x)/x. The remaining density is bounded using abs(harmonicPrimitive(t))<=4/t. The estimate is for the original improper integral, with no assumed decay hypothesis."))),
                DescribeRole.Theorem))));
}
