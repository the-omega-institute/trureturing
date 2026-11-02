using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail;

internal sealed class SharpArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor-uniform arithmetic identities.",
        H("Floor-uniform arithmetic identities"),
        Blocks(
            Paragraph(Text("The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-j-tail-from-slope"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.J_tail_from_slope"),
                H("Exact logarithmic harmonic tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, 2*J(x)=log(x)^2-gamma^2+alpha+2*log(x)*epsilon(x)+2*T_epsilon(x). This is algebraically derived from Basic.compensation and is consumed by the literal G decomposition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-g-tail-decomposition"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.G_tail_decomposition"),
                H("Exact tail decomposition of the literal G"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, G(x)=alpha+(1+gamma)*fract(x)-eta(x)+x*(1+gamma+log(x))*epsilon(x)+2*x*T_epsilon(x). The proof consumes finite_smoothing and the public slope identity; it adds no arithmetic premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-harmonicprimitive-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Arithmetic.harmonicPrimitive_bound"),
                H("A bounded compensated harmonic primitive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, abs(x*epsilon(x)+fract(x)-1/2)<=4/x. The entire real floor phase is retained. The proof consumes the two-sided public harmonic remainder bracket in RobinRationalBasis and elementary logarithm inequalities."))),
                DescribeRole.Theorem))));
}
