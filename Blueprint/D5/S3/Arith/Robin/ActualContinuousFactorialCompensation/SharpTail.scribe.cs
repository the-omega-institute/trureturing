using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation;

internal sealed class SharpTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact limit of the literal factorial compensation.",
        H("The exact limit of the literal factorial compensation"),
        Blocks(
            Paragraph(Text("The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-g-centered-decomposition"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_centered_decomposition"),
                H("Cancellation of the nondecaying floor phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, G(x)-ell=(1+gamma+log(x))*harmonicPrimitive(x)-(eta(x)-((1/2-fract(x))*log(x)+L/2))+2*x*T_epsilon(x), where ell=alpha+h1/2, L=log(2*pi), and h1=1+gamma-L."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-g-sharp-tail-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.G_sharp_tail_bound"),
                H("A global real-uniform sharp error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x>=1, abs(G(x)-ell)<=(4*gamma+24)*(1+log(x))/x. The theorem concerns the literal factorial compensation G=Z_h-h1*floor(x)-alpha*(x-1), with alpha=gamma^2+2*ceta-2. No desired estimate or asymptotic is a premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-exists-g-sharp-tail-constant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.exists_G_sharp_tail_constant"),
                H("A positive global constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a real C>0 such that, for every real x>=1, abs(G(x)-(alpha+h1/2))<=C*(1+log(x))/x. The proof supplies C=4*gamma+24."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-tendsto-g-ell"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail.tendsto_G_ell"),
                H("The exact full-real limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("As real x tends to positive infinity, the literal G(x) tends to alpha+h1/2. This is the full real limit and retains the noninteger floor intervals. It is consumed by no claimed RH or Fourier positivity conclusion."))),
                DescribeRole.Theorem))));
}
