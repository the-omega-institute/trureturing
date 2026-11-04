using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail;

internal sealed class SharpCausalDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted decay of the actual centered causal kernel.",
        H("Weighted decay of the actual centered causal kernel"),
        Blocks(
            Paragraph(Text("The arithmetic suppliers preserve the Terence Tao / Apache-2.0 attribution at LogConvolutionMassExpansion. Harmonic, Stirling, Abel and integral APIs are reused from pinned Mathlib. These are repository deductions, with no literature novelty claim. The literal factorial G is distinct from prime-weighted primitives in other RH routes.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-r-centered-decay"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_decay"),
                H("The actual kernel after subtracting its leading exponential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t>=0, abs(r(t)-ell*exp(-t/2))<=(4*gamma+24)*(1+t)*exp(-3*t/2). The function r is the existing causal kernel, equal to exp(-t/2)*G(exp(t)) on t>=0 and zero otherwise. This estimate consumes the arithmetic sharp-tail theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-factorial-sharp-r-centered-weighted-integrable"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay.r_centered_weighted_integrable"),
                H("Weighted L1 for every real exponent below 3/2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each real a<3/2, the function t -> exp(a*t)*(r(t)-ell*exp(-t/2)) is IntegrableOn (Ioi 0). The proof uses the actual centered estimate and integrable exponential moments. This statement does not establish complex analytic continuation, Fourier-symbol positivity, a zero-free region, RH, or the sufficient sublinear moment target."))),
                DescribeRole.Theorem))));
}
