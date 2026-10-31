using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RhPointwiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete integrated formula recovers the actual pointwise Chebyshev error under RH.",
        H("Pointwise recovery through shrinking physical windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chebyshev-error-little-o-three-quarters"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RhPointwise.chebyshev_error_isLittleO_rpow_three_quarters"),
                H("The actual error is little o of the three-quarter power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume Mathlib's literal RiemannHypothesis. For every positive epsilon, all sufficiently large real x satisfy abs(Chebyshev.psi(x)-x) <= epsilon*x^(3/4). The function is the inclusive actual Mangoldt sum; all integer and prime-power endpoints are included.")),
                    Paragraph(Text("The existing complete occurrence equivalence retains both imaginary signs and every analytic multiplicity. RH locates these actual zeros on the critical line. The existing absolutely summable actualCoeff series then writes exp(-y/2)*actualH(y) as a uniform sum of bounded trigonometric terms. Mathlib's uniform-limit theorem supplies uniform continuity, and the coefficient norm sum supplies a global bound.")),
                    Paragraph(Text("WeightedPrimeLimit.chebyshev_error_kernel_integrable supplies absolute tail integrability independently of this conclusion. CompleteChebyshevTailIdentity and WholeFormula give the exact sign: sqrt(x)*Q(x)+Re(h(log(x)))=(trivialT(log(x))-log(2*pi))/sqrt(x). The existing nonnegative bounded trivial-zero correction makes the right side tend to zero. No zero term or constant term is discarded.")),
                    Paragraph(Text("For each fixed c>0, put Delta=c*x^(3/4). Monotonicity on the right physical window bounds e(x) above by Delta+(x+Delta)^2*abs(Q(x)-Q(x+Delta))/Delta. The left window bounds -e(x) by Delta+x^2*abs(Q(x-Delta)-Q(x))/Delta. These are integral comparisons of the actual error kernel, valid across jumps. Uniform continuity is applied between moving logarithmic endpoints whose difference tends to zero; boundedness pays the change of square-root scale.")),
                    Paragraph(Text("Both tail differences multiplied by sqrt(x) tend to zero. After division by x^(3/4), the window inequalities give both signs at most c plus a term tending to zero. Choose c=epsilon/2 and then a common threshold. This is the new monotone local-average estimate; the normalized series identity and the algebraic Q=-U/x identity are reused normalization steps, not independent new mathematical content.")),
                    Paragraph(Text("This conditional estimate supplies a pointwise input for the continuing Robin debit programme. It proves neither RH, an actual record asymptotic, Ramanujan sharpness nor asymptotic attainment. No external open-problem-resolution claim is made. External stronger pointwise results are not asserted to be compatible compiled dependencies of this module."))),
                DescribeRole.Theorem))));
}
