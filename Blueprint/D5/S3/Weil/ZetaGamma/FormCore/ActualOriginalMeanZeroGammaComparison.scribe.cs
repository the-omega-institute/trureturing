using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualOriginalMeanZeroGammaComparisonDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualOriginalMeanZeroGammaComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual shifted Gamma energy difference is bounded below by minus "
            + "one half of the original physical excess for the same mean-zero H6 source.",
        H("Original Mean-Zero Gamma Comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-original-mean-zero-gamma-excess-comparison"),
                DeclarationHandle.Create(Owner + "actual_original_mean_zero_gamma_excess_comparison"),
                H("Actual Gamma comparison on the original source and its explicit form domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real c and original complex source F, assume "
                            + "originalPhysicalH6(F), the actual even arithmetic mean "
                            + "integral_r actualSuzukiEvenBProfile(F,r)=0, and the explicit "
                            + "originalGammaFormDomain(c,F). The conclusion first proves "
                            + "Integrable of (gammaWeight(xi)+c) times the squared norm of "
                            + "the unitary Fourier transform of t -> actualGammaProfile(F,abs(t)). "
                            + "It then gives -D(F)/2 <= E_c(F)-E_c,even(F)/2, where D(F) "
                            + "is integral_{x>pi} ((x/pi)^6-1)*norm(F(x))^2. Both energies "
                            + "are the literal integrals displayed in the Lean statement; "
                            + "the conclusion includes the even energy's genuine domain.")),
                    Paragraph(Text(
                        "Every profile and energy is built from this same original F. "
                            + "The actual Gamma profile uses the complete physical theta "
                            + "series and the original logarithmic change of variables. "
                            + "H6 supplies its L1 and L2 bounds, but does not by itself "
                            + "supply Gamma form-domain membership. The hGamma premise "
                            + "remains explicit for every real shift, including shifts "
                            + "whose weights may change sign. No trace-zero or finite-kernel "
                            + "premise is added to the public theorem.")),
                    Paragraph(Text(
                        "The complete Gamma identity retains the positive infinite tail "
                            + "sum_n [1+(3/2)/((n+1)*(n+7/2))] "
                            + "*normSq(L_{n+9/4}(actualGammaProfile(F))). Its coefficient "
                            + "and normSq factors prove every term nonnegative. The signed "
                            + "resonance -(6/5)*Re(conj(L_{5/4})*Lt_{5/4}) is retained. "
                            + "Here L and Lt are the actual half-line Laplace integral and "
                            + "its first moment. The finite norm-square coefficient is "
                            + "64/25+(6/5)*(Re(digamma(1))-log(2*pi)).")),
                    Paragraph(Text(
                        "The same-source mean-zero moment bounds control norm(L0)^2 "
                            + "by (3/1000)*pi^(7/2)*D(fullTheta(F)) and "
                            + "norm(L0)*norm(Lt) by (3/400)*pi^(7/2)*D(fullTheta(F)). "
                            + "The finite coefficient exceeds -49/100, giving debit "
                            + "1047/100000. The fullTheta excess is at most Z^2*D(F), "
                            + "where Z=sum_{n>=0}(n+1)^(-3)<=11/9. The resulting "
                            + "(1047/100000)*pi^3*Z^2 is less than 1/2. This pays the "
                            + "finite debit by the original D(F), while the whole positive "
                            + "tail is discarded only through its proved nonnegativity.")),
                    Paragraph(Text(
                        "The estimate applies to the stated original mean-zero source "
                            + "and its explicit Gamma form domain. The remaining full-energy "
                            + "positivity and global number-theoretic conclusions require "
                            + "additional arguments."))),
                DescribeRole.Theorem))));
}
