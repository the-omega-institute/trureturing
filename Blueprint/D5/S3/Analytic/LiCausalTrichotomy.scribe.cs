using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LiCausalTrichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/LiCausalTrichotomy",
            "The Li symbol is causal exactly at integral index, equivalently when Cayley monodromy vanishes."),
        H("The Li-Test Causal Trichotomy"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("causality-integrality-and-monodromy-are-equivalent"),
                H("Causality, integrality, and monodromy are equivalent"),
                LeanTheorem(
                    "D5/S3/Analytic/LiCausalTrichotomy.causal_iff_integer_iff_monodromy"),
                Disp(Seq(Kappa, Ge, Sp, D(0), Colon, Quad, Sp, Operatorname, Grp(F.Id("CausalRealization")), Open, Kappa, Close, Leftrightarrow, Sp, Kappa, InMacro, Mathbb, Grp(F.Id("N")), Leftrightarrow, Sp, F.Id("e"), Caret, Grp(D(2), Pi, Sp, F.Id("i"), Kappa), Eq, D(1), Comma, Qquad, Sp, Delta, Underscore, D(0), Left, Open, F.Id("z"), Caret, Kappa, Minus, D(1), Right, Close, Eq, D(2), F.Id("i"), Sin, Open, Pi, Kappa, Close, Comma, Qquad, Sp, Ell, Underscore, Kappa, Open, F.Id("u"), Close, Sim, Frac, Grp(Sin, Open, Pi, Kappa, Close), Grp(Pi, Sp, F.Id("u")), Esc, Esc, Open, F.Id("u"), To, Pm, Infty, Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Use the angular Fourier convention F(f)(gamma) = integral f(u) exp(i gamma u) du, obtained by reflecting the repository's canonical negative-sign kernel. For every nonnegative real kappa, an integrable inverse supported almost everywhere in u < 0 exists exactly when kappa is a natural number, and this is equivalent to exp(2 pi i kappa) = 1. At n = 0 both the symbol and packet are zero. For n >= 1 the inverse is exactly -1_{u<0} exp(u/2) L_{n-1}^{(1)}(-u), where L_m^{(1)} is the explicit standard finite sum, and its transform is z(gamma)^n - 1 for z(gamma) = (gamma + i/2)/(gamma - i/2).")),
                    Paragraph(Text(
                        "At the Cayley branch cut, the right and left principal-log limits are exp(pi i kappa) - 1 and exp(-pi i kappa) - 1, so their difference is 2 i sin(pi kappa). For nonintegral kappa this jump is nonzero, while every L1 Fourier transform is continuous; therefore no causal L1 realization exists. The bounded scaled symbol nevertheless defines a tempered distribution, and inverse Fourier transform gives its canonical generalized inverse. Off zero, integration by parts separates the jump from the L1 transform of the symbol derivative. Riemann-Lebesgue then makes the remainder vanish and yields equivalence to sin(pi kappa)/(pi u) at both positive and negative infinity, hence eventual nonvanishing on both sides.")),
                    Paragraph(Text(
                        "The finite Laguerre transform is computed term by term from complex Laplace moments and the binomial theorem. The result is analytic only: it asserts neither Li positivity nor the Riemann hypothesis, zero statistics, numerical certification, or physical causality.")))
            ))));
}
