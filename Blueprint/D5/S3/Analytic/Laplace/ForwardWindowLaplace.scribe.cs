using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class ForwardWindowLaplaceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Laplace/ForwardWindowLaplace.";

    private static DocumentBlock.Describe Entry(string id, string name, string title, string statement,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forward integral window multiplies the tail Laplace transform and subtracts a finite cutoff correction.",
        H("Laplace transform of a forward window"),
        Blocks(
            Paragraph(Text("Let g be real-valued and let L(z) denote its tail Laplace transform with cutoff U "
                + "and kernel exp(−zt). The window uses times ahead of its starting time t, which gives "
                + "the positive sign in the exponent of the multiplier.")),
            Entry("forward-window", "forwardWindow", "Forward window integral",
                "The window at t is Wₕg(t)=∫ over (0,h] of g(t+v) dv.", DescribeRole.Definition),
            Entry("forward-window-eq-interval-integral", "forwardWindow_eq_intervalIntegral",
                "Interval integral for nonnegative widths",
                "If h≥0, then Wₕg(t)=∫₀ʰ g(t+v) dv.", DescribeRole.Theorem),
            Entry("window-multiplier", "windowMultiplier", "Window multiplier",
                "The multiplier Mₕ(z) is the integral of exp(zv) over (0,h].", DescribeRole.Definition),
            Entry("window-correction", "windowCorrection", "Finite cutoff correction",
                "The correction Q(z) is the integral over t∈(U−h,U] of exp(−zt) times "
                + "the integral of g over (U,t+h]. It is the contribution from starting the window "
                + "below U after extending g by zero on (−∞,U].", DescribeRole.Definition),
            Entry("window-multiplier-entire", "windowMultiplier_entire", "Entire multiplier",
                "For every real width h, the function Mₕ is entire.", DescribeRole.Theorem),
            Entry("window-multiplier-eq-div", "windowMultiplier_eq_div", "Closed form of the multiplier",
                "For h≥0 and z≠0, Mₕ(z)=(exp(zh)−1)/z.", DescribeRole.Theorem),
            Entry("window-multiplier-ne-zero-of-re-ne-zero", "windowMultiplier_ne_zero_of_re_ne_zero",
                "Nonvanishing off the imaginary axis",
                "If h>0 and Re(z)≠0, then Mₕ(z)≠0 since |exp(zh)|=exp(h Re(z))≠1.",
                DescribeRole.Theorem),
            Entry("window-correction-entire", "windowCorrection_entire", "Entire cutoff correction",
                "If h≥0 and g is integrable on (U,U+h], the finite cutoff correction Q is entire.",
                DescribeRole.Theorem),
            Entry("kernel-integrable-of-real-weight", "kernel_integrable_of_real_weight",
                "Integrability of the complex kernel",
                "If exp(−Re(z)t)g(t) is integrable on (U,∞), so is exp(−zt)g(t). "
                + "The two integrands have the same absolute value.", DescribeRole.Theorem),
            Entry("tail-laplace-forward-window", "tailLaplace_forwardWindow",
                "Transform identity at a convergent parameter",
                "If h≥0 and exp(−zt)g(t) is integrable on (U,∞), the window kernel is also integrable there. "
                + "Its tail transform is Mₕ(z)L(z)−Q(z). Extend g by zero below U, interchange the "
                + "absolutely integrable window and tail integrals, and subtract the contribution "
                + "for starts in (U−h,U].", DescribeRole.Theorem),
            Entry("forward-window-laplace-half-plane", "forwardWindow_laplace_halfPlane",
                "Transform identity on the right half-plane",
                "If h>0 and exp(−xt)g(t) is integrable on (U,∞) for each real x>0, then Q is entire "
                + "and the window transform converges absolutely and equals Mₕ(z)L(z)−Q(z) "
                + "for every z with Re(z)>0.", DescribeRole.Theorem),
            Entry("tail-laplace-first-moment-eq-neg-deriv", "tailLaplace_firstMoment_eq_neg_deriv",
                "First moment as a negative derivative",
                "If the derivative at s of the tail transform F of f is given by "
                + "−∫ over (U,∞) of t exp(−st)f(t) dt, then the tail transform of t↦t f(t) at s "
                + "equals −F′(s).", DescribeRole.Theorem),
            Entry("neg-deriv-euler-of-first-moment", "neg_deriv_euler_of_first_moment",
                "Euler equation for the first moment",
                "Suppose F is analytic at s and the identities zF″(z)+2F′(z)=Φ(z) and L(z)=−F′(z) "
                + "hold as germs at s. Differentiation gives sL″(s)+3L′(s)=−Φ′(s).", DescribeRole.Theorem))));
}
