using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class GeneralParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original general-parameter Mills target, regularity, Gamma coefficients, sharp origin obstruction, strict remainder moment bounds, closed kernel ranges and absolute Laplace control.",
        H("General-parameter Mills remainder classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("f-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F"),
                H("Original signed remainder normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "F n a x is the original signed remainder (-1)^n * D n x a, "
                    + "where D is imported from the frozen Xu-Yang Mills source and retains "
                    + "the Gaussian Mills ratio, Gamma coefficients, and finite truncation.")))),
            Describe.Lean(
                DescribeId.Create("theorem-21-target"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21"),
                H("Theorem 2.1 target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every n >= 2 and real a, the positive global-sign predicate is "
                        + "equivalent to complete monotonicity and to a <= theta (n-2); "
                        + "the negative global-sign predicate is equivalent to complete "
                        + "monotonicity of -F and to a >= theta (n-1), with both endpoints "
                        + "included. The proposition is retained as the exact source target.")),
                    Paragraph(Text(
                        "The proposition states two separate equivalences in each chain: "
                        + "global sign iff complete monotonicity, and complete monotonicity iff "
                        + "the sharp parameter bound. It is a target definition, not an asserted theorem. "
                        + "the exact Laplace representation and the positive sufficiency branch "
                        + "are now proved in the continuation; the infinity asymptotic, sharp negative "
                        + "necessity and complete two-chain theorem remain open."))),
                DescribeRole.Definition),
            Proof("regularity-and-origin", "regularity_and_origin",
                "Gaussian regularity and the original origin asymptotic",
                "For every n >= 2 and every real a, the original F n a is C-infinity on x > 0, "
                + "and x^(2n) F n a x tends to -u n a (a-2) as x decreases to zero. "
                + "The Gaussian tail equals its value at zero minus its interval primitive. "
                + "The fundamental theorem of calculus gives smoothness of that primitive. "
                + "After multiplying the finite remainder by x^(2n), every lower truncation "
                + "term vanishes at zero and only the original nth Gamma coefficient remains."),
            Proof("positive-origin-obstruction", "positive_cm_necessary",
                "Sharp necessary threshold for the positive branch",
                "For every n >= 2 and real a, if the original F n a is completely monotone, "
                + "then a <= theta (n-2). "
                + "The proof consumes the zeroth derivative sign and the concrete origin limit. "
                + "The hypothesis that F is globally nonnegative alone suffices, "
                + "as established by positive_sign_necessary. The exact general-a Gamma coefficient "
                + "identity and positivity of B_(n-2) translate u_n <= 0 into the threshold bound."),
            Proof("negative-origin-obstruction", "negative_cm_necessary",
                "Origin obstruction for the negative branch",
                "For every n >= 2 and real a, if -F n a is completely monotone, or merely globally nonnegative, "
                + "then a >= theta (n-2). This is the obstruction at the origin; "
                + "it does not establish the required infinity obstruction u (n+1) a (a-2) >= 0 "
                + "or the sharp negative-branch threshold theta (n-1)."),
            Proof("remainder-upper-multiplier", "exp_remainder_ratio_strict_anti",
                "Strictly decreasing upper normalized remainder",
                "Write E_k(y) = (-1)^k (exp(-y) - sum_{j<k} (-y)^j/j!). "
                + "For every k >= 1, E_k(y)/y^k strictly decreases on y > 0. "
                + "The proof uses the existing public ExpRemainderDifferences.R with k=r+1, "
                + "then the pinned Mathlib Taylor integral theorem gives "
                + "E_k(y)/y^k = integral_0^1 (1-s)^(k-1) exp(-sy) ds / (k-1)!. "
                + "Strict integral comparison at s=1/2 proves the multiplier order."),
            Proof("remainder-lower-multiplier", "exp_remainder_ratio_strict_mono",
                "Strictly increasing lower normalized remainder",
                "For every k >= 1, E_k(y)/y^(k-1) strictly increases on y > 0. "
                + "Changing variables in the same Taylor integral gives "
                + "E_k(y)/y^(k-1) = integral_0^y (1-q/y)^(k-1) exp(-q) dq / (k-1)!. "
                + "Increasing y increases the integrand on the old interval and adds a strictly "
                + "positive interval. This includes k=1."),
            Proof("moment-ratio-bounds", "moment_ratio_bounds",
                "Strict exponential remainder moment bounds",
                "With source remainder order r+1 and z positive, B_r/I_r < M2/M0 "
                + "< B_(r+1)/I_(r+1). Both M0 and M2 are strictly positive. "
                + "Apply IncompleteBeta.Comparison.weighted_means_lt to the positive densities "
                + "E_(r+1)(z(1+v^2)) and (1+v^2)^r for the lower bound, "
                + "and to (1+v^2)^(r+1) and E_(r+1)(z(1+v^2)) for the upper bound. "
                + "The two proved normalized remainder orders give the required strict density ratios."),
            Proof("inner-threshold-bounds", "inner_threshold_bounds",
                "Strict inner threshold bounds",
                "The two positive moment ratios imply theta_r < (1-M0/M2)/2 < theta_(r+1). "
                + "Every denominator is strictly positive, including both polynomial moments. "
                + "The conclusion holds for every r >= 0 and z > 0."),
            Proof("closed-kernel-ranges", "kernel_closed_ranges",
                "Both closed parameter ranges for the signed kernel",
                "For source truncation n=r+2 and every t>0, the kernel L from (2.5) "
                + "is strictly positive when a <= theta_r and strictly negative when a >= theta_(r+1). "
                + "Its inner integral is exactly 2 M2 times the difference between the inner threshold "
                + "and a. The strict inner bounds include both parameter endpoints. "
                + "This proves the kernel sign ranges. The continuation below proves equality of its "
                + "Laplace integral with the original F and uses it for both sufficiency branches."),
            Proof("original-coefficient-identity", "coefficient_identity",
                "Exact general-parameter Gamma coefficient correspondence",
                "For every r >= 0 and real a, the original u_(r+2)(a,a-2) equals "
                + "(2r+3)! / (4^(r+1) r!) times (I_r+(2a-1)B_r). "
                + "The proof directly consumes Result.coeff_sum, Result.intPow_rec and "
                + "Result.coeff_factorial at their original owner. "
                + "The same original identities give u_1(a,a-2)=0 for every real a; "
                + "this removes the first term from the rescaled finite sum. "
                + "Linearity of the polynomial moment gives B_r=I_(r+1)-I_r. "
                + "The coefficient is a strictly positive factor times a-theta_r. "
                + "Both coefficient-sign equivalences include the zero endpoint."),
            Proof("kernel-polynomial-bound", "kernel_polynomial_bound",
                "Absolute polynomial bound for the signed kernel",
                "For every r >= 0, every real a and t >= 0, the absolute value of L r a t "
                + "is at most (abs(1-2a)+1) t^(2r+5). The source remainder order is r+1. "
                + "The proof consumes the exact original Result.expRemainderBounds through "
                + "E r y = Result.expRemainder (r+1) y. The coefficient weight is bounded "
                + "in absolute value on [0,1], so this estimate holds without a sign restriction on a."),
            Proof("kernel-exponential-moments", "kernel_exponential_moments",
                "Every absolute exponential moment of the signed kernel",
                "For every pair of natural orders r,m, every real a and every x>0, "
                + "t^m exp(-xt) L r a t is absolutely integrable on t>0. "
                + "The polynomial estimate is dominated by the existing exact exponential "
                + "moment of order m+2r+5. The kernel is continuous for all real t."),
            Proof("kernel-laplace-rec", "kernel_laplace_rec",
                "Exact original Gamma coefficient in the Laplace recurrence",
                "For every r>=0, real a and x>0, the Laplace integral of L (r+1) a "
                + "equals -u_(r+3)(a,a-2)/x^(2r+6) minus the Laplace integral of L r a. "
                + "The exact original exponential-remainder recurrence gives the polynomial "
                + "kernel difference. Absolute integrability permits integral subtraction, "
                + "and the original coefficient_identity identifies the polynomial moment."),
            Proof("finite-laplace-subtraction", "laplace_finite_subtraction",
                "Exact finite subtraction inside the Laplace integral",
                "For every r>=0, real a and x>0, the Laplace integral of L r a equals "
                + "(-1)^(r+2) times the Laplace integral of the original G_a minus the "
                + "finite sum of the original (-1)^k u_k(a,a-2)/x^(2k), with 1<=k<=r+2. "
                + "The base case subtracts u_2/x^4 and uses u_1=0. The exact kernel recurrence "
                + "then adds each successive Gamma term. All integral subtractions are absolutely integrable. "
                + "The difference between this expression and the actual F is precisely "
                + "(-1)^(r+2) times Y_(a,a-2)-(a-1)-Laplace(G_a)."),
            Proof("signed-kernel-all-orders", "signed_kernel_moment_iterated",
                "Every ordinary derivative of the signed kernel integral",
                "For every r,m>=0 and every real a, the mth ordinary derivative of the Laplace "
                + "integral of L r a equals the integral of (-t)^m exp(-xt) L r a t for x>0. "
                + "No positivity assumption on the kernel or parameter is used. "
                + "On y>x/2, the absolute derivative integrand is dominated by "
                + "(abs(1-2a)+1) t^(m+2r+6) exp(-xt/2), an integrable exponential moment. "
                + "Repeated dominated differentiation also gives C-infinity regularity of this integral."),
            Proof("all-order-original-defect", "all_order_laplace_defect",
                "The exact outstanding Gaussian term in every derivative of the original F",
                "For every derivative order m including zero, the mth derivative of the original "
                + "F_(r+2,a) equals the signed-kernel moment plus the mth derivative of "
                + "(-1)^(r+2) [Y_(a,a-2)-(a-1)-Laplace(G_a)]. "
                + "The finite-subtraction identity and smoothness justify this equality on x>0. "
                + "The Gaussian identity is discharged in the continuation below. The remaining open "
                + "obligations are the infinity asymptotic, sharp negative necessity and assembly of "
                + "the complete two-chain classification."),
            Proof("gaussian-kernel-identity", "gaussian_kernel_identity",
                "General-parameter Gaussian convolution kernel identity",
                "For every real a and t, the source kernel G_a(t) equals "
                + "t^3/4 times the integral from zero to one of "
                + "(1+(2a-1)v^2) exp(-(1+v^2)t^2/4). "
                + "Integrating the derivative of v exp(-(1+v^2)t^2/4) gives "
                + "exp(-t^2/2) as the integral of (1-t^2 v^2/2) times the same exponential. "
                + "Substitution in G and linearity of the integral give the stated identity. "
                + "This is the source's pointwise identity (2.3)."),
            Proof("gaussian-kernel-base", "gaussian_kernel_eq_K",
                "The negative-parameter Gaussian kernel is the original K kernel",
                "A second interval integration by parts gives G_(-1)(t)=K(t), preserving the "
                + "original Gaussian convolution normalization and the exact K supplier."),
            Proof("gaussian-laplace-identity", "gaussian_laplace_identity",
                "The exact general-parameter Gaussian Laplace identity",
                "The original Mills Laplace formula and square convolution are combined with the "
                + "original kernelLaplace identity at parameter -1. A direct integration by parts gives "
                + "the t times Gaussian integral, and linearity in a then yields "
                + "Y_(a,a-2)(x)-(a-1)=integral exp(-xt) G_a(t) for every x>0."),
            Proof("actual-f-laplace", "actual_f_laplace",
                "The exact Laplace representation of the original F",
                "Substitution of the Gaussian identity into the finite-subtraction defect removes the "
                + "residual exactly, giving F_(r+2,a)(x)=integral exp(-xt)L_(r,a)(t)."),
            Proof("actual-f-iterated-deriv", "actual_f_iterated_deriv",
                "Every ordinary derivative of the original F",
                "The exact Laplace representation and the signed-kernel iterated differentiation theorem "
                + "give the integral of (-t)^m exp(-xt)L for every ordinary order m, including zero."),
            Proof("positive-cm-sufficiency", "positive_cm_sufficiency",
                "Positive complete-monotonicity sufficiency with the closed endpoint",
                "The positive closed kernel range, exact F Laplace representation and all-order derivative "
                + "formula prove complete monotonicity whenever a <= theta_(n-2), including equality."),
            Proof("negative-cm-sufficiency", "negative_cm_sufficiency",
                "Negative complete-monotonicity sufficiency with the closed endpoint",
                "The negative closed kernel range, exact F Laplace representation and all-order derivative "
                + "formula prove complete monotonicity of -F whenever a >= theta_(n-1), including equality. "
                + "The converse still requires the infinity asymptotic."))));

    private static DocumentBlock Proof(string id, string name, string title, string narrative) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter." + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))),
            DescribeRole.Theorem);
}
