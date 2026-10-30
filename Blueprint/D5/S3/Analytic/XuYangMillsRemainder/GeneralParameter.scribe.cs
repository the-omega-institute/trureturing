using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class GeneralParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original general-parameter Mills target, regularity, origin asymptotic, strict remainder moment bounds and closed kernel ranges.",
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
                        + "The exact Laplace representation, "
                        + "infinity asymptotic and both classification "
                        + "chains remain open."))),
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
                + "This proves the kernel sign ranges; equality of its Laplace integral with the original "
                + "F, all derivative signs and the complete classification remain open."),
            Proof("original-coefficient-identity", "coefficient_identity",
                "Exact general-parameter Gamma coefficient correspondence",
                "For every r >= 0 and real a, the original u_(r+2)(a,a-2) equals "
                + "(2r+3)! / (4^(r+1) r!) times (I_r+(2a-1)B_r). "
                + "The proof directly consumes Result.coeff_sum, Result.intPow_rec and "
                + "Result.coeff_factorial at their original owner. "
                + "Linearity of the polynomial moment gives B_r=I_(r+1)-I_r. "
                + "The coefficient is a strictly positive factor times a-theta_r. "
                + "Both coefficient-sign equivalences include the zero endpoint."),
            Proof("gaussian-kernel-identity", "gaussian_kernel_identity",
                "General-parameter Gaussian convolution kernel identity",
                "For every real a and t, the source kernel G_a(t) equals "
                + "t^3/4 times the integral from zero to one of "
                + "(1+(2a-1)v^2) exp(-(1+v^2)t^2/4). "
                + "Integrating the derivative of v exp(-(1+v^2)t^2/4) gives "
                + "exp(-t^2/2) as the integral of (1-t^2 v^2/2) times the same exponential. "
                + "Substitution in G and linearity of the integral give the stated identity. "
                + "This is the source's pointwise identity (2.3); its Laplace relation with Y "
                + "is not asserted here."))));

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
