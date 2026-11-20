using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class HalfIntegerBesselDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/HalfIntegerBessel.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Analytic/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite complex half-integer carriers and their Wronskians on the right half-plane.",
        H("Complex half-integer modified Bessel carriers"),
        Blocks(
            Node("prefactor", "Common prefactor",
                "The common prefactor is the positive real square root of pi/2 divided by "
                + "the principal complex square root of z.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("K", "Decaying carrier",
                "At order m+1/2, K is the prefactor times exp(-z) times P_m(1/z), "
                + "where P_m is the rational factorial polynomial.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("L", "Reflected carrier",
                "The growing carrier is the prefactor times exp(z) times P_m(-1/z).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("I", "Regular carrier",
                "The regular carrier I is the difference of L and (-1)^m K divided by pi.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("hasDerivAt_K", "Derivative of the decaying carrier",
                "On Re z > 0 the derivative of K is its prefactor times exp(-z) times "
                + "the sum of -(1+1/(2z)) P_m(1/z) and -P_m'(1/z)/z^2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("hasDerivAt_L", "Derivative of the reflected carrier",
                "On Re z > 0 the derivative of L is its prefactor times exp(z) times "
                + "the sum of (1-1/(2z)) Q_m(1/z) and -Q_m'(1/z)/z^2, "
                + "where Q_m(X) = P_m(-X).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("hasDerivAt_I", "Derivative of the regular carrier",
                "On Re z > 0 the derivative of I is (L' - (-1)^m K')/pi.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wronskian_KL", "Wronskian of the finite reflected pair",
                "On Re z > 0, z(K L' - K' L) = pi. The square-root terms cancel "
                + "in the derivative difference. Evaluating the rational reflected Wronskian "
                + "at 1/z gives the factor 2, and the squared prefactor is pi/(2z).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wronskian_KI", "Wronskian of the decaying and regular carriers",
                "On Re z > 0, K I' - K' I = 1/z. The multiple of K cancels and "
                + "the reflected Wronskian is divided by pi.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("hasDerivAt_deriv_K", "Ordinary modified Bessel equation",
                "At order nu = m+1/2 and on Re z > 0, the derivative of K' is "
                + "(1+nu^2/z^2) K - K'/z. Differentiating the finite carrier twice "
                + "reduces the equation to the rational polynomial equation at 1/z.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("order", "Real order", "The order nu is m + 1/2.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("S", "Phase root", "S(w) is the principal square root of 1 + w^2.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("S_re_pos", "Sign of the phase root",
                "If Re w > 0, then Re S(w) > 0. The radicand lies in the slit plane.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("eta", "Phase", "The phase is S(w) + Log w - Log(1 + S(w)), with principal logarithms.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("eta_eq_log_div", "Principal logarithm of the phase quotient",
                "On Re w > 0 the phase is S(w) + Log(w / (1 + S(w))).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("hasDerivAt_eta", "Phase derivative",
                "On Re w > 0 the derivative of the phase is S(w) / w.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("F_K", "Normalized decaying amplitude",
                "F_K is sqrt(2 nu / pi) sqrt(S(w)) exp(nu eta(w)) K_m(nu w). "
                + "The first root is real and the second is principal complex.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("F_K_eq_carrier", "Canceled normalization of the decaying amplitude",
                "On Re w > 0, F_K is sqrt(S(w)) / sqrt(w) times exp(nu (eta(w) - w)) "
                + "times P_m(1 / (nu w)). Positive real scaling factors out of the principal root.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("D", "Phase differentiation",
                "D applies the complex derivative and multiplies by w / S(w).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("psi", "Liouville–Green potential",
                "The potential is w^2 (4 - w^2) / (4 (1 + w^2)^3).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("liouvilleGreen_K", "Scaled equation for the decaying amplitude",
                "On Re w > 0, D^2 F_K - 2 nu D F_K = psi F_K. The scaled ordinary "
                + "equation for K_m first gives D^2 U = (nu^2 + psi) U for "
                + "U = sqrt(S(w)) K_m(nu w). The exponential factor gives the equation for F_K.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("radialP", "Radial phase coefficient", "For the ray r u, p(r) is S(r u) / r.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("radialQ", "Radial potential coefficient", "On the ray, q(r) is p(r) psi(r u).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("radialSystem_K", "Radial system for the decaying amplitude",
                "For Re u > 0 and r > 0, eta(r u) has derivative p(r). With F(r) = F_K(r u) "
                + "and G(r) = (D F_K)(r u), the real derivatives are F' = p G "
                + "and G' = 2 nu p G + q F. Also Re p > 0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radial_S_re_ge", "Sector angle of the phase root",
                "If u has unit norm and positive real part and r > 0, then "
                + "Re S(r u) is at least Re u times the norm of S(r u).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sectorMajorant", "Sector majorant",
                "Q_kappa(r) is r (4 + r^2) / (4 (sqrt(kappa))^5 (sqrt(1 + r^2))^5).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("norm_radialQ_le", "Pointwise radial potential bound",
                "For kappa > 0, a unit ray with Re u at least kappa, and r > 0, "
                + "the norm of q(r) is at most Q_kappa(r).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sectorMajorant_mass", "Finite interval mass bound",
                "For every pair of real endpoints and kappa > 0, the oriented integral "
                + "of Q_kappa is at most 1 / (2 (sqrt(kappa))^5). The negative derivative of "
                + "((1+r^2)^(-1/2) + (1+r^2)^(-3/2)) / (4 kappa^(5/2)) is Q_kappa.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radial_K_terminal", "Terminal values of the decaying amplitude",
                "As r tends to infinity along Re u > 0, F_K(r u) tends to one and "
                + "(D F_K)(r u) tends to zero. In the reciprocal coordinate v = 1/w, "
                + "write T = S(v). The principal-root and logarithm identities give the "
                + "analytic amplitude sqrt(T) exp(nu (v/(1+T) - Log(v+T))) P_m(v/nu) "
                + "at v = 0. The derivative in the phase variable acts there by "
                + "multiplying the v derivative by -v^2/T.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sectorMass", "Sector mass",
                "V_kappa is 1 / (2 (sqrt(kappa))^5).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("radial_K_bounds", "Volterra bounds on a unit ray",
                "For kappa > 0, nu > V_kappa, Re u at least kappa, |u| = 1 and r > 0, "
                + "the norms of F_K(r u) and F_K(r u) - 1 are bounded by "
                + "nu / (nu - V_kappa) and V_kappa / (nu - V_kappa), respectively.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sector_K_estimate", "Uniform sector error and nonvanishing",
                "For kappa > 0 and nu at least 4 V_kappa, at every nonzero w with "
                + "Re w at least kappa |w|, the norm of F_K(w) - 1 is at most "
                + "2 V_kappa / nu, which is at most 1/2, and K_m(nu w) is nonzero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("F_I", "Normalized regular amplitude",
                "F_I is sqrt(2 pi nu) sqrt(S(w)) exp(-nu eta(w)) I_m(nu w). "
                + "The first root is real and the second is principal complex.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Dlmf)),
            Node("F_I_div_F_K", "Relative amplitude normalization",
                "On Re w > 0 with K_m(nu w) nonzero, the ratio F_I / F_K equals "
                + "pi exp(-2 nu eta(w)) I_m(nu w) / K_m(nu w).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radial_I_div_K_zero", "Carrier quotient at the origin",
                "For Re u > 0, I_m(nu r u) / K_m(nu r u) tends to zero as r decreases to zero. "
                + "Reversing the degree-m carrier P_m gives B_m with B_m(0) nonzero. "
                + "The analytic expression for the quotient near zero is "
                + "(-1)^m (exp(2z) B_m(-z) / B_m(z) - 1) / pi at z = nu r u.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radial_eta_re_atBot", "Phase at the origin",
                "On a unit ray, Re eta(r u) tends to negative infinity as r decreases "
                + "to zero. Its log(r) term diverges and the remaining terms are continuous "
                + "at zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("half-integer-bessel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
