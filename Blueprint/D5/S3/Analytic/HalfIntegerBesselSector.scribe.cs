using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class HalfIntegerBesselSectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/HalfIntegerBesselSector.";
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Asymptotics/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Radial integration controls the normalized decaying and regular amplitudes on right half-plane sectors.",
        H("Sector bounds for the half-integer Bessel amplitudes"),
        Blocks(
            Node("reverse_eval", "Evaluation of the reversed carrier",
                "At nonzero z the reversed carrier evaluates to z^m times P_m(1/z).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
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
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sector_I_estimate", "Uniform sector bounds for the regular amplitude",
                "For kappa > 0 and nu at least 4 V_kappa, let delta = 2 V_kappa / nu. "
                + "At every nonzero w with Re w at least kappa |w|, the norm of F_I(w)/F_K(w) - 1 "
                + "is at most 10 delta / kappa, and the norm of F_I(w) - 1 is at most "
                + "(1 + 15 / kappa) delta. Along the inward ray, the Wronskian gives the derivative "
                + "of the normalized quotient correction as the phase kernel derivative times "
                + "(F_K^(-2) - 1). Factoring the inverse square error bounds its norm by 10 delta. "
                + "The sector angle compares the derivative norm to the derivative of the real "
                + "exponential kernel. Finite interval integration and the zero limit of the "
                + "correction at the origin give the quotient bound. Multiplying by F_K and using "
                + "its norm bound of 3/2 gives the regular amplitude bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("half-integer-bessel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
