using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RootSpectrumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual zero spectrum at a real root cutoff",
        H("The signed transform and its primitive"),
        Blocks(
            Entry("root-density", "rootDensity", "The log density at degree r",
                "For r > 1, each actual nontrivial zero occurrence rho contributes the coefficient "
                + "-r/[rho(r-rho)] times exp((rho/r-1/2)u). Take the real part after summation.",
                DescribeRole.Definition),
            Entry("root-spectral-transform", "root_spectral_transform", "The weighted transform of the zero tail",
                "At y = exp(v), the substitution s = exp(w) changes the spectral exponent from rho-1 to rho-r. "
                + "The open critical strip and absolute coefficient summability give an integrable majorant "
                + "on w > v. Termwise integration supplies 1/(r-rho). Combining the integrated and boundary "
                + "terms gives the density at u = rv.",
                DescribeRole.Theorem),
            Entry("root-primitive", "rootPrimitive", "The endpoint primitive",
                "For x > 0 the primitive is the real part of the sum of "
                + "2r² x^(rho/r-1/2)/[rho(r-rho)(r-2rho)] over the same occurrences.",
                DescribeRole.Definition),
            Entry("root-density-integral", "root_density_integral", "The oriented integral between two log cutoffs",
                "The density is interval integrable for every pair of real log cutoffs. "
                + "Absolute convergence on each bounded interval permits termwise integration, "
                + "and the result is the primitive at exp(b) minus the primitive at exp(a). "
                + "The identity includes reversed and equal endpoints.",
                DescribeRole.Theorem),
            Entry("root-centered-error", "root_centered_error", "The unconditional error after subtracting the spectrum",
                "For r > 1 and v at least log(2), set x = exp(rv). "
                + "The centered normalized Chebyshev tail at degree r differs from the log density at rv "
                + "by at most (2r-1)|log(2π)|x^(-1/2). "
                + "The pointwise residual in the complete formula and its weighted integral supply the two terms in the bound.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(
        string id, string name, string heading, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
