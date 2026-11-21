using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class SquareSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed square-cutoff zero series",
        H("The square-cutoff primitive at common endpoints"),
        Blocks(
            Entry("zero-tail", "zeroTail", "The complete log-coordinate zero tail",
                "Each natural-number index is one actual nontrivial zero occurrence, with analytic multiplicity.",
                DescribeRole.Definition),
            Entry("norm-zero-tail-le", "norm_zeroTail_le", "Absolute control under RH",
                "The sum of the absolute coefficients is firstLiMass. Each log-coordinate exponential has norm exp(-u/2) under RH.",
                DescribeRole.Theorem),
            Entry("zero-tail-eq", "zeroTail_eq", "The normalization of the existing zero series",
                "Multiplication by exp(-u) converts the exponent rho to rho-1 for each occurrence.",
                DescribeRole.Theorem),
            Entry("square-density", "squareDensity", "Square-cutoff log density",
                "The coefficient is -2/[rho(2-rho)] at every occurrence and the exponential is exp((rho-1)u/2).",
                DescribeRole.Definition),
            Entry("square-spectral-transform", "square_spectral_transform", "The signed transform at the square cutoff",
                "In the weighted integral, the substitution s=exp(v) changes the mode exponent from rho-1 to rho-2. "
                + "The norms of the weighted modes sum to an integrable multiple of exp(-3v/2) above the cutoff. "
                + "The integrated mode introduces 1/(2-rho). Subtraction from the boundary mode and multiplication by -2 give the stated density coefficient.",
                DescribeRole.Theorem),
            Entry("square-primitive", "squarePrimitive", "The square-cutoff primitive",
                "The primitive holds the complex power x^((rho-1)/2) and coefficient 4/[rho(1-rho)(2-rho)] before taking real parts.",
                DescribeRole.Definition),
            Entry("square-power-half-phase", "square_power_half_phase", "The same occurrence at the half and full log phase",
                "For x>0 the power factors into x^(-1/4) times the actual phase at log(x)/2. Squaring that phase gives the actual phase at log(x).",
                DescribeRole.Theorem),
            Entry("square-density-integral", "square_density_integral", "The square density integrates to an endpoint difference",
                "Absolute convergence on every finite interval permits termwise integration. Dividing by (rho-1)/2 produces the primitive coefficient, "
                + "and the two values use the same occurrence indexing at their respective endpoints.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string heading, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SquareSpectrum." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
