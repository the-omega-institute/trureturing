using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class ExponentialMultiplierFourierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/ExponentialMultiplierFourier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exponential multiplier in the normalized inverse Fourier transform.",
        H("Fourier inversion with an exponential multiplier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-multiplier"),
                DeclarationHandle.Create(Prefix + "targetMultiplier"),
                H("Target-line multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real c and ξ, the target-line multiplier is c/(c + 2πiξ)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("target-inverse-mem-lp"),
                DeclarationHandle.Create(Prefix + "targetInverse_memLp"),
                H("L² contraction of the pointwise inverse"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let c > 0 and let f be a complex-valued L² function on the real "
                    + "line. If the product of f and the target-line multiplier is "
                    + "integrable, its pointwise inverse Fourier transform belongs to "
                    + "L² and has extended L² norm at most that of f."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-inverse-eq-vertical-integral"),
                DeclarationHandle.Create(Prefix + "targetInverse_eq_vertical_integral"),
                H("Normalization of the target-line integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real σ, c, t and any complex function F, evaluate the inverse "
                    + "Fourier transform of ξ ↦ F(σ + 2πiξ) c/(c + 2πiξ) at t. "
                    + "It equals the integral of the smoothed integrand along σ + iy "
                    + "with respect to real y, scaled by 1/(2π). Both integrals use "
                    + "Lean's total Bochner integral."))),
                DescribeRole.Theorem))));
}
