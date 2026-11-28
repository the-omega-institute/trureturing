using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class PeriodicSublevelSamplingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/PeriodicSublevelSampling";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low-frequency estimates control the weighted mass of shrinking periodic sublevels.",
        H("Weighted sampling at regular periodic zeros"),
        Blocks(Describe.Lean(
            DescribeId.Create("tendsto-weighted-sublevel-of-fourier"),
            DeclarationHandle.Create(Owner + ".tendsto_weighted_sublevel_of_fourier"),
            H("The determinant coefficient for shrinking sublevels"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be a continuous map of the Euclidean plane, periodic under integer "
                    + "translations. Use a closed fundamental square formed by translating the unit square. "
                    + "List all its zeros in a finite list without repetition. They lie in the interior and "
                    + "have invertible Fréchet derivatives Aᵢ. "
                    + "An empty list is allowed.")),
                Paragraph(Text(
                    "Fix an index type and a filter on it. In each finite sample take nonnegative "
                    + "weights summing to one, a positive "
                    + "threshold εₙ tending to zero, and a positive integer cutoff Jₙ. For each "
                    + "nonzero integer frequency of maximum coordinate norm at most Jₙ, assume "
                    + "the weighted sum of exp(2πi⟨x,m⟩) has modulus at most cₙ + dₙ‖m‖∞² for "
                    + "nonnegative cₙ and dₙ. Assume cₙ/εₙ², dₙ/εₙ⁴ and 1/(εₙ⁶Jₙ⁴) tend to zero along the same filter.")),
                Paragraph(Text(
                    "Then the sum of weights at points with ‖F(x)‖ < εₙ, divided by εₙ², tends "
                    + "to π times the sum of |det Aᵢ|⁻¹. The derivatives use period-one coordinates.")),
                Paragraph(Text(
                    "The sampling estimate controls each fixed test after scaling, translating and "
                    + "periodizing it. Dividing by εₙ² makes the three error terms tend to zero. "
                    + "Nonnegative weights preserve the pointwise inequalities from the periodic "
                    + "sandwich. Finite sums of the tests converge to the sums of their plane "
                    + "integrals. Letting the two radii approach one squeezes the mass to the "
                    + "determinant coefficient.")),
                Paragraph(Text(
                    "For clock samples, the multiplicities must enter the normalized weights. "
                    + "The Fourier estimates, the zero enumeration and the derivative hypotheses "
                    + "must be verified for the chosen map and clock samples."))),
            DescribeRole.Theorem))));
}
