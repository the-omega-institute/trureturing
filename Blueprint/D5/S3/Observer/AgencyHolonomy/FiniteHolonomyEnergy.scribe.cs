using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class FiniteHolonomyEnergyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite stable swap curvature aggregates into a faithful nonnegative energy.",
        H("Finite Holonomy Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-holonomy-energy"),
                DeclarationHandle.Create(Prefix + "finiteHolonomyEnergy"),
                H("Finite ordered-pair holonomy energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite carrier, sum the squared norm of a supplied curvature over "
                        + "all ordered pairs. This is the unnormalized positive scalar energy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stable-residual-holonomy-energy"),
                DeclarationHandle.Create(Prefix + "stableResidualHolonomyEnergy"),
                H("Stable residual holonomy energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specialize the finite energy to the stable residual swap curvature of "
                        + "the preceding truth source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-stable-holonomy-energy-bound"),
                DeclarationHandle.Create(
                    Prefix + "finite_stable_holonomy_energy_bound"),
                H("Residual envelopes control finite holonomy energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Unit-bounded channels and a common nonnegative residual envelope give "
                            + "a nonnegative energy bounded by the square of the carrier "
                            + "cardinality times the square of the pairwise residual bound.")),
                    Paragraph(Text(
                        "Because every summand is a squared norm, the total vanishes exactly "
                            + "when every pairwise curvature vanishes. A zero residual envelope "
                            + "therefore forces zero finite energy.")),
                    Paragraph(Text(
                        "The theorem is finite and unnormalized. It does not assert residual "
                            + "decay, observer-origin recovery near resonance, an infinite prime "
                            + "limit, or domination of zero-side spectral energy."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound")),
        ]));
}
