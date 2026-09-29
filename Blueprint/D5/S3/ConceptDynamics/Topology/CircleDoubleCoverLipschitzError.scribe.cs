using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class CircleDoubleCoverLipschitzErrorDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean squared chord error for intrinsically Lipschitz selectors of the circle "
            + "squaring cover, with attainment for L at least one half.",
        H("Lipschitz Circle Reconstruction Error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("circle-lipschitz-chord-error"),
                DeclarationHandle.Create(Module + "circle_error"),
                H("Squared chord reconstruction error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a map s of the angle circle of circumference 2*pi, circle_error(s,x) "
                        + "is the squared complex norm of exp(2i*s(x)) - exp(i*x). "
                        + "The angle-circle metric is intrinsic; this definition uses the "
                        + "complex chord only for error measurement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circle-lipschitz-error-lower-bound"),
                DeclarationHandle.Create(Module + "lower_bound"),
                H("Uniform lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative L and every circle map s that is L-Lipschitz "
                            + "in the intrinsic quotient metric, normalized Haar mean "
                            + "circle_error(s,x) is at least 2/(2L+1).")),
                    Paragraph(Text(
                        "Lift s to a real angle theta. Its endpoint displacement is an "
                            + "integral number of turns, so the phase 2*theta(t)-t has odd, "
                            + "nonzero winding. Its derivative is bounded by 2L+1 almost "
                            + "everywhere. The primitive 2*(u-sin(u)) of 2-2*cos(u) converts "
                            + "that winding into a weighted variation of at least 4*pi; "
                            + "normalizing the interval integral by Haar measure yields the "
                            + "stated bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-lipschitz-error-sharpness"),
                DeclarationHandle.Create(Module + "sharpness"),
                H("Attainment at and above one half"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each L at least 1/2, an actual circle map is L-Lipschitz in "
                            + "the intrinsic metric and has normalized mean squared complex "
                            + "chord error exactly 2/(2L+1).")),
                    Paragraph(Text(
                        "Set a=2*pi/(2L+1) and b=2*pi-a. The real lift is t/2 on [0,b] "
                            + "and L*(2*pi-t) on [b,2*pi]. The branches agree at b and the "
                            + "endpoints agree on the circle. The proof checks both the "
                            + "direct and wrapping shortest arcs for global Lipschitz "
                            + "continuity. The error is zero on [0,b]; affine substitution "
                            + "and the primitive give the exact integral on [b,2*pi]. "
                            + "No sharpness statement for 0<L<1/2 is made."))),
                DescribeRole.Theorem))));
}
