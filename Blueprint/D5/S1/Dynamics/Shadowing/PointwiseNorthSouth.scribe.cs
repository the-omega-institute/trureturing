using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class PointwiseNorthSouthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/PointwiseNorthSouth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sided pointwise north-south dynamics forces stable poles and uniform attraction on compact sets away from the opposite pole.",
        H("Pointwise North-South Stability and Compact Uniformity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stability-and-compact-uniformity"),
                DeclarationHandle.Create(Owner + "stability_and_compact_uniformity"),
                H("Stability and uniform attraction are conclusions"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "M is an arbitrary compact metric space and f is a homeomorphism. The distinct "
                        + "poles N and S are fixed. Every other point converges to S under nonnegative "
                        + "powers of f and to N under nonnegative powers of its inverse. These are "
                        + "pointwise assumptions; stability, uniformity, local connectedness, a flow "
                        + "and differentiability are not premises.")),
                    Paragraph(Text(
                        "Both poles are Lyapunov stable in the appropriate direction. On every compact "
                        + "C excluding N, all sufficiently large forward iterates lie in any prescribed "
                        + "neighborhood of S, uniformly over C. The inverse assertion holds for compact "
                        + "C excluding S. Empty compact sets and the two-point space remain in scope.")),
                    Paragraph(Text(
                        "Failure of stability gives first-exit points with exit times tending to infinity. "
                        + "A compact subsequential limit is outside a small pole neighborhood; every "
                        + "strictly negative iterate belongs to its closure, which excludes N. The "
                        + "pointwise backward limit gives the contradiction. Stable-entry neighborhoods "
                        + "then form a finite cover of each compact C, giving uniform attraction.")),
                    Paragraph(Text(
                        "This is the first dependency of the supplied full north-south crossing-selector "
                        + "proof, public-proof.txt SHA-256 "
                        + "9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc. "
                        + "It does not by itself construct the selector or settle Artigue's final "
                        + "Question 5.19, printed page 52 (arXiv v1 Question 5.21). The source is "
                        + "Alfonso Artigue, Shadowing maps, DOI 10.2140/om.2027.4.29. No priority "
                        + "or comprehensive literature novelty claim is made."))),
                DescribeRole.Theorem))));
}
