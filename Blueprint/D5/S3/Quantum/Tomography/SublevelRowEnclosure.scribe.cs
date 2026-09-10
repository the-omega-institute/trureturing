using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class SublevelRowEnclosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every small-residual point is contained in an explicitly inflated preconditioned Newton row.",
        H("Scalar-Row Sublevel Enclosure"),
        Blocks(Describe.Lean(
            DescribeId.Create("preconditioned-sublevel-row-enclosure"),
            DeclarationHandle.Create("D5/S3/Quantum/Tomography/SublevelRowEnclosure.preconditioned_sublevel_row_enclosure"),
            H("A scalar mean-value estimate preserves all sublevel points"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("PreconditionedSublevelRowEnclosure"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let f:E to F have actual Frechet derivative J at every point m+t(x-m), "
                    + "0<=t<=1. Let observe:E to R and precondition:F to R be continuous linear maps. "
                    + "Suppose the absolute value of observe(x-m)-precondition(J(m+t(x-m))(x-m)) "
                    + "is bounded by radius along this segment, and norm(f(x))<=eta. "
                    + "Then the distance from observe(x) to observe(m)-precondition(f(m)) "
                    + "is at most radius+norm(precondition)*eta.")),
                Paragraph(Text(
                    "The proof composes the actual derivative with the segment map and applies "
                    + "Mathlib's scalar mean-value norm inequality. Each output row may use its own "
                    + "scalar estimate. No common intermediate point for a vector-valued mean-value "
                    + "equality is assumed. The residual inflation is essential; setting it to zero "
                    + "would only certify exact roots.")),
                Paragraph(Text(
                    "The interval implementation can discharge the directional bound by enclosing "
                    + "each row of (I-CJ) times the box displacement. This theorem certifies the "
                    + "analytic row inequality only. It does not by itself certify interval arithmetic, "
                    + "the concrete rational residual derivative, the complete subdivision tree, "
                    + "or any external JSON verdict. The source has not been locally elaborated."))),
            DescribeRole.Theorem))));
}
