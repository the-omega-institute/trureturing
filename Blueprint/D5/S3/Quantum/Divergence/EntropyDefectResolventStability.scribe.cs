using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class EntropyDefectResolventStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantum entropy loss controls supported resolvent intertwining.",
        H("Entropy defect and resolvent stability"), Blocks(
            Describe.Lean(
                DescribeId.Create("entropy-defect-resolvent-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/EntropyDefectResolventStability.entropy_defect_resolvent_stability"),
                H("A quartic error bound without faithful physical states"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For an arbitrary finite quantum channel and density states with input support "
                    + "containment, construct the existing canonical supported relative-modular model M. At every "
                    + "positive shift t, let w be the difference between (A+tI) inverse applied to the normalized "
                    + "input vector and V applied to (B+tI) inverse of the output vector. Then t^4 times "
                    + "the square of the squared L2 norm of w is at most four times the actual finite trace-log "
                    + "relative-entropy loss. Positivity is used only on the support carriers, so singular physical "
                    + "states are included.")),
                    Paragraph(Text("The proof reuses the canonical supported model, the spectral quadratic-form "
                    + "expansion and the saturated resolvent energy bound. The new finite-calculus step expands "
                    + "the shifted logarithmic difference F in positive spectral points with nonnegative unit-mass "
                    + "weights. Its derivative G is nonnegative and its limit at infinity is zero. The reciprocal "
                    + "inequality G(s) >= G(t) - (s-t)/t^2 makes F(s) - G(t)(s-t) + (s-t)^2/t^2 "
                    + "monotone for s >= t. Evaluate at s=t+G(t)t^2/2 and use F(0) <= F(t) <= F(s) <= 0. "
                    + "This bounds t^2 G(t)^2 by four times the entropy loss; the existing energy inequality "
                    + "t times norm squared of w <= G(t) gives the claimed quartic estimate. "
                    + "This is a repository derivation from finite spectral calculus and existing suppliers. "
                    + "It supplies no trace-distance recovery estimate or claim of literature novelty."))),
                DescribeRole.Theorem))));
}
