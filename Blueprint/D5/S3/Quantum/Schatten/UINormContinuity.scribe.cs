using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class UINormContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity and balanced scalar optimization.", H("UINormContinuity"), Blocks(
            Paragraph(Text("A unitarily invariant norm is convex by its triangle inequality and absolute homogeneity. Mathlib's continuity theorem for finite dimensional convex functions therefore gives continuity in the usual topology of finite complex matrices. Unitary invariance is unnecessary for this continuity argument.")),
            Paragraph(Text("For nonnegative m, f and g, the inequalities 2m ≤ tf + g/t for every positive t imply m² ≤ fg. If m is positive and f is positive, use t = m/f. If f vanishes, use t = (g+1)/m to contradict m > 0. This includes vanishing factors and avoids requiring a positive minimizing parameter.")),
            Paragraph(Text("These elementary consequences are used by the balanced inverse-adjoint argument for the rank-one matrix norm inequality. No mathematical originality is claimed.")))));
}
