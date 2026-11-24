using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibCoherentDisksDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks.extendible_iff_selected";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed-form choice of coupling for coherent marginals on three Fibonacci sites.",
        H("The two residual disks for Fibonacci marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-coherent-disks"),
                DeclarationHandle.Create(Result), H("Testing one prescribed coupling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume positive middle occupation and Hermitian endpoint blocks. A common "
                    + "positive semidefinite trace-one extension exists exactly when the two "
                    + "endpoint block traces equal one minus the middle occupation and both "
                    + "Schur residuals at the prescribed coupling are positive semidefinite.")),
                    Paragraph(Text(
                    "After scaling by the middle occupation, either residual has a fixed "
                    + "upper diagonal a, a lower diagonal e minus the squared modulus of z, "
                    + "and upper off-diagonal c minus the conjugate of k times z. For positive a, "
                    + "the determinant inequality completes a square centered at k times c "
                    + "divided by a plus the squared modulus of k. For zero a, the off-diagonal "
                    + "must vanish and the lower diagonal must be nonnegative. This gives a disk, "
                    + "a single point or an empty set. Negative a gives an empty set.")),
                    Paragraph(Text(
                    "For disk centers p and q, squared radii r and s, and squared center "
                    + "distance d, select the point on the segment at parameter "
                    + "(d + r - s) / (2d) clipped to the interval from zero to one. "
                    + "At coincident centers the selected point is their common center. "
                    + "The weighted squared-distance identity shows this point belongs to both "
                    + "disks whenever their intersection is nonempty."))),
                DescribeRole.Theorem))));
}
