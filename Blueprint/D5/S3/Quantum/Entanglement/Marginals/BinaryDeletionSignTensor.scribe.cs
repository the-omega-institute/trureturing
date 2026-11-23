using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class BinaryDeletionSignTensorDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer witness for each ordered bit pattern, with vanishing one-site deletions.",
        H("Integer coefficients with zero one-site deletions"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-deletion-signed-tensor-cancellation"),
                DeclarationHandle.Create(Owner + ".deleteSite"), H("Cancellation at any site"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pattern at a site records agreement or one of the two ordered differences. "
                    + "An agreement contributes +1 at 00 and −1 at 11. A difference contributes "
                    + "+1 at its indicated pair. All other local coefficients are zero. "
                    + "When both Boolean words have the pattern’s length, the coefficient is the product "
                    + "of their local coefficients.")),
                    Paragraph(Text(
                    "Split a pattern at the site to be deleted. In the two remaining words, "
                    + "the prefixes before that site have the corresponding prefix length. "
                    + "Reinsert zero in both words and then reinsert one. The two integer "
                    + "coefficients sum to zero. At the deleted site, the local diagonal "
                    + "coefficients are opposites. Reinstating each earlier site multiplies "
                    + "both by the same sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-deletion-signed-tensor-witness"),
                DeclarationHandle.Create(Owner + ".actualEntry"), H("A nonzero entry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite pattern, choose the indicated ordered bits at differing "
                    + "positions and zero in both words at agreement positions. Every local "
                    + "coefficient is +1, so the resulting coefficient is +1."))),
                DescribeRole.Theorem))));
}
