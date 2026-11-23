using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class QutritDiagonalResetDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary decoder after a plane-preserving diagonal reset has a matched Bell block "
        + "that dominates an explicitly attainable nonnegative block entry by entry.",
        H("Matched Bell comparison for diagonal-reset qutrit compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qutrit-diagonal-reset-bell-comparison"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset.diagonal_reset_bell_comparison"),
                H("An actual channel attains the matched block bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "The source is the normalized qutrit Bell state. The reference factor stays untouched, "
                    + "and a fixed encoder and decoder communicate solely through the qubit. "
                    + "The encoder acts identically on the first two levels, erases their coherences with "
                    + "the third level, and resets that level to a diagonal memory state. "
                    + "The matched block consists of the real parts of the joint state difference "
                    + "on the three vectors |ii>, multiplied by three. Order the kept levels so that "
                    + "the less reliably matched level is second, and let x be the square root of its "
                    + "matched output probability. Choi positivity bounds the real matched coherence "
                    + "by the product of the square roots of the two matched probabilities. Trace "
                    + "preservation bounds the probability sent to the discarded level from either kept "
                    + "level by one minus that level's matched probability. "
                    + "The resulting lower matrix has diagonal (0, 1 - x squared, x squared) "
                    + "and upper off-diagonal entries (1 - x, 1, 1). Resetting to the second level "
                    + "and using the two-Kraus decoder with amplitudes x and the square root of "
                    + "one minus x squared gives exactly this matched block."))),
                DescribeRole.Theorem))));
}
