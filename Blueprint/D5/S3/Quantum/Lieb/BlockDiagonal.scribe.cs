using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class BlockDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hilbert-space block operators used in the transplanted Jensen proof.",
        H("BlockDiagonal"),
        Blocks(
            Paragraph(Text("This module is a consumed supporting source transplant for the "
                + "strictly positive, interior-exponent Lieb joint trace concavity endpoint. "
                + "Its definitions and proof steps come from Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki's Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. The Lean file records the exact "
                + "original module and retained supplier license. No mathematical originality "
                + "is claimed.")),
            Paragraph(Text("The consumed endpoint and its precise positive-definite and "
                + "interior-exponent scope are described in the LiebConcavity blueprint. "
                + "Retirement is triggered by an equivalent consumed declaration in this "
                + "repository's pinned Mathlib. This supporting module does not assert the "
                + "singular PSD extension, closed exponent endpoints or trace-exponential consequence.")))));
}
