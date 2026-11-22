using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class DiagonalRecordCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Recovery/DiagonalRecordCapacity.";

    private static readonly LibraryNoteRef Galke =
        LibraryNoteRef.Create("D5/L/QuantumChannels/galke2023renyisufficiency");
    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/QuantumChannels/kato2025exactlocalcompression");
    private static readonly LibraryNoteRef KoashiImoto =
        LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct likelihood vectors give the exact quantum memory dimension of a diagonal experiment.",
        H("Quantum memory for a finite diagonal experiment"),
        Blocks(
            Paragraph(Text(
                "The experiment consists of a reference probability law on a finite basis and a family of "
                + "comparison laws supported on it. At each positive reference coordinate, record the vector "
                + "of comparison weights divided by the reference weight. The count is finite even when "
                + "the comparison family is indexed by an infinite type. The two-state likelihood decomposition "
                + "appears in Galke, van Luijk and Wilming, Appendix B. Kato's equation (62) gives the "
                + "equivalent posterior count for classical bipartite experiments.")),
            Describe.Lean(
                DescribeId.Create("sharp-recovery-dimension"),
                DeclarationHandle.Create(Prefix + "sharp_recovery_dimension"),
                H("Exact dimension for common physical recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Galke, Kato, KoashiImoto),
                Blocks(Paragraph(Text(
                    "Measure in the diagonal basis after decoding. The resulting stochastic kernel fixes "
                    + "the reference and every comparison law. Expanding the reference-weighted squared "
                    + "change in one likelihood ratio gives zero, so a positive transition stays inside "
                    + "the same likelihood class. Pulling the class measurement back through the decoder "
                    + "gives a perfect class measurement on the memory. The finite quantum measurement "
                    + "capacity theorem bounds the number of classes by the memory dimension. Recording "
                    + "the class in an orthogonal basis and preparing the reference law conditional on "
                    + "that class gives physical channels attaining the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-entropy-dimension"),
                DeclarationHandle.Create(Prefix + "sharp_entropy_dimension"),
                H("Exact dimension for fixed-reference entropy preservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Galke, Kato),
                Blocks(Paragraph(Text(
                    "The support-aware Petz equality theorem supplies one recovery channel constructed "
                    + "from the encoder and the reference. It recovers every comparison law whose "
                    + "Umegaki relative entropy is preserved. Conversely, applying data processing to "
                    + "the encoder and decoder gives equality for every comparison. The dimension "
                    + "bound and its attainment thus hold for arbitrary CPTP encoders."))),
                DescribeRole.Theorem))));
}
