using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReverseOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReverseOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical purified overlaps for the two explicit recovery channels.",
        H("Actual Kraus overlaps"),
        Blocks(
            Paragraph(Text("The recovered density matrix applies the amplified composite Kraus operators to the canonical maximally entangled purification of the maximally mixed qubit. Both original twelve-dimensional environment label sets occur in the composite, with a bijective finite reindexing.")),
            Entry("overlap", "purification_overlap", "Purification and Kraus sums",
                "The canonical purification overlap equals the sum of squared moduli of one-half the traces of the actual composite Kraus matrices. This is derived from the amplified map; the trace formula is not an assumption."),
            Entry("channels", "recovery_channels", "Normalized recovery channels",
                "The literal source-row construction and the environment-slice construction both define completely positive, trace-preserving channels on the six-dimensional physical output."),
            Entry("comparison", "canonical_overlap_gap", "A strict canonical overlap gap",
                "For the fixed radical rotation, the source-row recovery has strictly smaller canonical purified overlap than the slice recovery, whose overlap is 27/31. The proof uses the exact polynomial certificate. Identifying the slice recovery with ordinary Petz and identifying all padded source SVD completions remain additional obligations; this comparison alone does not assert a resolution of Burri's question."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
