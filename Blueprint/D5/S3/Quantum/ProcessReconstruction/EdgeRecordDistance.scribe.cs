using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordDistanceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform paired Choi CMI decay coexists with maximal diamond separation and an exact-data minimax lower bound.",
        H("Diamond Reconstruction Limits for Edge Record Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-uniform-choi-cmi-decay"),
                DeclarationHandle.Create(Module + ".choi_pairedCMI_decay"),
                H("A uniform bound in the middle region size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "For either channel and any pairwise disjoint regions L, M, R, "
                    + "the paired Choi CMI in nats is at most (log 2) exp(−(log 2)|M|). "
                    + "The prefactor and decay length in Liu–Wild Definition 1 are log 2 and "
                    + "1/log 2, independent of the path length."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-choi-trace-norm"),
                DeclarationHandle.Create(Module + ".choi_traceNorm"),
                H("The normalized Choi trace norm difference is 2/d"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The Choi states differ only at the all-ones reference word. The two "
                    + "opposite parity blocks there have disjoint supports and each has mass "
                    + "1/d, where d = 2ᴺ. Their unhalved trace norm difference is 2/d."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-product-probe-parity"),
                DeclarationHandle.Create(Module + ".product_probe_parity"),
                H("The all-ones product probe distinguishes the pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "One call on the all-ones computational product input followed by a global "
                    + "output parity measurement returns the channel bit with probability one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-maximal-diamond"),
                DeclarationHandle.Create(Module + ".maximal_diamond"),
                H("The unhalved diamond distance is 2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The all-ones product input gives output trace norm difference 2, attaining "
                    + "the universal upper bound on the unhalved diamond distance between channels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-paired-data-minimax"),
                DeclarationHandle.Create(Module + ".pairedData_minimax"),
                H("Any exact proper paired data estimator incurs diamond error at least 1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "On each finite path the two channels give the same family of exact proper "
                    + "paired marginals, so every channel-valued function of the entire family "
                    + "returns one common estimate. The maximum of its two unhalved diamond "
                    + "errors is at least 1. This bound also applies to data restricted to "
                    + "proper windows of any fixed width smaller than the path."))),
                DescribeRole.Theorem))));
}
