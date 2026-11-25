using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordQueryBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBridge";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hidden-input oracles are the edge-record channels after site-local input bit flips.",
        H("Query Hardness of Product-Environment Path Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-marked-pushforward"),
                DeclarationHandle.Create(Module + ".markedMass_eq_push"),
                H("The original uniform edge and site records give the marked row law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Translate the input word x to x + (allOn − a). Only the marked word a "
                    + "becomes all ones. The original local record map produces the uniform "
                    + "law on the parity-b fiber at a and the full uniform law elsewhere."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-marked-channel-equality"),
                DeclarationHandle.Create(Module + ".markedChannel_eq_activatedChannel"),
                H("The hidden-input oracle equals the translated path channel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The equal row laws identify the prepared density states, giving equality "
                    + "of the two CPTP maps."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-marked-environment-trace"),
                DeclarationHandle.Create(Module + ".trace_activatedDilation"),
                H("The translated record isometry realizes the channel on every input matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Permute the input columns of the original isometry by the site-local "
                    + "translation. Its environment partial trace gives the translated channel. "
                    + "In the paper circuit, the translation is one parallel layer of input "
                    + "bit flips before the original ten-layer schedule, with the same "
                    + "pure product environment initialization."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-marked-paired-data"),
                DeclarationHandle.Create(Module + ".activated_properPairedData_eq"),
                H("Every proper paired marginal agrees across all marks and parities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "In the normalized Choi state the translation relabels the input reference "
                    + "indices. The permutation splits across kept and discarded sites, so "
                    + "the original maximally mixed proper marginals are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-marked-cmi-decay"),
                DeclarationHandle.Create(Module + ".activated_pairedCMI_decay"),
                H("The same uniform Choi CMI decay holds throughout the family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The relabeling preserves every paired entropy, including that of the "
                    + "full Choi state. For disjoint L, M, R the CMI therefore obeys "
                    + "(log 2) exp(−(log 2)|M|) throughout the family, in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-path-query-bound"),
                DeclarationHandle.Create(Module + ".activated_query_lower_bound"),
                H("The translated path family requires at least 2ᴺ/3 calls for discrimination"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "One protocol must succeed with probability at least two thirds on each "
                    + "mark and parity. Its probes and CPTP interleavings may use arbitrary "
                    + "finite quantum memory, and the decision may receive the mark after "
                    + "the calls. A known mark can be queried directly in the computational basis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-path-reconstruction-bound"),
                DeclarationHandle.Create(Module + ".activated_reconstruction_query_lower_bound"),
                H("The translated path family requires at least 2ᴺ/3 calls for diamond reconstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The same bound applies when a finite POVM outcome selects a channel "
                    + "estimate and the unhalved diamond error is strictly below one with "
                    + "probability at least two thirds on every member. The accompanying "
                    + "paper algorithm uses O(2ᴺ) channel calls under the family promise."))),
                DescribeRole.Theorem))));
}
