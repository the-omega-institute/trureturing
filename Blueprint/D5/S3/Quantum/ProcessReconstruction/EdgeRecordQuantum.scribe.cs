using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordQuantumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The edge record channels have maximally mixed proper paired windows and an exact Choi CMI profile.",
        H("Normalized Choi States of the Edge Record Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-choi-diagonal"),
                DeclarationHandle.Create(Module + ".choi_diagonal"),
                H("The reference-first normalized Choi state is diagonal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Apply the channel to the input half of the normalized Bell state. "
                    + "The matrix unit entry formula gives the diagonal Choi weights Kᵦ(y|x)/d "
                    + "in reference-output order, where d = 2ᴺ and N is the number of sites."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-proper-output-replacer"),
                DeclarationHandle.Create(Module + ".proper_output_replacer"),
                H("Every proper output reduction is a mixed replacer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Retaining any proper set of output sites yields the maximally mixed state "
                    + "times the trace of the full input matrix. This equality holds on the "
                    + "full matrix algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-proper-paired-mixed"),
                DeclarationHandle.Create(Module + ".proper_paired_mixed"),
                H("All proper paired Choi windows are maximally mixed"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Keep each selected input reference with its corresponding output. Each "
                    + "proper set of s paired sites gives the identity divided by 4ˢ, for either "
                    + "channel. This holds for every proper subset and hence for every contiguous "
                    + "window of width less than N, uniformly in the window and path size."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-exact-choi-cmi"),
                DeclarationHandle.Create(Module + ".choi_pairedCMI"),
                H("Exact conditional mutual information of paired sites"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The full normalized Choi entropy is 2 log d − (log 2)/d. For pairwise "
                    + "disjoint L, M, R, the paired CMI is (log 2)/d if their union is full "
                    + "and both L and R are nonempty. It is zero in every other case."))),
                DescribeRole.Theorem))));
}
