using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-ones input block accounts for the entire entropy deficit of the paired law.",
        H("Entropy of the Paired Edge Record Law"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-paired-weight-entropy"),
                DeclarationHandle.Create(Module + ".pairedWeight_entropy"),
                H("Exact entropy of the paired weights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Write d = 2ᴺ for a path of N sites. Divide the channel kernel by d to give "
                    + "the joint input-output weights under a uniform input. Every input row but "
                    + "the all-ones row has entries 1/d². The all-ones row has d/2 entries of "
                    + "weight 2/d² and d/2 zeros. The entropy is 2 log d − (log 2)/d in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-cmi-profile"),
                DeclarationHandle.Create(Module + ".pairedCMI_profile"),
                H("The paired entropy profile gives an exact CMI"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "A proper mask of s sites has paired entropy 2s log 2. In the CMI combination "
                    + "for pairwise disjoint L, M, R, the size terms cancel. The full-mask deficit "
                    + "contributes only when the union is the whole path and both outer regions "
                    + "are nonempty. In that case the CMI is (log 2)/d."))),
                DescribeRole.Theorem))));
}
