using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordQueryChannelsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryChannels";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary reference sees an exact trace norm error proportional to the probe mass on the hidden word.",
        H("Hidden-Input Channel Action"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-reference-error"),
                DeclarationHandle.Create(Module + ".referenceError_exact"),
                H("The exact change from the uniform reference oracle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "For every joint probe and finite reference, the unhalved trace norm "
                    + "difference between the marked and uniform outputs equals the trace "
                    + "of the probe's positive reference block at the marked input. The "
                    + "channel is a deterministic specialization of Ghosh, Jackson and "
                    + "Datta, Equations (8)–(10)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-hidden-pair-diamond"),
                DeclarationHandle.Create(Module + ".markedPair_diamond"),
                H("Opposite parities at a shared mark have diamond distance two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "The computational probe at the mark attains the maximum unhalved "
                    + "diamond distance. The two open diamond balls of radius one are disjoint."))),
                DescribeRole.Theorem))));
}
