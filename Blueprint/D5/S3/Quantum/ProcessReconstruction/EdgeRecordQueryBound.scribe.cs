using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class EdgeRecordQueryBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound";
    private static readonly LibraryNoteRef LiuWild =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/liuwild2026localtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniform-oracle hybrid yields a lower bound for adaptive protocols with arbitrary finite quantum memory.",
        H("Coherent Query Lower Bounds for Hidden Inputs"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-record-hidden-query-bound"),
                DeclarationHandle.Create(Module + ".query_lower_bound"),
                H("Worst-case parity discrimination requires at least 2ᴺ/3 calls"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "Use an arbitrary joint initial state, sequential channel calls and arbitrary "
                    + "CPTP interleavings on the query register and finite memory. The terminal "
                    + "binary measurement may depend on the mark revealed after the last call. "
                    + "Success of at least two thirds at every mark and parity forces T ≥ 2ᴺ/3. "
                    + "Rosenthal et al., Theorem 1.2 and Section 3, use rare input weights "
                    + "for replacement-channel certification."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-record-hidden-reconstruction-bound"),
                DeclarationHandle.Create(Module + ".reconstruction_query_lower_bound"),
                H("Finite-outcome diamond reconstruction requires at least 2ᴺ/3 calls"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LiuWild),
                Blocks(Paragraph(Text(
                    "A finite terminal POVM yields a channel estimate at each outcome. "
                    + "At each member of the family the event of unhalved diamond error "
                    + "strictly below one must have probability at least two thirds."))),
                DescribeRole.Theorem))));
}
