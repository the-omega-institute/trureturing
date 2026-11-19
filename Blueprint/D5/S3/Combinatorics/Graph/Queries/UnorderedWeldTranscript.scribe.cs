using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class UnorderedWeldTranscriptDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conditional law of an alternating weld after complete neighborhood queries.",
        H("Conditioning on a transcript of the welded graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("unordered-weld-transcript-law"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript.weld_transcript_law"),
            H("A transcript specifies exactly the revealed weld edges"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the finite vertex set have n vertices of each color, with n at least two. "
                    + "The hidden graph is a uniformly chosen undirected alternating full cycle. "
                    + "A deterministic adaptive protocol queries complete unordered neighbor sets "
                    + "in the union of the hidden cycle and a fixed graph.")),
                Paragraph(Text(
                    "Consider the transcript of a reference cycle disjoint in edges from the "
                    + "fixed graph. From all edges recorded in the transcript, remove the fixed "
                    + "edges to obtain a graph F. A candidate cycle gives the reference transcript "
                    + "exactly when it contains F. The probability of the transcript is the number "
                    + "of such completions divided by n! times (n - 1)! divided by two. At positive "
                    + "transcript mass, the conditional law is uniform over those completions.")),
                Paragraph(Text(
                    "A replay must include each observed edge outside the fixed graph. Conversely, "
                    + "a candidate containing F supplies all observed edges after taking the union. "
                    + "Its degree after adding the fixed edges is bounded above by the reference "
                    + "degree because the reference adds two distinct edges outside the fixed graph "
                    + "at each vertex. The complete-neighborhood replay theorem then gives equality "
                    + "of the two transcripts."))),
            DescribeRole.Theorem))));
}
