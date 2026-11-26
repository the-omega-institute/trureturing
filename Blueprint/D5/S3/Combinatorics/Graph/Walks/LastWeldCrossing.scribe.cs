using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class LastWeldCrossingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A meeting witness decomposes at its last edge outside the fixed forest.",
        H("The last weld crossing of two meeting paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("meeting-arms-last-weld"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Walks/LastWeldCrossing.meeting_arms_last_weld"),
                H("The tail after the last crossing has length equal to the forest distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a fixed acyclic graph and a weld graph on the same vertex set. "
                        + "Two paths in their union run from the same start to the same end. "
                        + "Their total length is positive, and their final edges differ "
                        + "whenever both exist. Follow the first path and return along the "
                        + "second in reverse.")),
                    Paragraph(Text(
                        "The resulting walk has an edge of the weld graph outside the fixed "
                        + "forest. At the last such edge, take the suffix starting from its "
                        + "arrival vertex. This suffix has the same vertex list as a simple "
                        + "path in the fixed forest. Its length is the full walk length minus "
                        + "the number of steps through the crossing, and equals the forest "
                        + "distance from the arrival vertex back to the common start.")),
                    Paragraph(Text(
                        "The final-edge condition rules out immediate reversal at the join. "
                        + "In a forest a nonbacktracking walk is a path, so a nonempty closed "
                        + "walk with this condition must leave the forest. Taking the greatest "
                        + "index of an edge outside the forest leaves an entirely fixed suffix. "
                        + "It remains nonbacktracking and is thus the unique path between "
                        + "its endpoints in the forest."))),
                DescribeRole.Theorem))));
}
