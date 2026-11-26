using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingWeldOrientationLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform undirected weld completions and their orientations.",
        H("An oriented lift of an alternating weld"),
        Blocks(Describe.Lean(
            DescribeId.Create("alternating-weld-orientation-law"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw.alternating_weld_orientation_law"),
            H("The conditional law given the orientation of the observed edges"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a prescribed simple graph F on a finite vertex set of at least three "
                    + "vertices with two colors. Assume F extends to an alternating undirected "
                    + "full cycle. The uniform law on alternating oriented lifts projects to "
                    + "the uniform law on the undirected completions of F.")),
                Paragraph(Text(
                    "In each lift the prescribed orientation has as many directed edges "
                    + "as F has undirected edges. Given a prescribed orientation of positive "
                    + "mass, the directed full cycle is uniform over the alternating cycles "
                    + "extending that orientation. Its inclusion into the original lift space "
                    + "retains the prescribed orientation and the full successor permutation.")),
                Paragraph(Text(
                    "First use the uniform law on all undirected completions and their lifts. "
                    + "Alternation of the permutation is equivalent to alternation of its "
                    + "undirected graph, so restricting both laws to that event preserves the "
                    + "projection. Each directed prescribed edge projects to one undirected "
                    + "edge of F, and the lift gives each such edge exactly one direction. "
                    + "The fiber over a prescribed orientation is in bijection with the "
                    + "directed alternating completion space. Uniformity on that fiber gives "
                    + "the conditional law."))),
            DescribeRole.Theorem))));
}
