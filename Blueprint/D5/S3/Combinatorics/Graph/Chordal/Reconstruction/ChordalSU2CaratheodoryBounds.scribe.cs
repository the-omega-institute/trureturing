using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class ChordalSU2CaratheodoryBoundsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Caratheodory caps control round unit-quaternion reconstruction on all finite chordal graphs at small defect and across all defects at clique cutoffs five and six.",
        Blocks(
            Result("exists-su2-gain-potential-caratheodory", "exists_su2_gain_potential_caratheodory", "Small defects at arbitrary clique number",
                "For every finite chordal graph and every nonnegative defect budget through arcsine of the square root of 5 over 12, the edge error is bounded by twice arcsine of the product of the square root of 3 over 2 and the sine of the budget.",
                "The minimum-norm point of each spherical convex hull has a representation by at most four points in its supporting hyperplane. The normalized centers transport along breadth-first layers, and an inner-product estimate controls the edges within each layer."),
            Result("exists-cliqueFive-su2-gain-potential-caratheodory", "exists_cliqueFive_su2_gain_potential_caratheodory", "Global clique-five coefficient",
                "A graph with cliques of size at most five admits the uniform coefficient pi over arccosine of one third, which is strictly below eight thirds.",
                "The small-defect radius is convex on the relevant interval. At the crossover it matches the closed hemisphere fit available from four insertion candidates."),
            Result("exists-cliqueSix-su2-gain-potential-cap", "exists_cliqueSix_su2_gain_potential_cap", "Clique-six spherical cap",
                "A graph with cliques of size at most six admits a fit at radius arccosine of negative one quarter, for every skew gain assignment.",
                "Five points on the unit quaternion sphere admit this cap. A supporting hyperplane or a facet of their convex hull supplies its center. Reverse simplicial elimination uses this cap at each vertex."),
            Result("exists-cliqueSix-su2-gain-potential-caratheodory", "exists_cliqueSix_su2_gain_potential_caratheodory", "Global clique-six coefficient",
                "A graph with cliques of size at most six admits the uniform coefficient twice arccosine of negative one quarter over arccosine of one sixth, which is strictly below thirteen fifths.",
                "At the largest defect in the small-defect theorem, the radius equals the constant cap bound. The secant inequality and the cap then cover the full defect range."))));

    private static DocumentBlock.Describe Result(string id, string declaration, string heading,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);
}
