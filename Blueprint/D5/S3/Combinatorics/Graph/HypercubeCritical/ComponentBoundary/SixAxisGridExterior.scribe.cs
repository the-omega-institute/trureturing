using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class SixAxisGridExteriorDocument : IScribeDocumentDefinition
{
    private const string Parent = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Module = Parent + "ComponentBoundary/SixAxisGridExterior";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exterior lifts of the six-axis cubical grid",
        H("Joint restrictions on continuation directions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("six-axis-grid-selected-lift-labels"),
                DeclarationHandle.Create(Module + ".selectedLiftLabels"),
                H("Selected lifts in one row and one column"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a middle indexed by i and j and a flip direction e. A false label k "
                    + "tests the lift of middle (k,j), and a true label k tests the lift of "
                    + "middle (i,k). The filter keeps exactly the labels whose lifts belong to "
                    + "the ambient support. The central lift, when selected, contributes both "
                    + "its incident labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("six-axis-grid-exterior-lift-direction-exclusion"),
                DeclarationHandle.Create(Module + ".exterior_lift_direction_exclusion"),
                H("Axes excluded by lifts in the same exterior direction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let an injectively labelled six-axis grid lie in a balanced cube support. "
                        + "Fix a selected middle lift "
                        + "along an axis e outside the six grid axes. Its selected-neighbor "
                        + "directions are disjoint from the image of the selected lift labels. "
                        + "On its column this excludes the false axis of each selected lift, "
                        + "and on its row it excludes the true axis of each selected lift.")),
                    Paragraph(Text(
                        "At the central lift, either incident flip commutes past e and cancels "
                        + "the corresponding flip from the branch to the middle. The branch, "
                        + "the middle, and their two e-lifts would form a selected coordinate "
                        + "square, which balance forbids.")),
                    Paragraph(Text(
                        "Two distinct middles in a common column have a common branch p. Their "
                        + "directions a and b from p are distinct. With both e-lifts selected, "
                        + "a continuation along b from the a-middle lift would give two selected "
                        + "three-step words a,e,b and b,e,a from p to the same point. Balance "
                        + "forces equal first directions, contradicting a and b being distinct. "
                        + "The argument for a common row uses the other branch class.")),
                    Paragraph(Text(
                        "Injectivity counts each excluded label as a distinct axis. The number "
                        + "of selected internal continuation directions is bounded by six minus "
                        + "the number of selected labels, or four minus the number of other "
                        + "selected middles in the row and column using e. The statement holds "
                        + "for every exterior e on the same ambient support.")),
                    Paragraph(Text(
                        "In the singleton-trace branch of Hong–Wu–Xia Problem 2, the rule applies "
                        + "conditionally when the fifteen-point trace is the once-subdivided "
                        + "K3,3 on six coordinate axes. It constrains the possible exterior "
                        + "continuations of that trace. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Parent + "BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Parent + "BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(Parent + "CubicalSubdivisionRigidity"))
        ]));
}
