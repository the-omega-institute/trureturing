using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class GrayGridComponentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized Gray point-line incidence support has exact size, actual "
            + "induced regularity and balance in Huang's fixed Boolean cube signing.",
        H("The generalized Gray incidence support"),
        Blocks(
            Paragraph(Text(
                "Arrange the d squared coordinates in the literal row-major grid "
                    + "finProdFinEquiv(row,column). A point has precisely one FALSE "
                    + "coordinate in every row. A line has one empty FALSE row and "
                    + "precisely one FALSE coordinate in every other row. Their union "
                    + "is a finite subset of the actual Boolean cube, and adjacency "
                    + "is induced from that cube. The construction is the standard "
                    + "generalized Gray incidence object supplied for the study of "
                    + "Hong–Wu–Xia, Graph Sensitivity of Cartesian Products with "
                    + "Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . "
                    + "For d=3 the proved size formula evaluates to 54. The separate "
                    + "grid-wedge support has 72 vertices at d=3 and is not the support "
                    + "constructed here. Neither the original f2(Q9) problem, E15, "
                    + "nor a universal Gray classification is resolved.")),
            Describe.Lean(
                DescribeId.Create("gray-grid-pattern"),
                DeclarationHandle.Create(Prefix + "mem_support_iff"),
                H("Exact FALSE-row membership"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d and every Boolean vertex x, membership in "
                        + "support d is equivalent to the disjunction of pointPattern x "
                        + "and linePattern x. The FALSE-row finset is the existing gridRow "
                        + "applied to the Boolean complement of x. Point data are functions "
                        + "Fin d to Fin d. Line data are a missing row b together with "
                        + "a choice of column on the subtype of rows different from b. "
                        + "The proof constructs the data from the row patterns and proves "
                        + "equality using the existing gridRow_ext."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gray-grid-cardinality"),
                DeclarationHandle.Create(Prefix + "card_support"),
                H("Two equally sized incidence layers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d at least one, (support d).card = 2*d^d. "
                        + "Both encodings are injective, and the layers are disjoint "
                        + "because the missing row of a line is empty and every point "
                        + "row is a singleton. Points number d^d. Lines number "
                        + "d*d^(d-1), equal to d^d for d positive. The subtype count "
                        + "retains the empty function domain at d=1, so the zero exponent "
                        + "and uniqueness of the missing row require no exception."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gray-grid-actual-degree"),
                DeclarationHandle.Create(Prefix + "component_regular"),
                H("Exactly d actual selected neighbors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d, componentGraph d is regular of degree d. "
                        + "A point flip stays selected exactly when it removes that "
                        + "row's unique FALSE coordinate; the resulting line has that "
                        + "row missing. A line flip stays selected exactly when it "
                        + "inserts a FALSE coordinate into the missing row; the result "
                        + "is a point. A second FALSE coordinate in a row violates the "
                        + "row-cardinality bound, and deleting from another singleton "
                        + "row creates a second empty row. The full actual cube neighbor "
                        + "set is in bijection with these legal coordinate flips, and "
                        + "each of the two legal-flip sets is in bijection with Fin d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gray-grid-huang-switching"),
                DeclarationHandle.Create(Prefix + "support_isSwitching"),
                H("Balance in the original Huang signing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d, switching d is an IsSwitching function "
                        + "on support d. Its value is +1 at every point, and (-1)^b "
                        + "at a line whose unique missing row has index b. The proof "
                        + "reuses Huang's matrix_flip_zero and matrix_flip_succ to "
                        + "derive the product of -1 over earlier FALSE coordinates. "
                        + "At the edge deleting the FALSE in row b, precisely the "
                        + "single FALSE coordinate of each preceding row contributes. "
                        + "There are no earlier FALSE coordinates within row b, so "
                        + "the actual matrix entry is (-1)^b. Symmetry handles the "
                        + "reverse edge. This uses TRUE in the first recursive matrix "
                        + "block, hence the FALSE-prefix convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gray-grid-comparison-object"),
                DeclarationHandle.Create(Prefix + "gray_component"),
                H("The complete finite comparison object"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every d at least one, support d has size 2*d^d, its actual "
                        + "induced cube graph is regular of degree d, and it is "
                        + "IsBalanced in the existing Huang matrix. The explicit "
                        + "switching function witnesses balance. These conclusions "
                        + "supply a comparison object for later reconstruction, with "
                        + "no assertion of uniqueness or classification."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth"))
        ]));
}
