using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class ThinSliceGrayReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty actual Huang-balanced induced cubic support in Q9 with a coordinate-zero half "
            + "of size at most sixteen is a cube-symmetry image of the genuine Gray incidence support.",
        H("Reconstruction from the actual thin coordinate half"),
        Blocks(
            Paragraph(Text(
                "Q9 denotes Fin 9 to Bool, flip is BalancedCriticalSpectrum.flip, and H is the "
                    + "fixed Huang matrix from HypercubeSubQuorum. C is the original finite support; "
                    + "its graph is induced by actual cube adjacency. Balanced means IsBalanced C "
                    + "for that fixed signing. coordinateSlice C b filters C by x(0)=b. The "
                    + "symbol GraySupport(d) abbreviates GrayGridComponent.support d; its FALSE coordinates "
                    + "encode one selected position per row for points, and one empty row with "
                    + "one selected position in each other row for lines. Both equivalences in "
                    + "the conclusion are total: g acts on all cube vertices and p on all nine "
                    + "coordinates. The theorem assumes no face, coordinate labels, sign gauge, "
                    + "Gray normal form or connectedness of the original support.")),
            Describe.Lean(
                DescribeId.Create("thin-slice-gray-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction.thin_slice_gray_reconstruction"),
                H("Thin half determines the entire original support"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each C, its nonemptiness, induced degree-three regularity and Huang "
                            + "balance, each Boolean b and the bound on that actual coordinate-zero "
                            + "half imply the displayed two equivalences, flip intertwining and "
                            + "exact finite-set image equality. ThinCoordinateSlice supplies an "
                            + "actual fifteen-vertex K3,3 once-subdivision; CubicalSubdivisionRigidity "
                            + "supplies six injective star directions and all its vertices. Taking "
                            + "O to be X flipped in direction d(false,0) writes the branches as "
                            + "O flipped once and the middles as O flipped in one direction from "
                            + "each triple. Every direction avoids coordinate zero: each occurs "
                            + "on an actual branch-middle edge within the fixed half. Thus O(0)=b.")),
                    Paragraph(Text(
                        "The standard origin has its only FALSE entry at coordinate eight. "
                            + "The point and line definitions prove that the entire Gray half "
                            + "x(8)=FALSE consists of the six first-two-row branches and nine "
                            + "middles. Equiv.Perm.exists_extending_pair extends the two injective "
                            + "maps from Option(Bool times Fin 3): the six standard directions "
                            + "map to the six actual directions, and coordinate eight maps to "
                            + "zero. Coordinate permutation followed by Boolean translation maps "
                            + "the standard origin to O, intertwines every flip and identifies "
                            + "the two whole ambient coordinate halves.")),
                    Paragraph(Text(
                        "GrayGridComponent.support_isSwitching and component_regular, together "
                            + "with BalancedCriticalSpectrum.ambient_eigenvector, give the full "
                            + "Gray eigenvector of eigenvalue three. HuangCubeCovariance constructs "
                            + "the signed pushforward w(y)=theta(g inverse(y)) zGray(g inverse(y)); "
                            + "theta is evaluated in the old coordinates. Both switchings on the "
                            + "common slice multiply along each edge to its actual Huang coefficient. "
                            + "Their product is constant along those edges. The explicit incidence "
                            + "paths from A0 through M0j to Bj, then through Mi0 to Ai, then to Mij "
                            + "propagate a single unit scalar c across the fifteen vertices. "
                            + "The zero extensions therefore satisfy zC=c w on the entire half, "
                            + "including all vertices outside that slice support.")),
                    Paragraph(Text(
                        "The consumed private uniqueness argument uses full eigen-equations "
                            + "with the same eigenvalue. At a vertex in the known half, all "
                            + "same-half neighbor differences vanish. Reindexing the actual matrix "
                            + "row by coordinate flips leaves only the cut-edge coefficient times "
                            + "the opposite-half difference. That coefficient has square one, so "
                            + "the difference vanishes. This identifies both full eigenvectors. "
                            + "Their unit nonzero values recover exact equality of the original "
                            + "support and the image Gray support."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This conditional structural theorem is motivated by Hong, Wu and Xia, "
                    + "Graph Sensitivity of Cartesian Products with Matched Bridges, "
                    + "arXiv:2610.09483v1, Section 7 Problem 2, "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . The original f2(Q9)=3-or-4 "
                    + "question, E15, classification of arbitrary balanced components and the "
                    + "full 258-point obstruction remain unresolved. No novelty or priority "
                    + "claim is made."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));

    private static Formula ReconstructionFormula()
    {
        Formula c = F.Id("C"), b = F.Id("b"), g = F.Id("g"), p = F.Id("p");
        Formula x = F.Id("x"), i = F.Id("i");
        var cube = Call("Q", D(9));
        var coordinates = Call("Fin", D(9));
        var flipLaw = All("x", cube, All("i", coordinates,
            Eqn(At(g, Call("flip", x, i)), Call("flip", At(g, x), At(p, i)))));
        var image = Eqn(c, Call("image", Call("GraySupport", D(3)), g));
        var result = Exists("g", Call("Equiv", cube, cube),
            Exists("p", Call("Equiv", coordinates, coordinates), And(flipLaw, image)));
        var small = new Formula.Relation(Call("card", Call("coordinateSlice", c, b)),
            FormulaRelationOperator.LessThanOrEqual, D(1, 6));
        return Disp(All("C", Call("Finset", cube),
            Implies(Call("Nonempty", c),
                Implies(Call("IsRegularOfDegree", Call("induce", Call("hypercube", D(9)), c), D(3)),
                    Implies(Call("IsBalanced", c), All("b", Call("Bool"), Implies(small, result)))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
