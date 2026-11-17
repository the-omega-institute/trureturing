using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class EighteenPointSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty actual Huang-balanced induced cubic Q9 support with a coordinate-zero "
            + "slice of size at most eighteen is a total cube-symmetry image of Gray support3.",
        H("Gray reconstruction through the eighteen-point threshold"),
        Blocks(
            Paragraph(Text(
                "Q9 is Fin 9 to Bool, flip is BalancedCriticalSpectrum.flip, and C is the original "
                    + "finite support with its actual induced cube graph and the fixed Huang signing. "
                    + "coordinateSlice C b is the coordinate-zero filter. GraySupport(d) means "
                    + "GrayGridComponent.support d. The two equivalences in the conclusion act on "
                    + "the entire cube and all nine coordinates. This conditional classification "
                    + "assumes no Gray normal form, supplied path certificate or connectedness.")),
            Describe.Lean(
                DescribeId.Create("eighteen-point-slice-gray-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice.eighteen_point_slice_gray_reconstruction"),
                H("The actual slice has fifteen vertices and reconstructs the whole support"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every original nonempty C, induced regularity of degree three, original "
                            + "IsBalanced C, Boolean b and the bound on that actual slice imply the "
                            + "displayed flip-intertwining equivalences and exact image equality. "
                            + "The proof first derives that the slice has fifteen vertices. The "
                            + "reviewed ThinSliceGrayReconstruction theorem then supplies the total "
                            + "cube equivalence and coordinate permutation; its cubical rigidity, "
                            + "Huang covariance and full eigenvector reconstruction are reused.")),
                    Paragraph(Text(
                        "The new graph obstruction uses actual finite nonbacktracking paths from "
                            + "both ends of a high-high edge, through depth three and excluding that "
                            + "edge. Same-side endpoint injection follows from the existing girth "
                            + "path lemma. Across the edge, prepend it to the other simple path. "
                            + "A collision produces two distinct paths whose length sum is at most "
                            + "seven. Mathlib extracts a cycle of at most that length, contradicting "
                            + "girth at least eight. Thus the two trees have disjoint vertices. Each "
                            + "root supplies itself, two first vertices, at least two second vertices "
                            + "and at least four leaves. A low first vertex has a high second vertex "
                            + "with two forward neighbors; a high first vertex has two second "
                            + "vertices with at least one forward neighbor each. There are at least "
                            + "eighteen vertices in total.")),
                    Paragraph(Text(
                        "If there are exactly eighteen vertices, the trees cover the graph and "
                            + "both second layers have size two. The degree count forces all four "
                            + "first vertices to be low and therefore the second vertices to be high. "
                            + "With ten independent low vertices there are eight high vertices. "
                            + "The roots and second layers contain at most six of them, so at least "
                            + "two high vertices are leaves. Each has a high parent. The two roots, "
                            + "the two high leaves and one such parent are five distinct high vertices "
                            + "with high neighbors. Double-counting low-high incidences gives "
                            + "2q plus the number of high vertices with high neighbors at most 3h. "
                            + "For q=10 and h=8 that number is at most four, a contradiction. This "
                            + "is the same degree-capacity obstruction expressed as a consumed "
                            + "incidence deficit; it needs no connectedness assumption.")),
                    Paragraph(Text(
                        "For the actual cube slice put q=directionEdges C 0 and N equal to its "
                            + "size. Existing actual-slice results give degrees two or three, q "
                            + "independent low vertices, parity bipartiteness, girth at least eight, "
                            + "6q=|C| and |C| at least 54. Low-high counting gives 5q at most 3N. "
                            + "For N at most eighteen, q is nine or ten. The handshake identity "
                            + "excludes (q,N)=(9,18) and (10,17). Above sixteen, the only remaining "
                            + "cases are (9,17) and (10,18), each with an actual high-high edge. "
                            + "The double-root bound excludes the former and the equality obstruction "
                            + "excludes the latter. The existing fifteen-point slice theorem and "
                            + "genuine Gray reconstruction now apply."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The external anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products "
                    + "with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2, "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . The original f2(Q9)=3-or-4 "
                    + "problem and E15 remain open. This result does not assert that every balanced "
                    + "component admits a slice of size at most eighteen. No literature priority "
                    + "or open-problem resolution is claimed."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound"))
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
            FormulaRelationOperator.LessThanOrEqual, D(1, 8));
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
