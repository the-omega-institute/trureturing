using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class NineteenPointSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty actual Huang-balanced induced cubic Q9 support with a coordinate-zero "
            + "slice of size at most nineteen is a total cube-symmetry image of Gray support3.",
        H("Gray reconstruction through the nineteen-point threshold"),
        Blocks(
            Paragraph(Text(
                "Q9 is Fin 9 to Bool, flip is BalancedCriticalSpectrum.flip, and C is the original "
                    + "finite support with its actual induced cube graph and the fixed Huang signing. "
                    + "coordinateSlice C b is the coordinate-zero filter. GraySupport(d) means "
                    + "GrayGridComponent.support d. The two equivalences in the conclusion act on "
                    + "the entire cube and all nine coordinates. This conditional classification "
                    + "assumes no Gray normal form, supplied path certificate or connectedness.")),
            Describe.Lean(
                DescribeId.Create("nineteen-point-slice-gray-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice.nineteen_point_slice_gray_reconstruction"),
                H("Reconstruction from an actual slice of at most nineteen vertices"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The eighteen-point theorem handles every smaller slice. At nineteen "
                            + "vertices, the actual degree-two count is nine or eleven. Two depth-three "
                            + "trees about a high-high edge are disjoint by the girth-eight path "
                            + "argument. Each high first neighbor increases their lower bound by one. "
                            + "With eleven low vertices, there are only eight high vertices and at most "
                            + "two high vertices having a high neighbor. The roots account for those "
                            + "two; the tree layers then leave too few positions for all eight highs.")),
                    Paragraph(Text(
                        "With nine low vertices, high-high incidences force a high vertex with two "
                            + "high neighbors. Equality in the nineteen-point tree count fixes all "
                            + "vertices. Its remaining incidences yield six cycle branch vertices, "
                            + "six cycle middles and three opposite matching middles, forming an "
                            + "induced once-subdivision of K3,3. A selected center has a two-edge "
                            + "cube path to each of the three matching middles.")),
                    Paragraph(Text(
                        "Cubical subdivision rigidity gives an origin O and six distinct directions. "
                            + "The matching middles differ from O on three disjoint coordinate pairs "
                            + "P_i. If D is the differing-coordinate set between the selected center "
                            + "and O, each distance bound gives card(D) at most twice card(D intersect "
                            + "P_i). Summing gives three times card(D) at most twice card(D), so the "
                            + "center equals O. All six branch vertices are then selected neighbors "
                            + "of the center, contradicting its degree at most three. Only the "
                            + "two-edge paths are used; no degree assumption on their bridges is needed.")),
                    Paragraph(Text(
                        "The result is a conditional reconstruction for the displayed actual slice "
                            + "bound. It does not establish the original external Q9 classification "
                            + "for arbitrary support or the full 258-point obstruction."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceMatching"))
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
            FormulaRelationOperator.LessThanOrEqual, D(1, 9));
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
