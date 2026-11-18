using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class AdjacentLayerRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual Huang-balanced induced cubic 54-support in Q9 confined to two adjacent occupied layers is a genuine Gray-support cube image.",
        H("Rigidity of adjacent occupied layers in Q9"),
        Blocks(
            Paragraph(Text(
                "Q9 is Fin 9 to Bool, occupied x is the literal TRUE-coordinate support, and "
                    + "the hypotheses refer to the original finite support C, its induced cube graph "
                    + "and the fixed Huang balance. The layer condition is imposed on the supplied "
                    + "support itself; no graph, congruence or coordinate labeling is assumed.")),
            Describe.Lean(
                DescribeId.Create("adjacent-layers-gray-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity.adjacent_layers_gray_reconstruction"),
                H("Adjacent layers force Gray reconstruction"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The literal occupied-face image transfers actual cube adjacency to a finite "
                            + "face family. Cubic bipartite handshake gives 27 faces in each of the two "
                            + "layers. Huang's actual exterior zero-flow parity makes every unselected "
                            + "(r-1)-face degree even and every unselected (r+1)-face incidence even, "
                            + "while selected upper faces have incidence three. The ordered distinct-pair "
                            + "intersection/union bijection and Finset.offDiag_card give the exact pair "
                            + "double count. Reduction in ZMod 8 gives 54r congruent to 324 modulo 8, hence r congruent to 2 modulo 4; "
                            + "the bounds 2 ≤ r ≤ 6 then give r=2 or r=6.")),
                    Paragraph(Text(
                        "For r=2 the selected pairs form an actual coordinate graph. Selected triples are "
                            + "exactly its triangles; an unselected triple cannot have one selected pair, "
                            + "by the same actual exterior parity. Every edge has three common neighbors. "
                            + "Thus adjacent degrees sum to twelve, every nonisolated vertex lies in a "
                            + "triangle, and degree sums on the three triangle edges force every coordinate "
                            + "degree to be six. Incidence counting gives nine selected triples through each "
                            + "coordinate, hence the literal TRUE half has 6+9=15 vertices. For r=6 the "
                            + "same unsigned incidence argument is applied after taking actual complements, "
                            + "giving fifteen vertices in the literal FALSE half.")),
                    Paragraph(Text(
                        "The existing ThinSliceGrayReconstruction theorem is then applied unchanged to "
                            + "that actual coordinate half. The result supplies total equivalences of Q9 and "
                            + "Fin9, intertwines every actual flip with the coordinate permutation, and gives "
                            + "exact equality with GrayGridComponent.support 3. This proves only the adjacent "
                            + "layer theorem; the original universal 54-support problem, E15, threshold19 and "
                            + "the 258-point obstruction remain outside this statement."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The external anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with "
                    + "Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . No literature priority or "
                    + "resolution of that original open problem is claimed."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth"))
        ]));

    private static Formula ReconstructionFormula()
    {
        Formula c = F.Id("C"), r = F.Id("r"), g = F.Id("g"), p = F.Id("pi");
        Formula x = F.Id("x"), i = F.Id("i");
        var cube = Call("Q", D(9));
        var coordinates = Call("Fin", D(9));
        var flipLaw = All("x", cube, All("i", coordinates,
            Eqn(At(g, Call("flip", x, i)), Call("flip", At(g, x), At(p, i)))));
        var image = Eqn(c, Call("image", Call("GraySupport", D(3)), g));
        var result = Exists("g", Call("Equiv", cube, cube),
            Exists("pi", Call("Equiv", coordinates, coordinates), And(flipLaw, image)));
        var hcard = Eqn(Call("card", c), D(5, 4));
        var occupied = Call("occupied", x);
        var hband = All("x", cube, Implies(Member(x, c),
            Or(Eqn(Call("card", occupied), r), Eqn(Call("card", occupied), Add(r, D(1))))));
        return Disp(All("C", Call("Finset", cube),
            Implies(Call("Nonempty", c),
                Implies(Call("IsRegularOfDegree", Call("induce", Call("hypercube", D(9)), c), D(3)),
                    Implies(Call("IsBalanced", c), Implies(hcard,
                        All("r", Call("Nat"), Implies(hband, result))))))));
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Or, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
