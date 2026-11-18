using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HuangCubeCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual cube equivalence intertwining coordinate flips admits a sign "
            + "gauge whose pushforward commutes with Huang's fixed adjacency matrix.",
        H("Signed covariance of the actual Huang operator"),
        Blocks(
            Paragraph(Text(
                "Q(n) is the actual Boolean cube Fin n to Bool. The symbols flip and "
                    + "huangMatrix denote BalancedCriticalSpectrum.flip and the existing "
                    + "matrix from HypercubeSubQuorum, opened without changing its source. "
                    + "TRUE selects Huang's first recursive block; its directional signs "
                    + "therefore count earlier FALSE coordinates. The equivalences g and p "
                    + "act on vertices and coordinates respectively. Their sole geometric "
                    + "condition is g(flip(x,i)) = flip(g(x),p(i)); there is no assumed "
                    + "gauge, switching normal form, balance condition or positive dimension.")),
            Describe.Lean(
                DescribeId.Create("huang-cube-signed-covariance"),
                DeclarationHandle.Create(Prefix + "exists_signed_covariance"),
                H("A constructed gauge and full operator intertwining"),
                StatementSource.FromAuthor(CovarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural dimension n, every equivalence g of Q(n), "
                            + "and every coordinate equivalence p satisfying the displayed "
                            + "flip law, one sign function s works simultaneously on all "
                            + "actual edges and all real vectors. The signed pushforward "
                            + "at y is s(g inverse(y)) times z(g inverse(y)); thus the gauge "
                            + "is evaluated in old coordinates. The coefficient law is "
                            + "H(g(x),g(flip(x,i))) = s(x) H(x,flip(x,i)) s(flip(x,i)). "
                            + "The last equality is equality of full functions, and uses "
                            + "the existing full matrix mulVec, including every vertex.")),
                    Paragraph(Text(
                        "The proof multiplies the original edge signing by its geometric "
                            + "pullback. Edge-unit squares and reciprocity follow from "
                            + "matrix_sq_of_adj, matrix symmetry and flip involution. "
                            + "Evaluating gamma_anticommute on the constant-one function "
                            + "and applying gamma_apply gives negative square curvature "
                            + "for both signings, so their product is flat. A private "
                            + "dimension induction integrates that ratio: integrate the "
                            + "TRUE layer first and multiply by the head-edge ratio on "
                            + "the FALSE layer. Head-tail flatness supplies every remaining "
                            + "edge. At n=0 the constant-one function suffices. The actual "
                            + "matrix row is then restricted to its cube neighbors and "
                            + "bijectively indexed by coordinate flips. Reindexing those "
                            + "coordinates through p and cancelling s squared proves the "
                            + "operator equation. The construction is on its live proof path."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This algebraic bridge supports reconstruction after thin-slice cube "
                    + "geometry has supplied an actual vertex/coordinate equivalence. "
                    + "The genuine generalized Gray incidence support is the separate "
                    + "GrayGridComponent construction. Covariance alone does not identify "
                    + "an arbitrary support with that construction. The external research "
                    + "anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products "
                    + "with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2, "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . The original "
                    + "f2(Q9)=3-or-4 question, E15, the 258-vertex obstruction and universal "
                    + "component classification remain unresolved. No literature novelty "
                    + "or priority claim is made."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation"))
        ]));

    private static Formula CovarianceFormula()
    {
        Formula n = F.Id("n"), g = F.Id("g"), p = F.Id("p"), s = F.Id("s");
        Formula x = F.Id("x"), y = F.Id("y"), i = F.Id("i"), z = F.Id("z");
        var cube = Call("Q", n);
        var coordinates = Call("Fin", n);
        var vector = new Formula.TypeArrow(cube, Call("Real"));
        var gx = At(g, x);
        var xi = Call("flip", x, i);
        var geometry = All("x", cube, All("i", coordinates,
            Eqn(At(g, xi), Call("flip", gx, At(p, i)))));
        var signs = All("x", cube, Logic(Eqn(At(s, x), D(1)),
            FormulaLogicOperator.Or, Eqn(At(s, x), Seq(Minus, D(1)))));
        var coefficients = All("x", cube, All("i", coordinates,
            Eqn(Call("huangMatrix", n, gx, At(g, xi)),
                Mul(Mul(At(s, x), Call("huangMatrix", n, x, xi)), At(s, xi)))));
        var inverseY = Call("symm", g, y);
        var push = Lambda("y", Mul(At(s, inverseY), At(z, inverseY)));
        var matrix = Call("huangMatrix", n);
        var intertwining = All("z", vector,
            Eqn(Call("mulVec", matrix, push),
                Lambda("y", Mul(At(s, inverseY), At(Call("mulVec", matrix, z), inverseY)))));
        var conclusion = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"), vector,
            And(signs, And(coefficients, intertwining)));
        return Disp(All("n", Call("Nat"),
            All("g", Call("Equiv", cube, cube),
                All("p", Call("Equiv", coordinates, coordinates),
                    Logic(geometry, FormulaLogicOperator.Implies, conclusion)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Lambda(string name, Formula body) =>
        Seq(Open, F.Id(name), Sp, Mapsto, Sp, body, Close);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
}
