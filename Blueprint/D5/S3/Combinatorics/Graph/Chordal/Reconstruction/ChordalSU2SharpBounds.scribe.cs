using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class ChordalSU2SharpBoundsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle defects control reconstruction of unit-quaternion gains on finite chordal graphs.",
        H("Sharp unit-quaternion reconstruction bounds"),
        Blocks(
            Bound("sharp-global", "exists_su2_gain_potential_global_sharp", "The global coefficient",
                Times(Fraction(434, 125), F.Id("delta")), 0, true, null,
                "The breadth-first construction transports a frame along common shadow predecessors and normalizes the nearest point of each candidate hull. Across consecutive layers, two cap radii bound the residual. Within a layer, nested predecessor sets give corresponding candidates in the two caps. In the lower defect interval, a projection of their convex mean gives the comparison. In the upper interval, three Rayleigh quotients for the same weighted holonomy matrix force a common quaternionic eigenline with large overlap. The asymmetric overlap inequality and the rational interval estimates exclude the resulting angle. When the proposed bound reaches pi, the diameter of the unit three-sphere suffices."),
            Bound("small-two", "exists_su2_gain_potential_small_defect_two", "Defects at most pi over six",
                Times(D(2), F.Id("delta")), 0, false, Seq(Frac, Grp(Pi), Grp(D(6))),
                "Reverse simplicial elimination inserts a cap center at each vertex. The residual on the parent clique and the triangle defect give a candidate diameter at most three times the defect. The four-point spherical Jung criterion follows from the triple-angle and double-angle identities."),
            Bound("small-eight-fifths", "exists_su2_gain_potential_small_defect_eight_fifths",
                "Defects at most one tenth", Times(Fraction(8, 5), F.Id("delta")), 0, false, Fraction(1, 10),
                "The same simplicial insertion uses the spherical Jung cosine criterion with radius eight fifths of the defect. Cubic and linear sine bounds certify the criterion on the entire interval."),
            Bound("clique-three", "exists_cliqueThree_su2_gain_potential_min", "At most two parents",
                Apply("min", F.Id("delta"), Seq(Frac, Grp(Pi), Grp(D(2)))), 3, false, null,
                "With at most two parents, half the candidate diameter bounds the insertion radius for defects below pi over two. The closed-hemisphere estimate gives the radius pi over two for larger defects."),
            Bound("clique-four", "exists_cliqueFour_su2_gain_potential_two", "At most three parents",
                Times(D(2), F.Id("delta")), 4, false, null,
                "The three-point Jung cap handles defects through pi over five. Between pi over five and pi over four, the initial two spectral moments and the cubic triangle holonomy moment exclude a nearest point with norm below the target cosine. From pi over four onward the closed-hemisphere radius suffices."),
            Bound("clique-five", "exists_cliqueFive_su2_gain_potential_half_pi", "At most four parents",
                Seq(Frac, Grp(Pi), Grp(D(2))), 5, false, null,
                "The affine span of at most four unit quaternions has dimension at most three. A unit normal with the appropriate sign gives a closed hemisphere containing every insertion candidate.",
                needsDefect: false))));

    private static Describe Bound(string id, string theorem, string title, Formula bound, int clique,
        bool connected, Formula? defectLimit, string proof, bool needsDefect = true) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Gid}.{theorem}"),
            H(title), StatementSource.FromAuthor(Disp(Statement(bound, clique, connected, defectLimit, needsDefect))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Skew gains invert under edge reversal. The triangle defect is the round distance between a two-edge product and the direct gain. Clique size bounds apply to every clique.")),
                Paragraph(Text(proof))),
            DescribeRole.Theorem);

    private static Formula Statement(Formula bound, int clique, bool connected, Formula? defectLimit,
        bool needsDefect)
    {
        var V = F.Id("V");
        var G = F.Id("G");
        var g = F.Id("g");
        var p = F.Id("p");
        var u = F.Id("u");
        var v = F.Id("v");
        var delta = F.Id("delta");
        var su2 = Apply("SU", D(2));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var potential = new Formula.TypeArrow(V, su2);
        var gain = new Formula.TypeArrow(V, potential);
        var residual = Apply("d", Apply("eval", g, u, v),
            Seq(new Formula.Power(Apply("eval", p, u), Seq(Minus, D(1))), Sp, Apply("eval", p, v)));
        var fit = Bind(FormulaQuantifier.Exists, "p", potential,
            For("u", V, For("v", V, If(Apply("Adj", G, u, v),
                new Formula.Relation(residual, FormulaRelationOperator.LessThanOrEqual, bound)))));
        Formula result = fit;
        if (clique > 0)
            result = If(Apply("CliqueBound", G, D(clique)), result);
        if (needsDefect)
        {
            result = If(Apply("TriangleBound", G, g, delta), result);
            if (defectLimit is not null)
                result = If(new Formula.Relation(delta, FormulaRelationOperator.LessThanOrEqual, defectLimit), result);
            result = For("delta", real,
                If(new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, delta), result));
        }
        result = For("g", gain, If(Apply("Skew", G, g), result));
        if (connected)
            result = If(Apply("Connected", G), result);
        result = For("G", Apply("SimpleGraph", V), If(Apply("Chordal", G), result));
        return For("level", Apply("Universe"), For("V", Apply("Type", F.Id("level")),
            If(Apply("Finite", V), result)));
    }

    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);

    private static Formula For(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula If(Formula p, Formula q) =>
        new Formula.Logic(Seq(Open, p, Close), FormulaLogicOperator.Implies, Seq(Open, q, Close));

    private static Formula Fraction(int n, int d) => Seq(Frac, Grp(D(n)), Grp(D(d)));

    private static Formula Times(Formula a, Formula b) => Seq(a, Sp, b);
}
