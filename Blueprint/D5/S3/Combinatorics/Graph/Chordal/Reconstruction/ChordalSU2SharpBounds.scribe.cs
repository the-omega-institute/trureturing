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
            Paragraph(Text("Write SU(2) for the group of unit real quaternions. The round distance d is the arccosine of the real inner product. The vertex type may lie in any universe.")),
            Predicate("skew", "SU2Skew", "Skew gains", SkewFormula(),
                "Reversing an oriented edge inverts its gain."),
            Predicate("triangle-bound", "SU2TriangleBound", "Triangle defects", TriangleFormula(),
                "The triangle defect compares the ordered two-edge product with the gain on the direct edge."),
            Predicate("fits", "SU2Fits", "Potential residuals", FitsFormula(),
                "The potential assigns a unit quaternion to each vertex. The relative potential of an oriented edge is the inverse of the potential at its tail times the potential at its head."),
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

    private static DocumentBlock.Describe Bound(string id, string theorem, string title, Formula bound, int clique,
        bool connected, Formula? defectLimit, string proof, bool needsDefect = true) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Gid}.{theorem}"),
            H(title), StatementSource.FromAuthor(Disp(Statement(bound, clique, connected, defectLimit, needsDefect))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static DocumentBlock.Describe Predicate(string id, string name, string title, Formula formula,
        string meaning) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Gid}.{name}"),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);

    private static Formula SkewFormula()
    {
        var V = F.Id("V");
        var G = F.Id("G");
        var g = F.Id("g");
        var u = F.Id("u");
        var v = F.Id("v");
        return OnGraph(V, G, g, Iff(Apply("SU2Skew", G, g), For("u", V, For("v", V,
            If(Apply("Adj", G, u, v), new Formula.Relation(Apply("g", v, u),
                FormulaRelationOperator.Equal, Inverse(Apply("g", u, v))))))));
    }

    private static Formula TriangleFormula()
    {
        var V = F.Id("V");
        var G = F.Id("G");
        var g = F.Id("g");
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var delta = F.Id("delta");
        var product = Times(Apply("g", u, v), Apply("g", v, w));
        var bound = new Formula.Relation(Apply("d", product, Apply("g", u, w)),
            FormulaRelationOperator.LessThanOrEqual, delta);
        var triangles = For("u", V, For("v", V, For("w", V,
            If(Apply("Adj", G, u, v), If(Apply("Adj", G, v, w), If(Apply("Adj", G, u, w), bound))))));
        return OnGraph(V, G, g, For("delta", Reals, Iff(Apply("SU2TriangleBound", G, g, delta), triangles)));
    }

    private static Formula FitsFormula()
    {
        var V = F.Id("V");
        var G = F.Id("G");
        var g = F.Id("g");
        var p = F.Id("p");
        var r = F.Id("r");
        var u = F.Id("u");
        var v = F.Id("v");
        var residual = Apply("d", Apply("g", u, v), Times(Inverse(Apply("p", u)), Apply("p", v)));
        return OnGraph(V, G, g, For("p", Potential(V), For("r", Reals, Iff(Apply("SU2Fits", G, g, p, r),
            For("u", V, For("v", V, If(Apply("Adj", G, u, v),
                new Formula.Relation(residual, FormulaRelationOperator.LessThanOrEqual, r))))))));
    }

    private static Formula OnGraph(Formula V, Formula G, Formula g, Formula body) =>
        For("V", F.Id("Type"), For("G", Apply("SimpleGraph", V), For("g", Gain(V), body)));

    private static Formula Potential(Formula V) => new Formula.TypeArrow(V, Apply("SU", D(2)));

    private static Formula Gain(Formula V) => new Formula.TypeArrow(V, Potential(V));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Inverse(Formula p) => new Formula.Power(p, Seq(Minus, D(1)));

    private static Formula Iff(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Iff, Parenthesized(q));

    private static Formula Statement(Formula bound, int clique, bool connected, Formula? defectLimit,
        bool needsDefect)
    {
        var V = F.Id("V");
        var G = F.Id("G");
        var g = F.Id("g");
        var p = F.Id("p");
        var delta = F.Id("delta");
        Formula result = Bind(FormulaQuantifier.Exists, "p", Potential(V), Apply("SU2Fits", G, g, p, bound));
        if (clique > 0)
        {
            var S = F.Id("S");
            result = If(For("S", Apply("Finset", V),
                If(Apply("IsClique", G, Apply("coe", S)),
                    new Formula.Relation(Apply("card", S), FormulaRelationOperator.LessThanOrEqual, Digits(clique)))),
                result);
        }
        if (needsDefect)
        {
            result = If(Apply("SU2TriangleBound", G, g, delta), result);
            if (defectLimit is not null)
                result = If(new Formula.Relation(delta, FormulaRelationOperator.LessThanOrEqual, defectLimit), result);
            result = For("delta", Reals,
                If(new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, delta), result));
        }
        result = For("g", Gain(V), If(Apply("SU2Skew", G, g), result));
        if (connected)
            result = If(Apply("Connected", G), result);
        return For("V", F.Id("Type"), For("G", Apply("SimpleGraph", V),
            Seq(OpenBracket, Apply("Finite", V), CloseBracket, Sp, If(Apply("IsChordal", G), result))));
    }

    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(TextToken(name))), [.. args]);

    private static Formula TextToken(string name) => name.Contains("2", StringComparison.Ordinal)
        ? Seq(F.Id("SU"), D(2), F.Id(name[3..]))
        : F.Id(name);

    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);

    private static Formula For(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula If(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.Implies, Parenthesized(q));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Digits(int n) =>
        D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());

    private static Formula Fraction(int n, int d) => Seq(Frac, Grp(Digits(n)), Grp(Digits(d)));

    private static Formula Times(Formula a, Formula b) => Seq(a, Sp, b);
}
