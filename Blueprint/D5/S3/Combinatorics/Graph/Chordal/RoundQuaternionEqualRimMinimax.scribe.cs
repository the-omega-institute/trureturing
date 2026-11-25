using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class RoundQuaternionEqualRimMinimaxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic equal-rim assignment has an exact minimax fit at every angle. Its ratio of fit radius to positive triangle defect has a unique maximum at the quarter turn.",
        H("Cyclic equal-rim quaternion minimax"),
        Blocks(
            Paragraph(Text("Write S for the group of unit real quaternions and D for inverse reversal, identity diagonal and the triangle defect bound. Write F for the bound on every directed edge error of a potential on four vertices. The gain G has identity spokes and forward rim gain given by the cosine of the angle plus its sine times the unit imaginary quaternion. Reverse rim gains are inverses.")),
            Paragraph(Text("The defect e is three times the angle up to pi over three. From there to pi over two it is two pi minus three times the angle. For larger angles it equals the angle. The radius R equals the angle up to pi over three. For larger angles it is the arccosine of the positive quadratic root. The quadratic coefficient is the difference between the cosine of the angle displaced by two pi over three and the cosine of the angle. The linear coefficient is one and the constant coefficient is the negative of the displaced cosine.")),
            Result("exact-defect-and-minimax", "equalRim_exact_defect_and_minimax",
                "Exact triangle defect and minimax radius", Exact(),
                "The spoke and rim triangles have principal angles given by the common rim angle and the angle of its cube. The spokes bound the projection of the rim mean. Subtracting that mean leaves a cyclic symmetric sum equal to minus half the centered energy and a cyclic skew sum bounded by the square root of three times half that energy. These bounds give the quadratic constraint on any positive common edge score. A constant potential attains the small-angle bound. An equilateral triangle at the latitude of the positive root attains the large-angle bound."),
            Result("unique-quarter-turn-ratio", "equalRim_ratio_unique_maximum_at_quarter_turn",
                "Unique maximum of the minimax-to-defect ratio", Ratio(),
                "The small-angle ratio is one third. At latitude one over the square root of three the common rim score is the sine of the angle times the latitude. This bounds the radius by a convex arccosine function of the distance from the quarter turn. Its secant bound increases strictly more slowly than the scaled defect away from the quarter turn. At the quarter turn the fixed latitude is the optimal quadratic root."))));

    private static DocumentBlock Result(string id, string declaration, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula lhs, FormulaLogicOperator op, Formula rhs) =>
        new Formula.Logic(Par(lhs), op, Par(rhs));
    private static Formula Par(Formula term) => Seq(Open, term, Close);
    private static Formula And(Formula lhs, Formula rhs) => Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula Imp(Formula lhs, Formula rhs) => Logic(lhs, FormulaLogicOperator.Implies, rhs);
    private static Formula Eq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Le(Formula lhs, Formula rhs) => Seq(lhs, Sp, Leq, Sp, rhs);
    private static Formula FracOf(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));

    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(V("H")));
    private static Formula Potential => new Formula.TypeArrow(Call("Fin", D(4)), V("S"));

    private static Formula Exact()
    {
        var i = V("I");
        var a = V("a");
        var g = Call("G", i, a);
        var defect = Call("e", a);
        var radius = Call("R", a);
        var p = V("p");
        var r = V("r");
        var minimalDefect = All("d", Reals,
            Imp(Call("D", g, V("d")), Le(defect, V("d"))));
        var attained = Some("p", Potential, Call("F", g, p, radius));
        var minimalRadius = All("p", Potential, All("r", Reals,
            Imp(Call("F", g, p, r), Le(radius, r))));
        return All("I", Quaternions, Imp(Eq(Call("re", i), D(0)),
            Imp(Eq(Call("norm", i), D(1)),
                All("a", Reals, Imp(And(Le(D(0), a), Le(a, Pi)),
                    And(Call("D", g, defect), And(minimalDefect, And(attained, minimalRadius))))))));
    }

    private static Formula Ratio()
    {
        var a = V("a");
        var quotient = FracOf(Call("R", a), Call("e", a));
        var root = Seq(Sqrt, Grp(D(3)));
        var coefficient = FracOf(Seq(D(2), Sp, Cdot, Sp, Call("arccos", FracOf(D(1), root))), Pi);
        return All("a", Reals, Imp(And(Seq(D(0), Sp, F.Lt, Sp, a), Le(a, Pi)),
            And(Le(quotient, coefficient),
                Logic(Eq(quotient, coefficient), FormulaLogicOperator.Iff, Eq(a, FracOf(Pi, D(2)))))));
    }
}
