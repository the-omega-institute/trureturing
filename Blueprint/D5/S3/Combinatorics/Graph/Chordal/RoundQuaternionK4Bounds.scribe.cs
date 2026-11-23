using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class RoundQuaternionK4BoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every round unit-quaternion gain assignment on four vertices admits a fit at four fifths of its triangle defect.",
        H("Round quaternion reconstruction on four vertices"),
        Blocks(
            Paragraph(Text("The vertices are the four elements of Fin(4). The unit quaternions form the round three-sphere, with distance given by the arccosine of the real inner product. Write Q for the assignment with identity spokes, gains I on the directed rim 12, 23, 31 and inverse gains on the reversed edges, where I is the quaternion with imaginary coordinates (1,0,0).")),
            Paragraph(Text("Write D(g,e) for inverse reversal, identity diagonal and a distance of at most e between the ordered product along two triangle sides and the gain along the third. Write F(g,p,r) when the directed edge distances between g and the gain induced by p are all at most r.")),
            Result("round-quaternion-upper-bound", "reconstruction_bound", "Uniform reconstruction",
                Uniform(FracOf(D(4), D(5))),
                "For large defects, choose successive potentials orthogonal to each already assigned potential transported along its edge. For smaller defects, gauge the spokes to one. The middle two potentials are constrained by two pairs of spherical centers. Compare their normalized sums and move toward the opposite midpoint when their separation permits. At larger separations, project a common direction orthogonally to the center planes. Six rational interval estimates for cosine guarantee the four center inequalities and the remaining edge inequality."),
            Result("round-quaternion-quarter-turn", "quarter_turn_sharp", "The cyclic quarter-turn optimum",
                Quarter(),
                "The three spoke projections bound the squared length of the rim mean from below by the square of the smallest edge cosine. The sum of the skew products on the rim equals the skew product of two orthogonal coordinates of the centered rim vectors multiplied by the square root of three. The Cauchy–Schwarz inequality and the centered energy identity bound the three skew products jointly. An equilateral configuration in the imaginary plane perpendicular to I attains equality on all edges."),
            Result("round-quaternion-coefficient-obstruction", "not_subcritical_claim",
                "Obstruction to a smaller coefficient", Seq(Neg, Sp, Par(Some("k", Reals,
                    And(Lt(F.Id("k"), Ratio), Uniform(F.Id("k")))))),
                "Evaluate the proposed coefficient on the cyclic quarter-turn assignment at defect pi over two. Its exact minimax radius gives the contradiction."))));

    private static DocumentBlock Result(string id, string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula term) => Seq(Open, term, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula FracOf(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vertex => Call("Fin", D(4));
    private static Formula Sphere => Seq(F.Id("S"), Caret, Grp(D(3)));
    private static Formula Potential => new Formula.TypeArrow(Vertex, Sphere);
    private static Formula Gains => new Formula.TypeArrow(Vertex, Potential);
    private static Formula Ratio => FracOf(Mul(D(2), Error), Pi);
    private static Formula Error => Call("arccos", FracOf(D(1), Seq(Sqrt, Grp(D(3)))));
    private static Formula HalfPi => FracOf(Pi, D(2));

    private static Formula Uniform(Formula coefficient)
    {
        var g = F.Id("g");
        var e = F.Id("e");
        return All("g", Gains, All("e", Reals,
            Imp(LeqOf(D(0), e), Imp(LeqOf(e, Pi), Imp(Call("D", g, e),
                Some("p", Potential, Call("F", g, F.Id("p"), Mul(coefficient, e))))))));
    }

    private static Formula Quarter()
    {
        var q = F.Id("Q");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        Formula Gain(Formula a, Formula b) => new Formula.Apply(q, [a, b]);
        Formula Pot(Formula a) => Call("p", a);
        Formula Edge() => Call("d", Gain(i, j), Mul(Call("inv", Pot(i)), Pot(j)));
        var exact = Some("i", Vertex, Some("j", Vertex, Some("k", Vertex,
            And(Ne(i, j), And(Ne(j, k), And(Ne(i, k),
                Eq(Call("d", Mul(Gain(i, j), Gain(j, k)), Gain(i, k)), HalfPi)))))));
        var lower = All("p", Potential, Some("i", Vertex, Some("j", Vertex,
            And(Ne(i, j), LeqOf(Error, Edge())))));
        var equality = Some("p", Potential, All("i", Vertex, All("j", Vertex,
            Imp(Ne(i, j), Eq(Edge(), Error)))));
        return And(Call("D", q, HalfPi), And(exact,
            And(lower, And(equality, Lt(FracOf(D(3), D(5)), Ratio)))));
    }
}
