using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class RoundQuaternionLocalSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A phase-normalized potential gives a quantitative fit gap near the quarter turn. Weighted variance identifies an angular region in which this estimate applies.",
        H("Strict local quaternion sharpness"),
        Blocks(
            Paragraph(Text("Write S for the group of unit real quaternions. The gain assignment G has identity on the diagonal and on all spokes at vertex zero. The three cyclic rim gains are the entries of A and all reverse gains are inverses. The radius e is the maximum of the round angles of the three spokes' triangles and the cyclic rim triangle. The predicate Fits bounds the round distance from a gain to the transported vertex potential on each directed edge.")),
            Paragraph(Text("Write QPair for the complex-pair coordinates of a real quaternion in the basis 1, I, J, IJ. The transverse field W consists of the two nonconstant Fourier modes of the cyclic rim. Write E for the maximum absolute scalar perturbation and Rho for three fiftieths. The coefficient C is twice the quarter-turn radius divided by pi. The potential P first rotates the transverse phase to make the product of the second Fourier coefficient and the root-of-unity difference real and nonnegative, uses the prescribed rim potentials, and transports them back.")),
            Result("strict-local-fit", "quarterLocal_strictFit", "Strict quantitative local fit",
                Strict(), "The rim scores have a common quadratic term and controlled cubic and higher-degree terms. The largest triangle defect bounds a scalar combination of the axial and transverse perturbations. A supporting tangent for the cosine of the scaled defect converts these bounds into the displayed score gap. At the center the cyclic quarter-turn obstruction attains its sharp radius."),
            Paragraph(Text("In the chart the three axial angles are a, b, and c. The second and third imaginary directions are separated from the first by u and v, with relative azimuth w. The functions Chart and Defect denote the resulting gains and their exact triangle defect.")),
            Result("angular-neighborhood", "quarterLocal_angularRegion", "Weighted-variance angular neighborhood",
                Angular(), "Align the positive imaginary-part sum with I. Orthogonal projection onto its transverse plane has weighted mean zero. The pairwise weighted variance and the three-mode Parseval identity give the bound on the two transverse Fourier amplitudes. Conjugation transports the fit back to the original chart. Zero perturbation forces the three axial angles to equal pi over two and the two separations to vanish."))));

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
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Logic(Formula lhs, FormulaLogicOperator op, Formula rhs) =>
        new Formula.Logic(Par(lhs), op, Par(rhs));
    private static Formula And(Formula lhs, Formula rhs) => Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula Imp(Formula lhs, Formula rhs) => Logic(lhs, FormulaLogicOperator.Implies, rhs);
    private static Formula Eq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) => Seq(lhs, Sp, Neq, Sp, rhs);
    private static Formula Le(Formula lhs, Formula rhs) => Seq(lhs, Sp, Leq, Sp, rhs);
    private static Formula Lt(Formula lhs, Formula rhs) => Seq(lhs, Sp, F.Lt, Sp, rhs);
    private static Formula Fr(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));
    private static Formula Sq(Formula x) => Seq(Par(x), Caret, Grp(D(2)));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Not(Formula x) => Seq(Neg, Sp, Par(x));
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);

    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Rim => Call("Fin", D(3));
    private static Formula Vertices => Call("Fin", D(4));
    private static Formula Potential => Arrow(Vertices, V("S"));
    private static Formula Quarter => Fr(Pi, D(2));

    private static Formula Face(Formula g, Formula e)
    {
        var i = V("i"); var j = V("j"); var k = V("k");
        return Some("i", Vertices, Some("j", Vertices, Some("k", Vertices,
            And(Ne(i, j), And(Ne(j, k), And(Ne(i, k),
                Eq(Call("roundDist", Mul(Call("edge", g, i, j), Call("edge", g, j, k)),
                    Call("edge", g, i, k)), e)))))));
    }

    private static Formula StrictRadius(Formula g, Formula r, Formula p) =>
        Some("R", Reals, And(Lt(V("R"), r), Call("Fits", g, p, V("R"))));

    private static Formula Sharp(Formula g, Formula r) =>
        All("z", Potential, All("R", Reals, Imp(Lt(V("R"), r),
            Not(Call("Fits", g, V("z"), V("R"))))));

    private static Formula Strict()
    {
        var p = V("p"); var q = V("q"); var eta = V("eta"); var gamma = V("gamma"); var j = V("j");
        var i = V("i"); var a = V("A"); var g = Call("G", a); var e = Call("e", a);
        var radius = Mul(V("C"), e); var phi = Call("P", p, q); var E = Call("E", eta);
        var w = Call("W", p, q, j);
        var coordinates = All("j", Rim, Eq(Call("gain", a, j),
            Call("QPair", Seq(Open, Minus, Call("val", eta, j), Comma, Call("val", gamma, j), Close), w)));
        var root = All("j", Rim, Eq(Call("val", gamma, j), Seq(Sqrt, Grp(
            Seq(D(1), Minus, Sq(Call("val", eta, j)), Minus, Sq(Abs(w)))))));
        var positive = All("j", Rim, Lt(D(0), Call("val", gamma, j)));
        var bounds = And(Le(Abs(p), V("Rho")), And(Le(Abs(q), V("Rho")), Le(E, V("Rho"))));
        var zero = And(Eq(p, D(0)), And(Eq(q, D(0)), Eq(eta, D(0))));
        var advantage = Seq(Call("cos", radius), Plus, Fr(Abs(q), D(2,0,0)), Plus,
            Mul(Fr(D(3), D(1,0,0)), Par(Seq(Sq(Abs(p)), Plus, E))));
        var score = Seq(Langle, Sp, Call("edge", g, i, j), Comma, Sp,
            Mul(Seq(Par(Call("val", phi, i)), Caret, Grp(Minus, D(1))), Call("val", phi, j)), Sp, Rangle);
        var scores = All("i", Vertices, All("j", Vertices, Imp(Ne(i, j), Le(advantage, score))));
        var outcomes = And(Call("DefectLE", g, e), And(Face(g, e), And(scores,
            And(Call("Fits", g, phi, radius), And(Imp(Not(zero), StrictRadius(g, radius, phi)),
                Imp(zero, Sharp(g, radius)))))));
        return All("A", Arrow(Rim, V("S")), All("p", Complexes, All("q", Complexes,
            All("eta", Arrow(Rim, Reals), All("gamma", Arrow(Rim, Reals),
                Imp(coordinates, Imp(root, Imp(positive, Imp(bounds, outcomes)))))))));
    }

    private static Formula Angular()
    {
        var a = V("a"); var b = V("b"); var c = V("c"); var u = V("u"); var v = V("v"); var w = V("w");
        var g = Call("Chart", a, b, c, u, v, w);
        var e = Call("Defect", a, b, c, u, v, w);
        var radius = Mul(V("C"), e);
        var bound = Mul(Fr(D(1,7), D(9,0,0)), Pi);
        Formula Band(Formula x) => Le(Abs(Seq(x, Minus, Quarter)), bound);
        var size = Le(Seq(Sq(u), Plus, Sq(v), Plus, Sq(Seq(u, Plus, v))),
            Mul(Fr(D(4,4,9,7), D(5,0,0)), Sq(Fr(D(3), D(5,0)))));
        var center = And(Eq(a, Quarter), And(Eq(b, Quarter), And(Eq(c, Quarter), And(Eq(u, D(0)), Eq(v, D(0))))));
        var fit = Some("p", Potential, And(Call("Fits", g, V("p"), radius),
            Imp(Not(center), StrictRadius(g, radius, V("p")))));
        var outcomes = And(Call("DefectLE", g, e), And(Face(g, e), And(fit, Imp(center, Sharp(g, radius)))));
        var hypotheses = And(Band(a), And(Band(b), And(Band(c),
            And(Le(D(0), u), And(Le(D(0), v), And(Lt(Seq(u, Plus, v), Quarter), size))))));
        return All("a", Reals, All("b", Reals, All("c", Reals, All("u", Reals,
            All("v", Reals, All("w", Reals, Imp(hypotheses, outcomes)))))));
    }
}
