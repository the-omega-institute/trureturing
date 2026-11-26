using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class RoundQuaternionLocalGeometryDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_defect_estimates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triangle defect and the cyclic rim trace control the scaled cosine threshold near the quarter turn.",
        H("Quarter-turn defect and score comparison"),
        Blocks(
            Paragraph(Text("Let S denote the group of unit real quaternions. The map W is the transverse Fourier field of the three cyclic rim gains A, and QPair denotes the complex-pair quaternion embedding. The maximum absolute scalar perturbation is E. The quantity h is the maximum of the three scalar perturbations and the negative real part of the cyclic rim product. The radius e is the largest triangle defect of the hub-gauged assignment. The coefficient cStar is twice the sharp quarter-turn radius divided by pi.")),
            Describe.Lean(DescribeId.Create("local-geometry"), DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_geometry"),
                H("Exact face geometry in the hub gauge"),
                StatementSource.FromAuthor(Disp(Call("GeometryLaws", Op("hubMaxDefect")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The geometric laws use the coordinate identities for the complex pair and the cyclic phase, and the preservation of distances and scores by unitary conjugation. The maximum angle is the largest over the four faces. Cyclic rotation and reversal preserve each oriented triangle's angle, so a face realizing this maximum attains the defect in the directed definition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-defect-estimates"), DeclarationHandle.Create(Gid),
                H("Exact triangle defect and its quantitative comparison"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three cyclic transverse areas equal the same constant times the difference of the squared Fourier amplitudes. Substituting those areas into the scalar part of the triple quaternion product gives the fourth face bound. Averaging that bound with the three spoke inequalities and using the scalar perturbation of largest absolute value gives the stated estimate for h. The strict concavity of the scaled cosine as a function of h bounds it by its tangent at zero. The rational Taylor bounds for the quarter-turn coefficient leave the displayed score margin."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Op(name), [.. args]);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Par(left), op, Par(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Lt(Formula left, Formula right) => Seq(left, Sp, F.Lt, Sp, right);
    private static Formula Fr(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));
    private static Formula Pow(Formula x, byte exponent) => Seq(Par(x), Caret, Grp(D(exponent)));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);

    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Rim => Call("Fin", D(3));

    private static Formula Statement()
    {
        var a = V("A");
        var p = V("p");
        var q = V("q");
        var eta = V("eta");
        var gamma = V("gamma");
        var j = V("j");
        var s = V("s");
        var e = Call("e", a);
        var h = Call("h", a, eta);
        var axialMax = Call("E", eta);
        var rho = Fr(D(3), D(5,0));
        var scaled = Mul(Op("cStar"), e);
        var pNorm = Abs(p);
        var qNorm = Abs(q);

        var coordinates = All("j", Rim, Eq(Call("gain", a, j),
            Call("QPair", Seq(Open, Minus, Call("val", eta, j), Comma, Call("val", gamma, j), Close),
                Call("W", p, q, j))));
        var positiveAxis = All("j", Rim, Lt(D(0), Call("val", gamma, j)));
        var exactDefect = Eq(e, Seq(Fr(Pi, D(2)), Plus, Call("arcsin", h)));
        var traceRange = Lt(Abs(h), Fr(D(1), D(5)));
        var traceError = Seq(Mul(Fr(D(1,3), D(5)), Pow(qNorm, 2)), Plus,
            Mul(Mul(D(2,5), Pow(rho, 2)), axialMax));
        var traceLower = Le(Seq(Fr(axialMax, D(3)), Plus,
            Fr(Mul(Fr(D(5,1), D(2,0)), Pow(pNorm, 2)), D(6)), Minus, Fr(traceError, D(3))), h);
        var scaledRange = And(Le(D(0), scaled), Le(scaled, Pi));

        var minScore = Seq(Fr(D(1), Root(D(3))), Plus, Fr(qNorm, Root(D(6))),
            Minus, Mul(Fr(Root(D(3)), D(1,2)), Pow(pNorm, 2)),
            Minus, Mul(Fr(D(2), D(5)), Pow(pNorm, 3)),
            Minus, Mul(D(3), Pow(pNorm, 4)),
            Minus, Mul(Mul(Fr(D(6,2,7), D(1,0,0)), rho), qNorm),
            Minus, Mul(Mul(D(2), rho), axialMax));
        var threshold = Seq(Call("cos", scaled), Plus, Fr(qNorm, D(2,0,0)), Plus,
            Mul(Fr(D(3), D(1,0,0)), Par(Seq(Pow(pNorm, 2), Plus, axialMax))));
        var comparison = All("s", Reals, Imp(Le(minScore, s), Le(threshold, s)));
        var conclusion = And(exactDefect, And(traceRange, And(traceLower, And(scaledRange, comparison))));
        var assumptions = Imp(coordinates, Imp(positiveAxis, Imp(Le(pNorm, rho),
            Imp(Le(qNorm, rho), Imp(Le(axialMax, rho), conclusion)))));
        return All("A", Arrow(Rim, V("S")), All("p", Complexes, All("q", Complexes,
            All("eta", Arrow(Rim, Reals), All("gamma", Arrow(Rim, Reals), assumptions)))));
    }
}
