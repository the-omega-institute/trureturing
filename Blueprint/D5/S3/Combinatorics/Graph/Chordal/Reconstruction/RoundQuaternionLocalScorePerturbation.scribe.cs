using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class RoundQuaternionLocalScorePerturbationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation.";


    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pure Fourier rim estimate extends to all edges with controlled losses from the second Fourier mode and the scalar perturbation.",
        H("The local quaternion score"),
        Blocks(
            Paragraph(Text("The three cyclic rim gains A determine the hub-gauged assignment G. Write W for the two-mode transverse field, E for the maximum absolute scalar perturbation, and Rho for three fiftieths. The potential X uses the positive-root complex-pair rim coordinates after the second mode has been given the prescribed phase.")),
            Describe.Lean(DescribeId.Create("local-quantitative-score"), DeclarationHandle.Create(Prefix + "local_minScore"),
                H("Quantitative score on each directed edge"), StatementSource.FromAuthor(Disp(Score())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rationalize the difference of the two real fibre coordinates as the real coordinate increases. The linear response of the potential subtracts one copy of the second-mode term, while the new transverse gain adds two copies. The scalar and axial dot-product estimates bound the remaining gain changes. The spokes have the prescribed real score and reversing an edge preserves its score."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Logic(Formula lhs, FormulaLogicOperator op, Formula rhs) =>
        new Formula.Logic(Par(lhs), op, Par(rhs));
    private static Formula Imp(Formula lhs, Formula rhs) => Logic(lhs, FormulaLogicOperator.Implies, rhs);
    private static Formula Eq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) => Seq(lhs, Sp, Neq, Sp, rhs);
    private static Formula Le(Formula lhs, Formula rhs) => Seq(lhs, Sp, Leq, Sp, rhs);
    private static Formula Fr(Formula n, Formula d) => Seq(Frac, Grp(n), Grp(d));
    private static Formula Sq(Formula x) => Seq(Par(x), Caret, Grp(D(2)));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);

    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Rim => Call("Fin", D(3));
    private static Formula Vertices => Call("Fin", D(4));


    private static Formula Score()
    {
        var a = V("A");
        var p = V("p");
        var q = V("q");
        var eta = V("eta");
        var gamma = V("gamma");
        var i = V("i");
        var j = V("j");
        var k = V("k");
        var rho = Seq(Operatorname, Grp(V("Rho")));
        var w = Call("W", p, q, k);
        var E = Call("E", eta);
        var pNorm = Abs(p);
        var qNorm = Abs(q);
        var gains = Call("G", a);
        var potential = Call("X", p, q);
        var root = All("k", Rim, Eq(Call("val", gamma, k), Seq(Sqrt, Grp(
            Seq(D(1), Minus, Sq(Call("val", eta, k)), Minus, Sq(Abs(w)))))));
        var coordinates = All("k", Rim, Eq(Call("gain", a, k),
            Call("QPair", Seq(Open, Minus, Call("val", eta, k), Comma, Call("val", gamma, k), Close), w)));
        var phase = Eq(Mul(q, Par(Seq(Seq(Operatorname, Grp(V("zeta"))), Minus, D(1)))),
            Mul(Seq(Sqrt, Grp(D(3))), qNorm));
        var t = Fr(D(1), Seq(Sqrt, Grp(D(3))));
        var alpha = Fr(Seq(Sqrt, Grp(D(3))), D(1,2));
        var rhs = Seq(t, Plus, Fr(qNorm, Seq(Sqrt, Grp(D(6)))), Minus, Mul(alpha, Sq(pNorm)),
            Minus, Mul(Fr(D(2), D(5)), Seq(Par(pNorm), Caret, Grp(D(3)))),
            Minus, Mul(D(3), Seq(Par(pNorm), Caret, Grp(D(4)))),
            Minus, Mul(Fr(D(6,2,7), D(1,0,0)), Mul(rho, qNorm)), Minus, Mul(D(2), Mul(rho, E)));
        var score = Seq(Langle, Sp, Call("edge", gains, i, j), Comma, Sp,
            Mul(Seq(Par(Call("val", potential, i)), Caret, Grp(Minus, D(1))),
                Call("val", potential, j)), Sp, Rangle);
        var target = All("i", Vertices, All("j", Vertices, Imp(Ne(i, j), Le(rhs, score))));
        return All("A", Arrow(Rim, V("S")), All("p", Complexes, All("q", Complexes,
            All("eta", Arrow(Rim, Reals), All("gamma", Arrow(Rim, Reals),
                Imp(Le(pNorm, rho), Imp(Le(qNorm, rho), Imp(Le(E, rho),
                    Imp(root, Imp(coordinates, Imp(phase, target)))))))))));
    }
}
