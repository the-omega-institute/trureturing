using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntryReturnTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common slow return mode of a reversible single-entry network.",
        H("The common slow association tail"),
        Blocks(Describe.Lean(DescribeId.Create("single-entry-finite-network-common-slow-tail"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/SingleEntryReturnTail.finite_network_common_slow_tail"),
            H("One root governs every pair"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "For a nonempty finite family of sites, k supplies all positive binding, unbinding, entry and return rates. The probability vector p is independently anchored by the actual configuration generator and starts from the repressed point mass. There is a positive secular root l below every free site rate, and the actual net current theta p(R)-eta p(empty), multiplied by exp(l t), converges to -theta/F'(l), which is strictly positive. This same l is the least positive eigenvalue of the full negative configuration generator. For every distinct pair i,j, exp(l t) times its association r kappa(i,j)-X(i)X(j) converges to -theta rInf q(i)q(j)/((s(i)+s(j)-l)F'(l)), which is also strictly positive. The root is selected before quantifying over the pairs, so the scale is common to all of them. The derivative is the independently defined secularSlope, identified with F' by the scalar root theorem.")), Paragraph(Text(
                "The free product transform sends the actual forward equation to the extended mode matrix B. A positive diagonal scaling makes B symmetric: its symmetric form is D+vv-transpose, where D has subset rates on cube modes and zero at R, while v(R)=sqrt(theta) and v(S)=-sqrt(eta W(S)). Every eigenvector below the first free pole is determined by its R coordinate. Normalize this coordinate to one. Its squared norm N satisfies theta N=-l F'(l), by the secular equation. Expansion in an orthonormal eigenbasis shows that the total squared R coordinate across all eigenvectors with eigenvalue l is 1/N. This argument does not require selecting a unique eigenbasis index. All larger positive modes disappear after multiplication by exp(l t), and zero modes contribute zero to the derivative. The result therefore concerns the same actual trajectory and its net current, rather than an independently chosen spectral mixture."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Positive(Formula x) => Rel(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula Statement()
    {
        var k = F.Id("k"); var p = F.Id("p"); var l = F.Id("l"); var t = F.Id("t");
        var a = Call("a", k); var b = Call("b", k); var e = Call("eta", k); var h = Call("theta", k);
        var state = Call("Option", Call("Finset", F.Id("I")));
        var coefficient = Seq(Minus, h, Slash, Call("secularSlope", a, b, e, l));
        var current = Seq(h, Sp, Cdot, Sp, Call("apply", p, t, Call("none")), Sp, Minus, Sp,
            e, Sp, Cdot, Sp, Call("apply", p, t, Call("some", Emptyset)));
        var scaled = Seq(Call("exp", Seq(l, Sp, Cdot, Sp, t)), Sp, Cdot, Sp, Open, current, Close);
        var limit = Call("Tendsto", Call("fun", t, scaled), Call("atTop"), Call("nhds", coefficient));
        var i = F.Id("i"); var j = F.Id("j");
        var rInf = Seq(h, Slash, Open, h, Plus, e, Cdot, Call("modeWeight", a, b, Emptyset), Close);
        var pairCoefficient = Seq(Minus, h, Cdot, rInf, Cdot, Call("occupancy", a, b, i), Cdot, Call("occupancy", a, b, j), Slash,
            Open, Open, Call("siteRate", a, b, i), Plus, Call("siteRate", a, b, j), Minus, l, Close, Cdot,
            Call("secularSlope", a, b, e, l), Close);
        var pairScaled = Seq(Call("exp", Seq(l, Cdot, t)), Cdot, Call("association", p, i, j, t));
        var pairLimit = Call("Tendsto", Call("fun", t, pairScaled), Call("atTop"), Call("nhds", pairCoefficient));
        var pairs = All("i", F.Id("I"), All("j", F.Id("I"), Imp(Rel(i, FormulaRelationOperator.NotEqual, j),
            And(pairLimit, Positive(pairCoefficient)))));
        var matrix = Call("neg", Call("generator", k));
        var vector = Seq(state, To, R());
        Formula Eigen(string name, Formula value) => Ex(name, vector, And(Rel(F.Id(name), FormulaRelationOperator.NotEqual, D(0)),
            Rel(Call("mulVec", matrix, F.Id(name)), FormulaRelationOperator.Equal, Call("smul", value, F.Id(name)))));
        var least = All("m", R(), Imp(Positive(F.Id("m")), Imp(Eigen("y", F.Id("m")),
            Rel(l, FormulaRelationOperator.LessThanOrEqual, F.Id("m")))));
        var tail = And(limit, And(Positive(coefficient), pairs));
        var spectral = And(Eigen("x", l), And(least, tail));
        var upper = All("i", F.Id("I"),
            Rel(l, FormulaRelationOperator.LessThan, Call("siteRate", a, b, F.Id("i"))));
        var rootEquation = Rel(Call("secular", a, b, e, h, l), FormulaRelationOperator.Equal, D(0));
        var root = Ex("l", R(), And(Positive(l), And(upper, And(rootEquation, spectral))));
        var body = All("k", Call("Rates", F.Id("I")), All("p", Seq(R(), Sp, To, Sp, state, Sp, To, Sp, R()),
            Imp(Call("ForwardSolution", k, p), root)));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", F.Id("I")), CloseBracket, Sp, body)));
    }
}
