using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteConvexFiberMapDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] xs)
    {
        var b = xs[^1];
        for (var i = xs.Length - 2; i >= 0; --i) b = new Formula.Logic(xs[i], FormulaLogicOperator.And, b);
        return b;
    }
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Not(Formula a) => F.Seq(F.Neg, F.Sp, F.Grp(a));
    private static Formula Inst(string s, params Formula[] xs) =>
        F.Seq(F.OpenBracket, Call(s, xs), F.CloseBracket, F.Sp);

    private static Formula Statement()
    {
        var X = Id("X"); var E = Id("E"); var real = Id("Real"); var n = Id("n");
        var x = Id("x"); var b = Id("b"); var j = Id("j"); var zero = F.D(0);
        var K = Id("K"); var L = Id("L"); var R = Id("R"); var O = Id("O");
        var setX = Call("Set", X); var setE = Call("Set", E); var index = Call("Fin", n);
        Formula V(Formula y) => Call("V", y);
        Formula B(Formula y) => Call("B", y);
        Formula N(Formula y) => Call("N", y);
        Formula A(Formula y) => Call("A", y);
        Formula Conv(Formula t) => Call("Convex", real, t);
        var assumptions = And(
            All("j", index, Call("IsOpen", V(j))),
            All("x", X, Ex("j", index, Mem(x, V(j)))),
            Conv(K), Conv(L), All("j", index, Conv(N(j))),
            All("x", X, Call("Subset", B(x), K)),
            All("j", index, All("x", X, Imp(Mem(x, V(j)), Call("Subset", B(x), N(j))))),
            All("j", index, Not(Mem(zero, N(j)))),
            All("j", index, new Formula.Logic(Call("Disjoint", N(j), R), FormulaLogicOperator.Or,
                Call("Subset", V(j), O))),
            Call("Subset", Call("Inter", L, R), Call("Singleton", zero)),
            All("x", X, Mem(Call("a", x), B(x))),
            All("x", X, Imp(Mem(x, O), Mem(Call("a", x), L))));
        var result = Ex("A", Call("ContinuousMaps", X, E), And(
            All("x", X, Mem(A(x), K)), All("x", X, Not(Mem(A(x), R))),
            All("x", X, All("b", E, Imp(Mem(b, B(x)),
                Not(Mem(zero, Call("segment", real, b, A(x)))))))));
        return All("X", Id("Types"), All("E", Id("Types"), F.Seq(
            Inst("TopologicalSpace", X), Inst("CompactSpace", X), Inst("TTwoSpace", X),
            Inst("NormedAddCommGroup", E), Inst("NormedSpace", real, E),
            All("n", Id("Nat"), All("V", new Formula.TypeArrow(index, setX),
            All("B", new Formula.TypeArrow(X, setE), All("N", new Formula.TypeArrow(index, setE),
            All("K", setE, All("L", setE, All("R", setE, All("O", setX,
            All("a", new Formula.TypeArrow(X, E), Imp(assumptions, result)))))))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite convex averaging gives a continuous map avoiding a forbidden set while controlling every point of every fiber.",
        H("Convex averaging with whole-fiber control"),
        Blocks(Describe.Lean(DescribeId.Create("continuous-ray-avoiding-fiber-map"),
            DeclarationHandle.Create("D5/S3/Topology/FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map"),
            H("A continuous average without continuous fiber selections"),
            StatementSource.FromAuthor(F.Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("X is any compact Hausdorff space and E any real normed vector space. V is a finite open cover. B(x) is a subset of E for each x; the notation fiber imposes no additional regularity assumption. Every B(x) lies in the convex set K. Each V(j) controls its entire fiber: x in V(j) implies B(x) is contained in the convex set N(j), and zero is outside every N(j).")),
                Paragraph(Text("R is the forbidden subset of E. It need not itself be a ray for this construction. For each j, either N(j) is disjoint from R, or V(j) lies in O. The convex slice L meets R only possibly at zero. The arbitrary representatives a(x) belong to B(x), and belong to L whenever x lies in O. They are not assumed continuous. ContinuousMaps denotes continuous maps, Inter denotes intersection, Singleton denotes a singleton, Subset denotes inclusion, and segment denotes the closed affine segment.")),
                Paragraph(Text("Construct a finite centered star refinement and take a second partition of unity subordinate to it. Average the finitely many representatives at its centers. The weights are continuous, nonnegative and sum to one, so this average A is continuous and lies in K.")),
                Paragraph(Text("At any x choose a refinement member with positive weight. Every other active member meets it at x. The star condition puts x and all active centers in one V(j). Thus B(x) and every active representative lie in the same N(j), and convexity puts A(x) there too. Every segment from any b in B(x) to A(x) stays in N(j), so it avoids zero.")),
                Paragraph(Text("If that N(j) is disjoint from R, the average avoids R. Otherwise every active center is in O, so every active representative lies in L and the average lies in L. Membership in R would force A(x) to be zero, contradicting its membership in N(j). This checks the mixed terms through a common convex set; separate bounds on individual representatives would not suffice.")),
                Paragraph(Text("The result supplies a finite convex construction, with no dimension, metrizability or continuous-selection assumption on X and no finite-dimensional assumption on E. Applying it to a boundary quotient still requires construction of the quotient, a common slice, the finite controlling neighborhoods and the stated representatives. Radial projection and the final topological obstruction are further conclusions, not hypotheses or conclusions of this theorem. The construction carries no originality claim."))),
            DescribeRole.Theorem))));
}
