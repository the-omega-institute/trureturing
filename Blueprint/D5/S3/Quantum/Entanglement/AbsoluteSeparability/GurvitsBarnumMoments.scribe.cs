using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class GurvitsBarnumMomentsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(F.Id(n), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, Par(Seq(F.Id(n), Colon, t)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Sp, q);
    private static Formula Eq(Formula p, Formula q) => Seq(p, F.Eq, q);
    private static Formula Le(Formula p, Formula q) => Seq(p, Leq, Sp, q);
    private static Formula Sum(string n, Formula t, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(n), Colon, t)), Sp, body);
    private static Formula Arrow(Formula p, Formula q) => Seq(p, To, Sp, q);
    private static Formula Mul(Formula p, Formula q) => Seq(p, Cdot, Sp, q);
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Dim => F.Id("d");
    private static Formula Index => Call("Fin", Dim);
    private static Formula Vector => Arrow(Index, C);
    private static Formula Functional => Arrow(Par(Vector), C);
    private static Formula Matrix => Arrow(Index, Arrow(Index, C));
    private static Formula L(Formula f) => Call("L", Dim, f);
    private static Formula Re(Formula f) => Call("Re", f);
    private static Formula Q(Formula t, Formula z) => Call("q", t, z);
    private static Formula Lam(string n, Formula body) =>
        Seq(Lambda, Sp, F.Id(n), Comma, Sp, body);
    private static Formula Power(Formula b, Formula e) => new Formula.Power(b, e);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite fourth roots of unity, corrected by standard basis vectors, reproduce the two pairings of fourth moments.",
        H("Corrected finite fourth moments"), Blocks(
            Paragraph(Text("For z indexed by Fin d, let q(T,z) be the sum of conjugate(z_i) z_j T_ij. Let L_d(f) be the sum of f over all vectors with coordinates in {1,i,-1,-i}, plus 4^d times the sum of f over the standard basis vectors. The basis term supplies the additional contribution when all four indices coincide. These formulas include d = 0.")),
            Describe.Lean(DescribeId.Create("gb-design-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.designSum_sum"),
                H("Finite additivity"), StatementSource.FromAuthor(Disp(Additivity())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both finite sums defining L commute with an additional finite sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gb-design-real-monotone"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.re_designSum_mono"),
                H("Real monotonicity"), StatementSource.FromAuthor(Disp(Monotonicity())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every weight in L is nonnegative, so it preserves pointwise inequalities of real parts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gb-design-quadratic-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.quadratic_product_sum"),
                H("Two quadratic forms"), StatementSource.FromAuthor(Disp(Product())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Rotating one phase coordinate by i makes every unbalanced fourth moment vanish. The balanced terms give the product of traces and the crossed matrix product. The standard basis correction removes the double-counting deficit at coincident indices."))), DescribeRole.Theorem))));

    private static Formula Additivity()
    {
        var a = F.Id("a");
        var f = F.Id("f");
        var z = F.Id("z");
        var index = F.Id("J");
        var finite = Seq(OpenBracket, Call("Fintype", index), CloseBracket);
        return All("d", N, All("J", F.Id("Type"),
            Seq(finite, Comma, Sp, All("f", Arrow(index, Par(Functional)),
                Eq(L(Lam("z", Sum("a", index, Call("f", a, z)))),
                    Sum("a", index, L(Call("f", a))))))));
    }

    private static Formula Monotonicity()
    {
        var z = F.Id("z");
        return All("d", N, All("f", Functional, All("g", Functional,
            Imp(All("z", Vector, Le(Re(Call("f", z)), Re(Call("g", z)))),
                Le(Re(L(F.Id("f"))), Re(L(F.Id("g"))))))));
    }

    private static Formula Product()
    {
        var t = F.Id("T");
        var u = F.Id("U");
        var z = F.Id("z");
        var i = F.Id("i");
        var j = F.Id("j");
        return All("d", N, All("T", Matrix, All("U", Matrix,
            Eq(L(Lam("z", Mul(Q(t, z), Q(u, z)))),
                Mul(Power(D(4), Dim), Par(Seq(Mul(Call("tr", t), Call("tr", u)), Plus,
                    Sum("i", Index, Sum("j", Index,
                        Mul(Call("T", i, j), Call("U", j, i)))))))))));
    }
}
