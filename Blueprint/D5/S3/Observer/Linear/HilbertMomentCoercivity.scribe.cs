using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class HilbertMomentCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hilbert moment coercivity", H("Hilbert moment coercivity"), Blocks(
            Describe.Lean(DescribeId.Create("hilbert-moment-positive-definite"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbertMoment_posDef"),
                H("Positive definiteness of the Hilbert moment matrix"), StatementSource.FromAuthor(Positive()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For N≥0, let H(N) be the real (N+1) by (N+1) matrix with entry 1/(i+j+1), indexed by 0≤i,j≤N. Let lambda(N) be the minimum of its real eigenvalues.")),
                    Paragraph(Text("Its quadratic form is the integral on [0,1] of the squared scalar polynomial with the supplied coefficient vector. A zero integral forces this continuous nonnegative function to vanish. A polynomial vanishing on an interval has all coefficients zero, which proves strict positivity on every nonzero coefficient vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hilbert-polynomial-coercivity"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/HilbertMomentCoercivity.hilbert_polynomial_coercivity"),
                H("Hilbert-valued coefficient energy"), StatementSource.FromAuthor(Coercivity()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let W be any real inner-product space and v(0),...,v(N) arbitrary vectors. There is no ambient dimension or completeness assumption. Expanding the integral gives the entrywise pairing of H(N) with the Gram matrix of these vectors.")),
                    Paragraph(Text("The matrix H(N)-lambda(N)I is positive semidefinite. Its Hadamard product with the coefficient Gram matrix is positive semidefinite; testing the all-ones vector yields the energy floor. Thus the same least eigenvalue works in every real Hilbert output space."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-polynomial-energy-floor"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/HilbertMomentCoercivity.taylor_polynomial_energy_floor"),
                H("Factorial short-window scaling"), StatementSource.FromAuthor(Taylor()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let K be the real or complex field, W any inner-product space over K, and 0<T≤1. Real coefficients act through the canonical embedding into K. The underlying real inner product preserves all norms.")),
                    Paragraph(Text("After t=Ts, the coefficients become T^i v(i)/i!. Since 0<T≤1 and i≤N, each T^i/i! is at least T^N/N!. The unit-interval floor and the change of variable give precisely T^(2N+1)/(N!)^2, including N=0 and T=1."))), DescribeRole.Theorem))));

    private static Formula Positive() => Disp(Seq(Forall, Sp, F.Id("N"), InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp, App(F.Id("PosDef"), App(F.Id("H"), F.Id("N")))));

    private static Formula Coercivity()
    {
        Formula n = F.Id("N"), v = F.Id("v"), i = F.Id("i"), s = F.Id("s"), w = F.Id("W");
        return Disp(Seq(Forall, Sp, w, Comma, Sp, OpenBracket, App(F.Id("RealInnerProductSpace"), w), CloseBracket, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, v, Colon, Sp, F.Id("Fin"), Open, n, Plus, D(1), Close, To, Sp, w, Comma, Sp,
            D(0), Lt, Sp, App(LambdaLower, n), Sp, Land, Sp,
            App(LambdaLower, n), Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n), Pow(Norm(App(v, i)), D(2)), Le, Sp,
            Integral(D(1), Pow(Norm(Seq(Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n), Pow(s, i), App(v, i))), D(2)), s)));
    }

    private static Formula Taylor()
    {
        Formula n = F.Id("N"), v = F.Id("v"), i = F.Id("i"), t = F.Id("t"), T = F.Id("T"), w = F.Id("W"), k = F.Id("K");
        return Disp(Seq(Forall, Sp, k, Comma, Sp, w, Comma, Sp,
            OpenBracket, App(F.Id("RCLike"), k), CloseBracket, Sp,
            OpenBracket, App(F.Id("InnerProductSpace"), k, w), CloseBracket, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, v, Colon, Sp, F.Id("Fin"), Open, n, Plus, D(1), Close, To, Sp, w, Comma, Sp,
            Forall, Sp, T, Comma, Sp, D(0), Lt, Sp, T, Le, Sp, D(1), Rightarrow, Sp,
            Frac, Grp(App(LambdaLower, n), Pow(T, Seq(D(2), n, Plus, D(1)))), Grp(Pow(Seq(Open, n, Bang, Close), D(2))),
            Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n), Pow(Norm(App(v, i)), D(2)), Le, Sp,
            Integral(T, Pow(Norm(Seq(Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n),
                Frac, Grp(Pow(t, i)), Grp(i, Bang), App(v, i))), D(2)), t)));
    }

    private static Formula Integral(Formula upper, Formula f, Formula t) =>
        Seq(Int, Underscore, Grp(D(0)), Caret, Grp(upper), f, Sp, Mathrm, Grp(F.Id("d")), t);
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
}
