using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class AppellRootDerivativeChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict polynomial operator budget controls the derivative chain at an actual root.",
        H("Appell Root Derivative Chain"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-root-derivative-chain"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/Jensen/AppellRootDerivativeChain.actual_root_derivative_chain"),
            H("Conditional polynomial operator estimate"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("P is a complex polynomial of natural degree q. The point b is "
                    + "an actual root, s is a nonzero complex number, a is a positive real "
                    + "number, and g is an arbitrary sequence of complex coefficients. "
                    + "P^(m) denotes the m-fold polynomial derivative, with P^(0)=P. "
                    + "The operator equation is equality of polynomials, not merely equality "
                    + "at b. Every sum ranges over the natural indices 2 <= m < q. Norms "
                    + "are complex absolute values, and the row inequality is real.")),
                Paragraph(Text("Differentiate the operator equation k times and evaluate "
                    + "at b. The product rule gives s^2 P^(k+2)(b) = b P^(k+1)(b) "
                    + "- (q-k) P^(k)(b) + sum g_m P^(k+m+1)(b), for k+2 <= q. "
                    + "Derivatives above q vanish. The top derivative is the nonzero "
                    + "constant q! times the leading coefficient; monicity is unnecessary.")),
                Paragraph(Text("The finite sequence |P^(j)(b)|/a^j, for 0 <= j <= q, "
                    + "has a positive attained maximum M. Its zeroth entry is zero. "
                    + "If an index k+2 attains M, the differentiated equation and triangle "
                    + "inequality bound that entry by B M, where B is the displayed row "
                    + "budget. Since B < 1, this is impossible. The maximizing index is "
                    + "therefore one, giving a nonzero first derivative and all displayed "
                    + "ratios. For q=1 the higher-index range and coefficient sum are empty.")),
                Paragraph(Text("This is the polynomial implication used in LC359--LC361 "
                    + "of the repository's Romik analytic note. For its Appell specialization, "
                    + "P=R_(q,t)=M_t(partial_z) z^q, s^2=v chi', and a=8 sqrt(q)/|s|. "
                    + "The g_m are ordinary coefficients of the logarithmic remainder; "
                    + "in the cumulant convention g_m=kappa_(m+1)/m!. The actual source "
                    + "ODE and its coefficient and root-location budgets must be established "
                    + "separately. This theorem supplies no global node signs, RH or Robin "
                    + "conclusion, and makes no claim of literature originality."))),
            DescribeRole.Theorem))));

    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("P");
    private static Formula B => F.Id("b");
    private static Formula S => F.Id("s");
    private static Formula A => F.Id("a");
    private static Formula G => F.Id("g");
    private static Formula M => F.Id("m");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Call(Formula x, Formula y) => Seq(x, Open, y, Close);
    private static Formula Op(string x, Formula y) =>
        Call(Seq(Operatorname, Grp(F.Id(x))), y);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Deriv(Formula n) => Pow(P, Seq(Open, n, Close));
    private static Formula GM => Seq(G, Underscore, Grp(M));
    private static Formula SumOver(Formula body) => Seq(Sum, Underscore,
        Grp(Seq(D(2), Le, Sp, M, Lt, Sp, Q)), Sp, body);
    private static Formula For(Formula x, Formula type) =>
        Seq(Forall, Sp, x, InMacro, Sp, type, Comma, Sp);

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(For(Q, Naturals), For(P, Seq(Complexes, OpenBracket, F.Id("X"), CloseBracket)),
            For(B, Complexes), For(S, Complexes), For(A, Reals),
            For(G, Seq(Open, Naturals, To, Sp, Complexes, Close))),
        Seq(D(1), Le, Sp, Q, Sp, Rightarrow, Sp, Op("natDegree", P), Eq, Q, Sp, Rightarrow, Sp,
            Call(P, B), Eq, D(0), Sp, Rightarrow, Sp, S, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            D(0), Lt, Sp, A, Sp, Rightarrow, Sp),
        Seq(Pow(S, D(2)), Sp, Deriv(D(2)), Minus, F.Id("X"), Sp, Deriv(D(1)), Plus, Q, Sp, P,
            Eq, SumOver(Seq(GM, Sp, Deriv(Seq(M, Plus, D(1))))), Sp, Rightarrow, Sp),
        Seq(Div(Norm(B), Seq(Pow(Norm(S), D(2)), Sp, A)), Plus,
            Div(Q, Seq(Pow(Norm(S), D(2)), Sp, Pow(A, D(2)))), Plus,
            SumOver(Div(Seq(Norm(GM), Sp, Pow(A, Seq(M, Minus, D(1)))), Pow(Norm(S), D(2)))),
            Lt, D(1), Sp, Rightarrow, Sp),
        Seq(Call(Deriv(D(1)), B), Neq, Sp, D(0), Land, Sp,
            Open, For(M, Naturals), D(1), Le, Sp, M, Sp, Rightarrow, Sp,
            M, Le, Sp, Q, Sp, Rightarrow, Sp,
            Norm(Div(Call(Deriv(M), B), Call(Deriv(D(1)), B))), Le, Sp,
            Pow(A, Seq(M, Minus, D(1))), Close)
    ]));
}
