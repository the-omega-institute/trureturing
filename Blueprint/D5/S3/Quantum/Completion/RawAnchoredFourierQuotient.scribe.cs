using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawAnchoredFourierQuotientDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawAnchoredFourierQuotient.";
    private static Formula M => F.Id("M");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula U => F.Id("u");
    private static Formula V => F.Id("v");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Z => F.Id("z");
    private static Formula K => F.Id("k");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Plus2(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Minus2(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Three(Formula a) => Seq(D(3), Sp, Cdot, Sp, a);
    private static Formula Product(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
    private static Formula Mark(Formula a) => Call("U", a);
    private static Formula BetaOf(Formula a) => Call("beta", F.Id("c"), a);
    private static Formula ROf(Formula a) => Call("markerQuotient", F.Id("U"), F.Id("c"), F.Id("h"), a);
    private static Formula GammaOf(Formula a) => Call("gamma", F.Id("c"), a);
    private static Formula RhoOf(Formula a) => Call("rho", F.Id("U"), F.Id("c"), F.Id("h"), a);
    private static Formula TDef(Formula a, Formula b) => Call("defect", F.Id("c"), a, b);
    private static Formula Form(Formula a, Formula b) => Call("quotientForm", F.Id("c"), a, b);
    private static Formula Read(Formula a, Formula b) => Call("c", a, b);
    private static Formula Member(Formula a, string b) => Seq(a, Sp, InMacro, Sp, Call(b == "Rad" ? "radical" : b, F.Id("c")));
    private static Formula All(Formula variable, Formula carrier, Formula body) =>
        Seq(Open, Forall, Sp, variable, Colon, Sp, carrier, Comma, Sp, body, Close);
    private static Formula AllM(Formula variable, Formula body) => All(variable, M, body);
    private static Formula AllV(Formula variable, Formula body) => All(variable, Call("V", F.Id("c")), body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
    private static Formula Both(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Land, Sp, Open, b, Close, Close);
    private static Formula Sum3(Formula a, Formula b, Formula c) => Plus2(Plus2(a, b), c);
    private static Formula Conjunction(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = Both(clauses[i], result);
        return result;
    }
    private static Formula Iterate(Formula map, Formula n, Formula a) =>
        Seq(Open, map, Close, Caret, Grp(n), Open, a, Close);

    private static Formula Original(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
        Arrow(Call("RawBalance", F.Id("U"), F.Id("c")), body));

    private static Formula OriginalWithProof(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
        All(F.Id("h"), Call("RawBalance", F.Id("U"), F.Id("c")), body));

    private static Formula Result() => Conjunction(
        Eqn(Read(D(1), D(1)), D(0)),
        Eqn(BetaOf(D(1)), D(0)),
        AllM(A, AllM(B, Eqn(Form(BetaOf(A), BetaOf(B)), Call("kernel", F.Id("c"), A, B)))),
        All(X, Call("E", M), All(Y, Call("E", M),
            Eqn(Call("anchoredForm", F.Id("c"), Call("markerLinear", F.Id("U"), X), Call("markerLinear", F.Id("U"), Y)), Call("anchoredForm", F.Id("c"), X, Y)))),
        AllM(A, Eqn(BetaOf(Mark(Mark(Mark(A)))), BetaOf(A))),
        All(X, Call("E", M), Arrow(Member(X, "Rad"), Member(Call("markerLinear", F.Id("U"), X), "Rad"))),
        AllM(A, Eqn(ROf(BetaOf(A)), BetaOf(Mark(A)))),
        AllM(A, Eqn(ROf(ROf(ROf(BetaOf(A)))), BetaOf(A))),
        AllM(A, Eqn(TDef(D(1), A), D(0))),
        AllM(A, Eqn(TDef(A, D(1)), D(0))),
        Eqn(Call("map", Call("mkQ", Call("radical", F.Id("c"))), Call("anchoredSpan", M)), Call("top", Call("Submodule", Real, Call("V", F.Id("c"))))),
        Eqn(Call("span", Real, Call("range", Call("beta", F.Id("c")))), Call("top", Call("Submodule", Real, Call("V", F.Id("c"))))),
        AllV(Z, Arrow(AllM(A, Eqn(Form(Z, BetaOf(A)), D(0))),
            Arrow(AllM(A, Eqn(Form(BetaOf(A), Z), D(0))), Eqn(Z, D(0))))),
        AllV(X, Eqn(ROf(ROf(ROf(X))), X)),
        AllV(X, AllV(Y, Eqn(Form(ROf(X), ROf(Y)), Form(X, Y)))),
        AllM(A, AllM(B, Eqn(Form(Minus2(BetaOf(A), BetaOf(B)),
            Minus2(BetaOf(A), BetaOf(B))),
            Seq(Frac, Grp(Plus2(Read(A, B), Read(B, A))), Grp(D(2)))))),
        AllM(A, AllM(U, Eqn(Sum3(Call("q", F.Id("c"), Product(A, U)),
            Call("q", F.Id("c"), Product(A, Mark(U))), Call("q", F.Id("c"), Product(A, Mark(Mark(U))))),
            Plus2(Three(Call("q", F.Id("c"), A)), Three(Call("q", F.Id("c"), U)))))),
        AllM(B, AllM(V, Eqn(Sum3(Call("r", F.Id("c"), Product(B, V)),
            Call("r", F.Id("c"), Product(B, Mark(V))), Call("r", F.Id("c"), Product(B, Mark(Mark(V))))),
            Plus2(Three(Call("r", F.Id("c"), B)), Three(Call("r", F.Id("c"), V)))))),
        AllM(A, AllM(B, AllM(U, AllM(V,
            Eqn(Sum3(Form(BetaOf(Product(A, U)), BetaOf(Product(B, V))),
                Form(BetaOf(Product(A, Mark(U))), BetaOf(Product(B, Mark(V)))),
                Form(BetaOf(Product(A, Mark(Mark(U)))), BetaOf(Product(B, Mark(Mark(V)))))),
                Plus2(Three(Form(BetaOf(A), BetaOf(B))), Three(Form(BetaOf(U), BetaOf(V))))))))),
        AllM(A, AllM(U, Eqn(Sum3(BetaOf(Product(A, U)),
            BetaOf(Product(A, Mark(U))), BetaOf(Product(A, Mark(Mark(U))))), Three(BetaOf(A))))),
        AllM(A, AllM(U, Eqn(Sum3(BetaOf(Product(A, U)),
            ROf(ROf(BetaOf(Product(A, Mark(U))))),
            ROf(BetaOf(Product(A, Mark(Mark(U)))))), Three(BetaOf(U))))),
        AllV(X, Eqn(Sum3(X, ROf(X), ROf(ROf(X))), D(0))),
        AllM(A, AllM(U, Both(
            Eqn(BetaOf(Product(A, Mark(U))),
                Sum3(BetaOf(A), ROf(BetaOf(U)), ROf(ROf(TDef(A, U))))),
            Eqn(BetaOf(Product(A, Mark(Mark(U)))),
                Sum3(BetaOf(A), ROf(ROf(BetaOf(U))), ROf(TDef(A, U))))))),
        AllM(A, AllM(B, AllM(U, AllM(V, Eqn(Form(TDef(A, U), TDef(B, V)), D(0)))))),
        AllV(X, AllV(Y, Arrow(Member(X, "W"), Arrow(Member(Y, "W"), Eqn(Form(X, Y), D(0)))))),
        Eqn(Call("map", Call("markerQuotient", F.Id("U"), F.Id("c"), F.Id("h")), Call("W", F.Id("c"))), Call("W", F.Id("c"))),
        Eqn(GammaOf(D(1)), D(0)),
        AllM(A, AllM(U, Eqn(GammaOf(Product(A, U)), Plus2(GammaOf(A), GammaOf(U))))),
        AllM(A, Eqn(GammaOf(Mark(A)), RhoOf(GammaOf(A)))),
        AllM(A, AllM(U, All(K, Seq(Mathbb, Grp(F.Id("N"))),
            Eqn(GammaOf(Product(A, Iterate(F.Id("U"), K, U))),
                Plus2(GammaOf(A), Iterate(Call("rho", F.Id("U"), F.Id("c"), F.Id("h")), K, GammaOf(U))))))),
        AllM(A, AllM(B, Arrow(Eqn(GammaOf(A), GammaOf(B)),
            Both(Eqn(Read(A, B), D(0)), Eqn(Read(B, A), D(0)))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw balance yields the actual Fourier defect quotient and additive marker descent.",
        H("Raw Anchored Fourier Defect Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-three-phase-balance"),
                DeclarationHandle.Create(Gid + "RawBalance"),
                H("The original raw balance hypotheses"),
                StatementSource.FromAuthor(Disp(Frame(Eqn(Call("RawBalance", F.Id("U"), F.Id("c")),
                    Conjunction(Eqn(Mark(D(1)), D(1)),
                        AllM(A, AllM(B, Seq(D(0), Sp, Le, Sp, Read(A, B)))),
                        AllM(A, Eqn(Read(A, A), D(0))),
                        AllM(A, AllM(B, AllM(U, AllM(V, RawBalanceFormula()))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("M has only a binary operation and a two-sided unit. U is an arbitrary self-map fixing the unit, and c is finite and real-valued. No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("raw-marker-readouts"),
                DeclarationHandle.Create(Gid + "raw_marker_readouts"),
                H("The comparison has derived marker invariance"),
                StatementSource.FromAuthor(Disp(Original(Conjunction(
                    AllM(U, AllM(V, Eqn(Read(Mark(U), Mark(V)), Read(U, V)))),
                    AllM(A, AllM(B, AllM(U, AllM(V,
                        Eqn(Read(Product(A, Mark(Mark(Mark(U)))), Product(B, Mark(Mark(Mark(V))))),
                            Read(Product(A, U), Product(B, V))))))),
                    AllM(U, AllM(Z, Both(
                        Eqn(Read(Mark(Mark(Mark(U))), Z), Read(U, Z)),
                        Eqn(Read(Z, Mark(Mark(Mark(U)))), Read(Z, U))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s(n)=c(U^n u,U^n v), the raw law at the two units gives s(n+1)+s(n+2)=2s(n). Apply ThreeWayBalance.nonneg_recurrence_constant directly, exchanging the summands. Subtracting consecutive original balance identities gives contextual invariance. Specializing either contextual input to the unit gives every row and column equality. These equalities supply the ordered anchored-kernel descent below. Only the readings have period three; the original marker need not have period three."))),
                DescribeRole.Theorem),
            Paragraph(Text("Let E be the full finite-support real space on M, e(a)=delta(a)-delta(1), and E0 the real span of the e(a). Put q(a)=c(a,1), r(a)=c(1,a), and kernel(a,b)=(q(a)+r(b)-c(a,b))/2. B0 is its bilinear extension to E. Rad is the intersection of the left and right radicals, V=E/Rad, pi is the quotient map, beta(a)=pi(e(a)), and B is the induced ordered bilinear form. S is the free linear extension of U. R is its induced operator on V.")),
            Paragraph(Text("Put T(a,u)=beta(a*u)-beta(a)-beta(u), W=span(range T), gamma(a)=beta(a) mod W, and let rho be the operator induced by R on V/W. All spans and quotients are real. Function images of subspaces are written pi(E0) and R(W). Superscripts on U and rho denote iteration, including the zeroth iterate.")),
            Describe.Lean(
                DescribeId.Create("raw-anchored-radical-descent"),
                DeclarationHandle.Create(Gid + "raw_anchored_radical_descent"),
                H("The original raw law constructs the ordered Fourier quotient"),
                StatementSource.FromAuthor(Disp(OriginalWithProof(Result()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unit basis vector lies in both radicals, so pi(E0)=V and the beta labels span V. Testing both ordered pairings against these labels gives joint nondegeneracy. The complete raw law supplies the q and r averages and the bilinear balance, hence the unweighted and inverse-weighted constraints. Solving their three-character system gives the two original phase children. Bilinear Fourier cancellation makes the cross-defect pairing zero; linear extension gives B(W,W)=0, while the phase identities give R(W)=W. The same W supplies the actual gamma product and marker identities. Its isotropy, the difference diagonal identity and comparison nonnegativity force both directed comparisons to vanish on each gamma fibre. Isotropy alone does not say that W is a radical."))),
                DescribeRole.Theorem))));

    private static Formula RawBalanceFormula() => Eqn(
        Sum3(Read(Product(A, U), Product(B, V)),
            Read(Product(A, Mark(U)), Product(B, Mark(V))),
            Read(Product(A, Mark(Mark(U))), Product(B, Mark(Mark(V))))),
        Plus2(Three(Read(A, B)), Three(Read(U, V))));

    private static Formula Frame(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp, body);
}
