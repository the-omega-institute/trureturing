using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawAnchoredRadicalDescentDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawAnchoredRadicalDescent.";
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
    private static Formula BetaOf(Formula a) => Call("beta", a);
    private static Formula ROf(Formula a) => Call("R", a);
    private static Formula GammaOf(Formula a) => Call("gamma", a);
    private static Formula RhoOf(Formula a) => Call("rho", a);
    private static Formula TDef(Formula a, Formula b) => Call("T", a, b);
    private static Formula Form(Formula a, Formula b) => Call("B", a, b);
    private static Formula Read(Formula a, Formula b) => Call("c", a, b);
    private static Formula Member(Formula a, string b) => Seq(a, Sp, InMacro, Sp, F.Id(b));
    private static Formula All(Formula variable, Formula carrier, Formula body) =>
        Seq(Open, Forall, Sp, variable, Colon, Sp, carrier, Comma, Sp, body, Close);
    private static Formula AllM(Formula variable, Formula body) => All(variable, M, body);
    private static Formula AllV(Formula variable, Formula body) => All(variable, F.Id("V"), body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Both(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Sum3(Formula a, Formula b, Formula c) => Plus2(Plus2(a, b), c);
    private static Formula Conjunction(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = Both(clauses[i], result);
        return result;
    }
    private static Formula Iterate(string map, Formula n, Formula a) =>
        Seq(F.Id(map), Caret, Grp(n), Open, a, Close);

    private static Formula Result() => Conjunction(
        Eqn(Read(D(1), D(1)), D(0)),
        Eqn(BetaOf(D(1)), D(0)),
        AllM(A, AllM(B, Eqn(Form(BetaOf(A), BetaOf(B)), Call("kernel", A, B)))),
        All(X, F.Id("E"), All(Y, F.Id("E"),
            Eqn(Call("B0", Call("S", X), Call("S", Y)), Call("B0", X, Y)))),
        AllM(A, Eqn(BetaOf(Mark(Mark(Mark(A)))), BetaOf(A))),
        All(X, F.Id("E"), Arrow(Member(X, "Rad"), Member(Call("S", X), "Rad"))),
        AllM(A, Eqn(ROf(BetaOf(A)), BetaOf(Mark(A)))),
        AllM(A, Eqn(ROf(ROf(ROf(BetaOf(A)))), BetaOf(A))),
        AllM(A, Eqn(TDef(D(1), A), D(0))),
        AllM(A, Eqn(TDef(A, D(1)), D(0))),
        Eqn(Call("pi", F.Id("E0")), F.Id("V")),
        Eqn(Call("span", Call("range", F.Id("beta"))), F.Id("V")),
        AllV(Z, Arrow(AllM(A, Eqn(Form(Z, BetaOf(A)), D(0))),
            Arrow(AllM(A, Eqn(Form(BetaOf(A), Z), D(0))), Eqn(Z, D(0))))),
        AllV(X, Eqn(ROf(ROf(ROf(X))), X)),
        AllV(X, AllV(Y, Eqn(Form(ROf(X), ROf(Y)), Form(X, Y)))),
        AllM(A, AllM(B, Eqn(Form(Minus2(BetaOf(A), BetaOf(B)),
            Minus2(BetaOf(A), BetaOf(B))),
            Seq(Frac, Grp(Plus2(Read(A, B), Read(B, A))), Grp(D(2)))))),
        AllM(A, AllM(U, Eqn(Sum3(Call("q", Product(A, U)),
            Call("q", Product(A, Mark(U))), Call("q", Product(A, Mark(Mark(U))))),
            Plus2(Three(Call("q", A)), Three(Call("q", U)))))),
        AllM(B, AllM(V, Eqn(Sum3(Call("r", Product(B, V)),
            Call("r", Product(B, Mark(V))), Call("r", Product(B, Mark(Mark(V))))),
            Plus2(Three(Call("r", B)), Three(Call("r", V)))))),
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
        Eqn(Call("R", F.Id("W")), F.Id("W")),
        Eqn(GammaOf(D(1)), D(0)),
        AllM(A, AllM(U, Eqn(GammaOf(Product(A, U)), Plus2(GammaOf(A), GammaOf(U))))),
        AllM(A, Eqn(GammaOf(Mark(A)), RhoOf(GammaOf(A)))),
        AllM(A, AllM(U, All(K, Seq(Mathbb, Grp(F.Id("N"))),
            Eqn(GammaOf(Product(A, Iterate("U", K, U))),
                Plus2(GammaOf(A), Iterate("rho", K, GammaOf(U))))))),
        AllM(A, AllM(B, Arrow(Eqn(GammaOf(A), GammaOf(B)),
            Both(Eqn(Read(A, B), D(0)), Eqn(Read(B, A), D(0)))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw balance yields the actual Fourier defect quotient and additive marker descent.",
        H("Raw Anchored Fourier Defect Descent"),
        Blocks(
            Paragraph(Text("Let E be the full finite-support real space on M, e(a)=delta(a)-delta(1), and E0 the real span of the e(a). Put q(a)=c(a,1), r(a)=c(1,a), and kernel(a,b)=(q(a)+r(b)-c(a,b))/2. B0 is its bilinear extension to E. Rad is the intersection of the left and right radicals, V=E/Rad, pi is the quotient map, beta(a)=pi(e(a)), and B is the induced ordered bilinear form. S is the free linear extension of U. R is its induced operator on V.")),
            Paragraph(Text("Put T(a,u)=beta(a*u)-beta(a)-beta(u), W=span(range T), gamma(a)=beta(a) mod W, and let rho be the operator induced by R on V/W. All spans and quotients are real. Function images of subspaces are written pi(E0) and R(W). Superscripts on U and rho denote iteration, including the zeroth iterate.")),
            Describe.Lean(
                DescribeId.Create("raw-anchored-radical-descent"),
                DeclarationHandle.Create(Gid + "raw_anchored_radical_descent"),
                H("The original raw law constructs the ordered Fourier quotient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
                    OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
                    F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
                    F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
                    Arrow(Call("RawBalance", F.Id("U"), F.Id("c")), Result())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unit basis vector lies in both radicals, so pi(E0)=V and the beta labels span V. Testing both ordered pairings against these labels gives joint nondegeneracy. The complete raw law supplies the q and r averages and the bilinear balance, hence the unweighted and inverse-weighted constraints. Solving their three-character system gives the two original phase children. Bilinear Fourier cancellation makes the cross-defect pairing zero; linear extension gives B(W,W)=0, while the phase identities give R(W)=W. The same W supplies the actual gamma product and marker identities. Its isotropy, the difference diagonal identity and comparison nonnegativity force both directed comparisons to vanish on each gamma fibre. Isotropy alone does not say that W is a radical."))),
                DescribeRole.Theorem),
            Paragraph(Text("Only a binary operation with a two-sided unit is imposed on M. RawBalance means U(1)=1, c(a,b)>=0, c(a,a)=0, and the complete four-variable sum of c(a*U^k(u),b*U^k(v)) for k=0,1,2 equals 3c(a,b)+3c(u,v). No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.")),
            Paragraph(Text("Let N={a:gamma(a)=0} and K={(a,b):gamma(a)=gamma(b)}. The two directed comparison bounds on K are |B(beta(a)-beta(b),beta(z))|<=3r(z)/2 and |B(beta(z),beta(a)-beta(b))|<=3q(z)/2. The algebraic operator J=(2R+I)/sqrt(3) has square -I. For each real functional alpha, ell=alpha-i alpha J intertwines R with the explicit primitive cube root. The complete original children remain in N. The existing bounded_phase_recursion_vanishes is applied separately to both ordered functionals, using all finite history depths and the bound normSq(ell(beta(n)))<=10L^2.")),
            Describe.Lean(
                DescribeId.Create("raw-zero-fibre-vanishes"),
                DeclarationHandle.Create(Gid + "raw_zero_fibre_vanishes"),
                H("The actual zero fibre has zero anchored vector"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
                    OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
                    F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
                    F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
                    Arrow(Call("RawBalance", F.Id("U"), F.Id("c")),
                        AllM(U, Arrow(Member(U, "N"), Eqn(BetaOf(U), D(0)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both ordered pairings vanish by the two actual history applications. Joint nondegeneracy against the spanning beta labels then gives beta(u)=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-gamma-fibre-collapse"),
                DeclarationHandle.Create(Gid + "raw_gamma_fibre_collapse"),
                H("The original gamma fibre determines beta"),
                StatementSource.FromAuthor(Disp(AllM(A, AllM(B,
                    Arrow(Call("RawBalance", F.Id("U"), F.Id("c")),
                        Arrow(Eqn(GammaOf(A), GammaOf(B)), Eqn(BetaOf(A), BetaOf(B)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed ordered functional, take the supremum of its absolute beta difference over the same actual K. The original label d=U(a)*U(U(a)) has gamma(d)=-gamma(a), so a*d and b*d lie in N; d itself need not. The unweighted identity makes the k=0 child zero and bounds the other two children by that same supremum. Its 2/3 contraction forces zero. Apply this argument in both pairing orders."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-directed-comparison-descent"),
                DeclarationHandle.Create(Gid + "raw_directed_comparison_descent"),
                H("All directed readouts descend along the actual fibres"),
                StatementSource.FromAuthor(Disp(AllM(A, AllM(B,
                    Arrow(Call("RawBalance", F.Id("U"), F.Id("c")),
                        Arrow(Eqn(GammaOf(A), GammaOf(B)), Conjunction(
                            Eqn(Call("q", A), Call("q", B)),
                            Eqn(Call("r", A), Call("r", B)),
                            AllM(Z, Eqn(Read(A, Z), Read(B, Z))),
                            AllM(Z, Eqn(Read(Z, A), Read(Z, B)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of beta and the vanishing cross comparisons give equality of q and r. Substitution in the original ordered kernel then gives both complete rows and columns."))),
                DescribeRole.Theorem),
            Paragraph(Text("The full Hilbert representation criterion remains open. The comparison must still be constructed on the actual additive image, with translation invariance, the parallelogram law and Hilbert realization. The minimal unitary uniqueness, zero-comparison congruence and torsion-free Eisenstein conclusions are not asserted here.")))));
}
