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
    private static Formula Iterate(Formula map, Formula n, Formula a) =>
        Seq(Open, map, Close, Caret, Grp(n), Open, a, Close);

    private static Formula Original(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp,
        Arrow(Call("RawBalance", F.Id("U"), F.Id("c")), body));

    private static Formula Visible => Call("visibleGroup", F.Id("U"), F.Id("c"), F.Id("h"));
    private static Formula Comparison(Formula x, Formula y) => Call("visibleComparison", F.Id("U"), F.Id("c"), F.Id("h"), x, y);
    private static Formula Energy(Formula x) => Call("visibleEnergy", F.Id("U"), F.Id("c"), F.Id("h"), x);
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
            Paragraph(Text("Let E be the full finite-support real space on M, e(a)=delta(a)-delta(1), and E0 the real span of the e(a). Put q(a)=c(a,1), r(a)=c(1,a), and kernel(a,b)=(q(a)+r(b)-c(a,b))/2. B0 is its bilinear extension to E. Rad is the intersection of the left and right radicals, V=E/Rad, pi is the quotient map, beta(a)=pi(e(a)), and B is the induced ordered bilinear form. S is the free linear extension of U. R is its induced operator on V.")),
            Paragraph(Text("Put T(a,u)=beta(a*u)-beta(a)-beta(u), W=span(range T), gamma(a)=beta(a) mod W, and let rho be the operator induced by R on V/W. All spans and quotients are real. Function images of subspaces are written pi(E0) and R(W). Superscripts on U and rho denote iteration, including the zeroth iterate.")),
            Describe.Lean(
                DescribeId.Create("raw-anchored-radical-descent"),
                DeclarationHandle.Create(Gid + "raw_anchored_radical_descent"),
                H("The original raw law constructs the ordered Fourier quotient"),
                StatementSource.FromAuthor(Disp(OriginalWithProof(Result()))),
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
                StatementSource.FromAuthor(Disp(Original(AllM(A, AllM(B,
                    Arrow(Eqn(GammaOf(A), GammaOf(B)), Eqn(BetaOf(A), BetaOf(B)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed ordered functional, take the supremum of its absolute beta difference over the same actual K. The original label d=U(a)*U(U(a)) has gamma(d)=-gamma(a), so a*d and b*d lie in N; d itself need not. The unweighted identity makes the k=0 child zero and bounds the other two children by that same supremum. Its 2/3 contraction forces zero. Apply this argument in both pairing orders."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-directed-comparison-descent"),
                DeclarationHandle.Create(Gid + "raw_directed_comparison_descent"),
                H("All directed readouts descend along the actual fibres"),
                StatementSource.FromAuthor(Disp(Original(AllM(A, AllM(B,
                    Arrow(Eqn(GammaOf(A), GammaOf(B)), Conjunction(
                        Eqn(Call("q", F.Id("c"), A), Call("q", F.Id("c"), B)),
                        Eqn(Call("r", F.Id("c"), A), Call("r", F.Id("c"), B)),
                        AllM(Z, Eqn(Read(A, Z), Read(B, Z))),
                        AllM(Z, Eqn(Read(Z, A), Read(Z, B)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of beta and the vanishing cross comparisons give equality of q and r. Substitution in the original ordered kernel then gives both complete rows and columns."))),
                DescribeRole.Theorem),
            Paragraph(Text("The actual image A=gamma(M) is an additive subgroup of V/W: the original product supplies sums and U(a)*U(U(a)) supplies negatives. Let tau be rho restricted to A. For x,y in A, choose original labels representing them and put C(x,y)=c(a,b). The complete row and column descent proves that this is independent of both choices and that C(gamma(a),gamma(b))=c(a,b). Nonnegativity, diagonal zero and the full four-variable balance pass to this same C with group addition and tau.")),
            Describe.Lean(
                DescribeId.Create("raw-visible-translation-invariant"),
                DeclarationHandle.Create(Gid + "raw_visible_translation_invariant"),
                H("The actual directed comparison is translation invariant"),
                StatementSource.FromAuthor(Disp(OriginalWithProof(
                    All(X, Visible, All(Y, Visible, All(Z, Visible,
                        Eqn(Comparison(Plus2(X, Z), Plus2(Y, Z)), Comparison(X, Y)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed x,y put f(t)=C(x+t,y+t) and m=inf(range f). Nonnegativity bounds m below. The full balance with equal last operands gives f(t+w)<=3f(t)-2m. Taking w=s-t yields (f(s)+2m)/3<=f(t) for every t; the infimum property forces f(s)=m. In particular f(z)=f(0). This uses the constructed actual image and comparison."))),
                DescribeRole.Theorem),
            Paragraph(Text("Put f(x)=C(x,0). Translation invariance gives C(x,y)=f(x-y). The actual restricted marker tau satisfies tau^2=-I-tau and f(tau(x))=f(x); the original balance gives the three-phase equation for f. The frozen three_way_quadratic_structure applies directly to this same additive group, restricted marker, nonnegative energy and full three-phase equation. It supplies the quadratic map without repeating its evenness or parallelogram proof.")),
            Describe.Lean(
                DescribeId.Create("raw-visible-quadratic"),
                DeclarationHandle.Create(Gid + "raw_visible_quadratic"),
                H("The actual comparison is an integer quadratic distance"),
                StatementSource.FromAuthor(Disp(OriginalWithProof(Seq(
                    Exists, Sp, F.Id("Q"), Colon, Sp,
                    Call("QuadraticMap", Seq(Mathbb, Grp(F.Id("Z"))), Visible, Real), Comma, Sp,
                    Both(All(X, Visible, Eqn(Call("Q", X), Energy(X))),
                        All(X, Visible, All(Y, Visible,
                            Eqn(Comparison(X, Y), Call("Q", Minus2(X, Y)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the existing three_way_quadratic_structure with the actual visibleGroup, visibleMarker and visibleEnergy. Its returned Q agrees pointwise with this same energy. Translation invariance then identifies the original descended comparison with Q(x-y). This application is a consumed binding and supplies no new mathematical-content witness."))),
                DescribeRole.Theorem),
            Paragraph(Text("RawHilbertRepresentation(U,c) consists of a carrier H with its normed additive commutative group, complex inner-product space and completeness instances, together with an original-label map F:M->H. Its fields are F(1)=0, F(a*b)=F(a)+F(b), F(Ua)=omega F(a), c(a,b)=norm(F(a)-F(b))^2 and topologicalClosure(span_C(range F))=top. Here omega is the existing explicit complex number (-1/2,sqrt(3)/2), and the Lean inner product is conjugate-linear in its first variable. The represented distances and unitary uniqueness are independent of that convention.")),
            Describe.Lean(
                DescribeId.Create("raw-hilbert-characterization"),
                DeclarationHandle.Create(Gid + "raw_hilbert_characterization"),
                H("The complete original-domain Hilbert criterion and minimal uniqueness"),
                StatementSource.FromAuthor(Disp(HilbertCriterion())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen three_way_hilbert_characterization is applied to exactly visibleGroup(U,c,h), visibleMarker(U,c,h) and visibleEnergy(U,c,h). Composing its additive label with visibleLabel gives the original F, and surjectivity of visibleLabel identifies the two actual ranges. The converse quantifies over any complete complex Hilbert carrier and original label map with the product, phase and distance identities; it imposes no minimality or factorization hypothesis. It applies the same supplier to the identity representation of that carrier, with omega scalar multiplication, and substitutes the two original differences into its three-way norm law. The unit-zero identity already follows from product additivity at the unit. For any other original model, equality of gamma implies zero original comparison and hence equal labels. This proves factorization through the same actual visible group; no factorization certificate is assumed in the raw model. The supplier's unique complex-linear isometry then gives the unique original-label-preserving unitary, including models in independent universes."))),
                DescribeRole.Theorem),
            Paragraph(Text("Eisenstein is the actual subalgebra Algebra.adjoin_Z({omega}) inside the complex numbers. visibleImage(U,c,h,R) has carrier range(R.label) and inherits complex scalar multiplication restricted to Eisenstein. Algebra.adjoin_induction proves that this actual image is closed: integers use additive scalar multiplication, omega uses the actual marker phase, and sum/product closure uses the same range. omegaScalar is omega as an element of that generated subring. zeroComparisonSetoid(U,c,h) has literal relation c(a,b)=0; VisibleQuotient is its Quotient. The quotient group is transported through the proved bijection to visibleGroup, and the Eisenstein module is transported through the actual image equivalence. No new scalar ring, recipe, completion point or physical operation is supplied.")),
            Paragraph(Text("If the chosen Hilbert labels of a and b agree, the distance formula gives equality of every original row and every original column. This gives equality of q and r and annihilates both ordered B pairings of beta(a)-beta(b) against every beta label. The proved joint nondegeneracy forces beta(a)=beta(b), hence gamma(a)=gamma(b). Thus the actual energy is definite, and c(a,b)=0 is exactly equality of gamma. The original product and marker formulas give the congruence and all visible algebra identities. The linear image equivalence identifies the actual quotient with the label image. A nonzero Eisenstein scalar stays nonzero in the complex numbers, so its action on the Hilbert carrier has zero kernel; the same holds on the image and on the transported quotient. The zero model is included. No isotropic-to-radical shortcut or assertion W=0 is used.")),
            Paragraph(Text("These are mathematical consequences of the full original balance under U(1)=1, with every finite history depth allowed. The original operation may remain nonassociative and noncommutative and U cubed need not be the identity on original recipes. The group and module laws identify only their zero-comparison classes. Completion and scalar extension supply no extra actual recipes or physical controls. The whole source atom awaits independent cumulative admission and canonical deposit/coverage.")))));

    private static Formula Frame(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        F.Id("U"), Colon, Sp, M, Sp, To, Sp, M, Comma, Sp,
        F.Id("c"), Colon, Sp, M, Sp, To, Sp, M, Sp, To, Sp, Real, Comma, Sp, body);
    private static Formula Model => Call("RawHilbertRepresentation", F.Id("U"), F.Id("c"));
    private static Formula Label(Formula model, Formula a) => Call("label", model, a);
    private static Formula HilbertPart()
    {
        var s = F.Id("S"); var t = F.Id("T"); var e = F.Id("j");
        var unique = Arrow(Call("RawBalance", F.Id("U"), F.Id("c")),
            All(s, Model, All(t, Model, Seq(Exists, Sp, Bang, Sp, e, Colon, Sp,
                Call("LinearIsometryEquiv", Seq(Mathbb, Grp(F.Id("C"))), Call("carrier", s), Call("carrier", t)),
                Comma, Sp, AllM(A, Eqn(Seq(e, Open, Label(s,A), Close), Label(t,A)))))));
        return Conjunction(
            Seq(Open, Call("RawBalance", F.Id("U"), F.Id("c")), Sp, Iff, Sp, Call("Nonempty", Model), Close),
            GeneralConverse(), unique);
    }
    private static Formula GeneralConverse()
    {
        var h = F.Id("H"); var f = F.Id("F");
        Formula label(Formula a) => Seq(f, Open, a, Close);
        Formula distance = Seq(Call("norm", Minus2(label(A),label(B))), Caret, Grp(D(2)));
        return All(h, F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup",h), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace",Seq(Mathbb,Grp(F.Id("C"))),h), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace",h), CloseBracket, Comma, Sp,
            All(f, Seq(M,Sp,To,Sp,h),
                Arrow(AllM(A,AllM(B,Eqn(label(Product(A,B)),Plus2(label(A),label(B))))),
                    Arrow(AllM(A,Eqn(label(Mark(A)),Seq(Call("omega"),Sp,Cdot,Sp,label(A)))),
                        Arrow(AllM(A,AllM(B,Eqn(Read(A,B),distance))),
                            Call("RawBalance", F.Id("U"), F.Id("c"))))))));
    }
    private static Formula QuadraticResult() => Seq(
        Exists, Sp, F.Id("Q"), Colon, Sp,
        Call("QuadraticMap", Seq(Mathbb, Grp(F.Id("Z"))), Visible, Real), Comma, Sp,
        Both(All(X, Visible, Eqn(Call("Q", X), Energy(X))),
            All(X, Visible, All(Y, Visible, Eqn(Comparison(X,Y),Call("Q",Minus2(X,Y)))))));
    private static Formula HilbertCriterion() => Frame(Arrow(Eqn(Mark(D(1)),D(1)),
        Both(HilbertPart(), All(F.Id("h"), Call("RawBalance",F.Id("U"),F.Id("c")),
            Both(VisibleAlgebra(),QuadraticResult())))));
    private static Formula Quot => Call("VisibleQuotient", F.Id("U"), F.Id("c"), F.Id("h"));
    private static Formula QClass(Formula a) => Call("Quotientmk", Call("zeroComparisonSetoid", F.Id("U"), F.Id("c"), F.Id("h")), a);
    private static Formula VisibleAlgebra()
    {
        var d=F.Id("d"); var j=F.Id("j"); var s=F.Id("s");
        var model=Call("groupModel", F.Id("U"), F.Id("c"), F.Id("h"));
        return Conjunction(
            AllM(A, AllM(B, Seq(Eqn(Read(A,B),D(0)), Sp, Iff, Sp, Eqn(GammaOf(A),GammaOf(B))))),
            AllM(A, AllM(B, AllM(U, AllM(V, Arrow(Eqn(Read(A,B),D(0)), Arrow(Eqn(Read(U,V),D(0)),
                Eqn(Read(Product(A,U), Product(B,V)), D(0)))))))),
            AllM(A, AllM(B, Arrow(Eqn(Read(A,B),D(0)), Eqn(Read(Mark(A),Mark(B)),D(0))))),
            AllM(A, AllM(B, AllM(d, Eqn(Read(Product(Product(A,B),d), Product(A,Product(B,d))),D(0))))),
            AllM(A, AllM(B, Eqn(Read(Product(A,B),Product(B,A)),D(0)))),
            AllM(A, Eqn(Read(Mark(Mark(Mark(A))),A),D(0))),
            AllM(A, Eqn(QClass(Product(Mark(A),Mark(Mark(A)))), Seq(Minus,QClass(A)))),
            AllM(A, AllM(B, Eqn(QClass(Product(A,B)),Plus2(QClass(A),QClass(B))))),
            Seq(Exists, Sp, j, Colon, Sp, Call("LinearEquiv", Call("Eisenstein"), Quot,
                Call("visibleImage", F.Id("U"), F.Id("c"), F.Id("h"),model)), Comma, Sp,
                AllM(A, Eqn(Call("val", Seq(j,Open,QClass(A),Close)), Label(model,Call("visibleLabel",F.Id("U"),F.Id("c"),F.Id("h"),A))))),
            AllM(A,Eqn(QClass(Mark(A)),Seq(Call("omegaScalar"),Sp,Cdot,Sp,QClass(A)))),
            All(s,Call("Eisenstein"),All(X,Quot,Arrow(Seq(s,Sp,Neq,Sp,D(0)),
                Arrow(Eqn(Seq(s,Sp,Cdot,Sp,X),D(0)),Eqn(X,D(0)))))));
    }
}
