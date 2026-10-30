using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class MarkedPoissonCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual History Transfer and Signed Coefficient Extraction", H("Actual History Transfer and Signed Coefficient Extraction"), Blocks(
Describe.Lean(DescribeId.Create("markedhistoryalgebra-edgetilt"), DeclarationHandle.Create(Module + "edgeTilt"),
            H("edgeTilt"), StatementSource.FromAuthor(Disp(TFHQ("M k", TFHV("Nat"), TFHQ("m", TFHMarks, TFHQ("zp zm", TFHTilts, TFHQ("x y", TFHCall("Vertex", TFHV("M")), TFHEqn(TFHCall("edgeTilt", TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("x"), TFHV("y")), TFHCall("markedFactors", TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("x"), TFHV("y"))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The factor is the product over all marked rows j of zplus(j) when the departure is inl(m(j)) and the destination parity is 1, and zminus(j) when that departure has destination parity -1; each other factor is 1."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-sparse"), DeclarationHandle.Create(Module + "sparse"),
            H("sparse"), StatementSource.FromAuthor(Disp(TFHQ("M k", TFHV("Nat"), TFHQ("m", TFHMarks, TFHQ("a", TFHTilts, TFHQ("x", TFHCall("Vertex", TFHV("M")), TFHEqn(TFHCall("sparse", TFHV("m"), TFHV("a"), TFHV("x")), TFHCall("markedSum", TFHV("m"), TFHV("a"), TFHV("x"))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("markedSum is the finite sum of a(j) over indices for which x = inl(m(j)); all other summands are zero. This definition allows repeated marks."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-count-monomial"), DeclarationHandle.Create(Module + "count_monomial"),
            H("count monomial"), StatementSource.FromAuthor(Disp(TFHQ("M k s", TFHV("Nat"), TFHQ("e", TFHCall("Experiment"), TFHQ("m", TFHMarks, TFHQ("zp zm", TFHTilts, TFHQ("o", TFHCall("Obs", TFHV("M"), TFHV("s"), TFHV("e")), TFHEqn(TFHCall("countMonomial", TFHV("e"), TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("o")), TFHCall("edgeProduct", TFHV("e"), TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("o")))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("countMonomial is the product over j of zplus(j)^count(e,o,m(j),1) times zminus(j)^count(e,o,m(j),-1). edgeProduct is the product over the s edges of edgeTilt at their ordered endpoints. Natural powers include zero tilts and zero counts."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-edgetilt-eq-affine"), DeclarationHandle.Create(Module + "edgeTilt_eq_affine"),
            H("edgeTilt eq affine"), StatementSource.FromAuthor(Disp(TFHQ("M k", TFHV("Nat"), TFHQ("m", TFHMarks, TFHImp(TFHCall("injective", TFHV("m")), TFHQ("zp zm", TFHTilts, TFHQ("x y", TFHCall("Vertex", TFHV("M")), TFHEqn(TFHCall("edgeTilt", TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("x"), TFHV("y")), TFHCall("affineTilt", TFHV("m"), TFHV("zp"), TFHV("zm"), TFHV("x"), TFHV("y")))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("With u(j) = (zplus(j)+zminus(j))/2-1 and v(j) = (zplus(j)-zminus(j))/2, affineTilt equals 1+sparse(m,u,x)+sparse(m,v,x) chi(y). Distinct marks make at most one departure row active."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-sparse-sum"), DeclarationHandle.Create(Module + "sparse_sum"),
            H("sparse sum"), StatementSource.FromAuthor(Disp(TFHQ("M k", TFHV("Nat"), TFHQ("m", TFHMarks, TFHQ("f", TFHFn(TFHCall("Vertex", TFHV("M")), TFHV("Complex")), TFHQ("a", TFHTilts, TFHEqn(TFHCall("stateSparseSum", TFHV("f"), TFHV("m"), TFHV("a")), TFHCall("markedWeightedSum", TFHV("f"), TFHV("m"), TFHV("a"))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The left side is the sum over all x of f(x) sparse(m,a,x); the right side is the sum over all j of f(inl(m(j))) a(j). No injectivity condition is needed."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-endpointweight"), DeclarationHandle.Create(Module + "endpointWeight"),
            H("endpointWeight"), StatementSource.FromAuthor(Disp(TFHEndpointDef())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a finite state type X, endpointWeight(c,K,n,y) is c times the sum over all functions o : Fin(n+1) -> X ending at y of the product of K on the n consecutive ordered edges."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-endpoint-zero"), DeclarationHandle.Create(Module + "endpoint_zero"),
            H("endpoint zero"), StatementSource.FromAuthor(Disp(TFHEndpoint("endpoint_zero"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A length-zero path has mass c at each endpoint, including when c is zero."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-endpoint-next"), DeclarationHandle.Create(Module + "endpoint_next"),
            H("endpoint next"), StatementSource.FromAuthor(Disp(TFHEndpoint("endpoint_next"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("endpointConvolution is the sum over x of endpointWeight(c,K,n,x) K(x,y). Appending the final state is a bijection of complete histories."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-endpoint-total"), DeclarationHandle.Create(Module + "endpoint_total"),
            H("endpoint total"), StatementSource.FromAuthor(Disp(TFHEndpoint("endpoint_total"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("endpointSum sums endpointWeight over all final states. historySum is c times the sum of the edge-product weights of every complete length-n history."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-tilt-norms"), DeclarationHandle.Create(Module + "tilt_norms"),
            H("tilt norms"), StatementSource.FromAuthor(Disp(TFHQ("k", TFHV("Nat"), TFHQ("zp zm", TFHTilts, TFHQ("R", TFHV("Real"), TFHImp(TFHCall("tiltRadius", TFHV("zp"), TFHV("zm"), TFHV("R")), TFHQ("j", TFHFinF(TFHV("k")), TFHAndF(TFHLe(TFHNorm(TFHSubF(TFHDivF(TFHAdd(TFHCall("eval", TFHV("zp"), TFHV("j")), TFHCall("eval", TFHV("zm"), TFHV("j"))), TFHN(2)), TFHN(1))), TFHAdd(TFHV("R"), TFHN(1))), TFHLe(TFHNorm(TFHDivF(TFHSubF(TFHCall("eval", TFHV("zp"), TFHV("j")), TFHCall("eval", TFHV("zm"), TFHV("j"))), TFHN(2))), TFHV("R")))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("tiltRadius means both coordinate vectors have norms at most R at every index. The symmetric tilt has norm at most R+1 and the antisymmetric tilt has norm at most R."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-marked-sum-norm"), DeclarationHandle.Create(Module + "marked_sum_norm"),
            H("marked sum norm"), StatementSource.FromAuthor(Disp(TFHQ("k", TFHV("Nat"), TFHQ("D", TFHV("Real"), TFHQ("a", TFHTilts, TFHImp(TFHAndF(TFHSmallK, TFHLe(TFHN(0), TFHV("D")), TFHCall("coordinateBound", TFHV("a"), TFHV("D"))), TFHLe(TFHNorm(TFHCall("sum", TFHV("a"))), TFHMul(TFHN(2), TFHV("D"))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("coordinateBound means norm(a(j)) <= D for every j. One or two rows cost at most 2D in the sum norm."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("markedhistoryalgebra-profile-sum-zero"), DeclarationHandle.Create(Module + "profile_sum_zero"),
            H("profile sum zero"), StatementSource.FromAuthor(Disp(TFHProfile(TFHImp(TFHAndF(TFHLe(TFHN(1), TFHV("q")), TFHLtF(TFHV("q"), TFHV("M")), TFHLtF(TFHN(0), TFHV("r")), TFHLtF(TFHV("r"), TFHN(1)), TFHLtF(TFHCall("compensation", TFHV("M"), TFHV("q"), TFHV("r")), TFHN(1))), TFHEqn(TFHCall("profileSum", TFHV("r"), TFHV("S")), TFHN(0))), "M q"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("profileSum is the sum over all 2M native states of b(r,S,x). This is the zero-mean compensated profile of the finite stochastic model."))), DescribeRole.Theorem),
Describe.Lean(
                DescribeId.Create("marked-tilt-u"), DeclarationHandle.Create(Module + "tiltU"),
                H("Symmetric tilt"), StatementSource.FromAuthor(TFTiltFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each marked positive departure state has two arbitrary complex tilt coordinates, "
                    + "one for each destination parity. The symmetric coordinate is their half-sum minus one."))),
                DescribeRole.Definition),
Describe.Lean(
                DescribeId.Create("marked-tilt-v"), DeclarationHandle.Create(Module + "tiltV"),
                H("Antisymmetric tilt"), StatementSource.FromAuthor(TFTiltFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The antisymmetric coordinate is half the difference of the positive and negative destination tilts."))),
                DescribeRole.Definition),
Describe.Lean(
                DescribeId.Create("marked-drift-a"), DeclarationHandle.Create(Module + "driftA"),
                H("Total-mass drift"), StatementSource.FromAuthor(TFDriftFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The drift A averages u_j + b_j v_j over the 2M states. Here b_j is the native compensated "
                    + "profile at the marked positive state: b is r on positive support states, -c on the positive complement, and zero on negative states; c = rq/(M-q). Marks may lie in the support or its complement."))),
                DescribeRole.Definition),
Describe.Lean(
                DescribeId.Create("marked-drift-b"), DeclarationHandle.Create(Module + "driftB"),
                H("Endpoint-parity drift"), StatementSource.FromAuthor(TFDriftFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The drift B averages v_j + b_j u_j over the same state space. The compensating profile "
                    + "has zero total mass and vanishes on negative states."))),
                DescribeRole.Definition),
Describe.Lean(
                DescribeId.Create("actual-marked-pgf"), DeclarationHandle.Create(Module + "actualPGF"),
                H("Actual count generating function"), StatementSource.FromAuthor(TFPgfFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum ranges over all complete histories of T transitions, with the native uniform-start "
                    + "path mass. The positive and negative exponents count departures from each marked state "
                    + "followed by the corresponding destination parity. These counts share one history. "
                    + "A history is a function from Fin(T+1) to Fin(M) + Fin(M). Its mass w_T is (2M)^(-1) times the product of (1 + b(x) chi(y))/(2M) over its T edges, where chi is 1 on positive states and -1 on negative states. C_j^+ and C_j^- count edges whose departure is the positive state m(j) and whose destination chi is respectively 1 and -1. The symbol z denotes the pair (z^+, z^-). Natural powers include zero tilt coordinates and use the convention zero to the zeroth power equals one."))),
                DescribeRole.Definition),

Describe.Lean(DescribeId.Create("forward-marked-state"), DeclarationHandle.Create(Module + "forwardState"),
 H("Forward endpoint state"), StatementSource.FromAuthor(TFForwardStateFormula()), AssessedProvenance.FromRepo(),
 Blocks(Paragraph(Text("The row-coordinate state begins at (1,0). At each step its first coordinate becomes (1+A)x+A y and its second becomes B x+B y. The coordinates are the total and parity coefficients of the actual tilted endpoint density."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("forward-marked-matrix"), DeclarationHandle.Create(Module + "forwardMatrix"),
 H("Forward transfer matrix"), StatementSource.FromAuthor(TFForwardMatrixFormula()), AssessedProvenance.FromRepo(),
 Blocks(Paragraph(Text("The entries, listed in row order, are 1+A, B, A, B. At zero drift this is the projection onto the first coordinate."))), DescribeRole.Definition),
Describe.Lean(DescribeId.Create("actual-forward-path-transfer"), DeclarationHandle.Create(Module + "actual_marked_path_transfer"),
 H("Actual path transfer identity"), StatementSource.FromAuthor(TFForwardTransferFormula()), AssessedProvenance.FromRepo(),
 Blocks(Paragraph(Text("For every natural T, including zero, and every complex tilt, actualPGF equals both the first coordinate of forwardState and the (0,0) entry of the T-th power of forwardMatrix. A and B are the compensated drifts of the same fixed support and marked rows. The proof sums actual complete-history weights through their endpoint density. No bound on the tilts and no restriction to one or two rows is required for this exact identity."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("markedpoissoncoefficient-finite-count-poisson-relative"), DeclarationHandle.Create(Module + "finite_count_poisson_relative"),
            H("finite count poisson relative"), StatementSource.FromAuthor(Disp(Coefficient())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Omega is an arbitrary finite history carrier. w is an arbitrary real weight; nonnegativity is not required. cp and cm are natural count vectors. positiveMeanLowerBounds means that each muplus(j) and muminus(j) is positive and at least kappa L/2. coordinateCountBound means every prescribed coordinate is at most Czero L. tiltRadius bounds both complex tilt vectors coordinatewise. countPGF is the weighted sum of the count monomials; poissonPGF is exp(sum_j(muplus(j)(zp(j)-1)+muminus(j)(zm(j)-1))). signedPoissonScale is exp of the real part of that same exponent. P sums w over the simultaneous exact-count event. Q is the product over both signs and all j of exp(-mu) mu^n/n!. The displayed constant uses pi, the circle constant. The proof extracts coefficients on a product torus at positive radii (n+1)/mu, then applies the factorial estimate including n=0. It permits zero tilts and rare original point masses."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => D(n);
    private static Formula Call(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula Q(string names, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { V(s) } : new[] { Comma, V(s) })]), Colon, type, Comma, Sp, body);
    private static Formula Fn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula SubF(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula DivF(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula AndF(params Formula[] xs) => Join(xs, Land);
    private static Formula Join(Formula[] xs, Formula op)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, op, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula AbsF(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula FinF(Formula a) => Call("Fin", a);
    private static Formula Tilts => Fn(FinF(V("k")), V("Complex"));
    private static Formula SmallK => Seq(Open, V("k"), Eq, N(1), Sp, Lor, Sp, V("k"), Eq, N(2), Close);
    private static Formula Coefficient()
    {
        Formula kap = V("kappa"), c = V("Czero"), l = V("L"), eps = V("epsilon");
        Formula zp = V("zp"), zm = V("zm"), w = V("w"), cp = V("cp"), cm = V("cm"), mp = V("muplus"), mm = V("muminus");
        Formula radius = DivF(Mul(N(2), Add(c, N(1))), kap);
        Formula envelope = Q("zp zm", Tilts, Imp(Call("tiltRadius", zp, zm, radius), Le(
            Norm(SubF(Call("countPGF", w, cp, cm, zp, zm), Call("poissonPGF", mp, mm, zp, zm))),
            Mul(eps, Call("signedPoissonScale", mp, mm, zp, zm)))));
        Formula cs = Mul(Call("exp", N(2)), Add(Call("sqrt", Mul(N(2), V("pi"))), N(1)));
        Formula result = Le(AbsF(SubF(DivF(Call("P", w, cp, cm, V("np"), V("nm")), Call("Q", mp, mm, V("np"), V("nm"))), N(1))),
            Mul(Mul(Mul(eps, Pow(cs, N(4))), Pow(Add(c, N(1)), N(2))), Pow(l, V("k"))));
        return Q("Omega", V("Type"), Seq(OpenBracket, Call("Fintype", V("Omega")), CloseBracket, Sp,
            Q("k", V("Nat"), Q("kappa Czero L epsilon", V("Real"),
            Q("w", Fn(V("Omega"), V("Real")),
            Q("cp cm", Fn(V("Omega"), Fn(FinF(V("k")), V("Nat"))),
            Q("muplus muminus", Fn(FinF(V("k")), V("Real")),
            Q("np nm", Fn(FinF(V("k")), V("Nat")),
            Imp(AndF(LtF(N(0), kap), Le(N(1), c), Le(N(1), l), Le(N(0), eps), SmallK,
                Call("positiveMeanLowerBounds", kap, l, mp, mm), Call("coordinateCountBound", V("np"), V("nm"), c, l), envelope), result)))))))));
    }

    private static Formula TFPow(Formula x, Formula j) => Seq(Grp(x), Caret, Grp(j));
    private static Formula TFCall(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula TFTiltFormula(bool antisymmetric)
    {
        Formula j = V("j"), zp = V("zp"), zm = V("zm");
        Formula value = DivF(Seq(Call("eval", zp, j), antisymmetric ? Minus : Plus, Call("eval", zm, j)), N(2));
        return Disp(Q("k", V("Nat"), Q("zp zm", Tilts, Q("j", FinF(V("k")),
            Seq(Call(antisymmetric ? "tiltV" : "tiltU", zp, zm, j), Eq,
                antisymmetric ? value : SubF(value, N(1)))))));
    }
    private static Formula TFDriftFormula(bool parity)
    {
        Formula j = V("j"), r = V("r"), support = V("S"), mark = V("m"), zp = V("zp"), zm = V("zm");
        Formula profile = Call("b", r, support, Call("inl", Call("eval", mark, j)));
        Formula summand = Add(Call(parity ? "tiltV" : "tiltU", zp, zm, j),
            Mul(profile, Call(parity ? "tiltU" : "tiltV", zp, zm, j)));
        Formula sum = Seq(Sum, Underscore, Grp(j, Colon, FinF(V("k"))), Sp, Open, summand, Close);
        Formula body = Seq(Call(parity ? "driftB" : "driftA", r, support, mark, zp, zm), Eq,
            DivF(sum, Mul(N(2), V("M"))));
        return Disp(Q("M q k", V("Nat"), Q("r", V("Real"), Q("S", Call("Support", V("M"), V("q")),
            Q("m", Fn(FinF(V("k")), FinF(V("M"))), Q("zp zm", Tilts, body))))));
    }
    private static Formula TFPgfFormula()
    {
        Formula j = V("j"), o = V("o"), t = V("T"), r = V("r"), support = V("S"), mark = V("m"), zp = V("zp"), zm = V("zm");
        Formula path = Call("path");
        Formula row = Call("eval", mark, j);
        Formula powers = Mul(Pow(Call("eval", zp, j), Call("count", path, o, row, N(1))),
            Pow(Call("eval", zm, j), Call("count", path, o, row, Seq(Minus, N(1)))));
        Formula product = Seq(Prod, Underscore, Grp(j, Colon, FinF(V("k"))), Sp, powers);
        Formula sum = Seq(Sum, Underscore, Grp(o, Colon, Call("Obs", V("M"), t, path)), Sp,
            Mul(Call("probability", r, path, support, o), product));
        Formula body = Seq(Call("actualPGF", r, support, mark, zp, zm, t), Eq, sum);
        return Disp(Q("M q k T", V("Nat"), Q("r", V("Real"), Q("S", Call("Support", V("M"), V("q")),
            Q("m", Fn(FinF(V("k")), FinF(V("M"))), Q("zp zm", Tilts, body))))));
    }
    private static Formula TFForwardMatrixFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B");
        return Disp(Seq(Forall, Sp, a, Comma, b, Colon, F.Id("Complex"), Comma, Sp,
            TFCall("forwardMatrix", a, b), Eq, TFCall("matrix", Seq(D(1), Plus, a), b, a, b)));
    }
    private static Formula TFForwardStateFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), t = F.Id("t");
        return Disp(Seq(Forall, Sp, a, Comma, b, Colon, F.Id("Complex"), Comma, Sp,
            TFCall("forwardState", a, b, D(0)), Eq, TFCall("vector", D(1), D(0)), Sp, Land, Sp,
            Forall, Sp, t, Colon, F.Id("Nat"), Comma, Sp,
            TFCall("forwardState", a, b, Seq(t, Plus, D(1))), Eq,
            TFCall("rowTransfer", TFCall("forwardState", a, b, t), TFCall("forwardMatrix", a, b))));
    }
    private static Formula TFForwardTransferFormula()
    {
        Formula m = F.Id("M"), q = F.Id("q"), t = F.Id("T"), k = F.Id("k"), r = F.Id("r");
        Formula s = F.Id("S"), mark = F.Id("m"), zp = F.Id("zp"), zm = F.Id("zm");
        Formula a = TFCall("driftA", r, s, mark, zp, zm), b = TFCall("driftB", r, s, mark, zp, zm);
        Formula pgf = TFCall("actualPGF", r, s, mark, zp, zm, t);
        return Disp(Seq(Forall, Sp, m, Comma, q, Comma, t, Comma, k, Colon, F.Id("Nat"), Comma, Sp,
            Forall, Sp, r, Colon, F.Id("Real"), Comma, Sp,
            D(1), Leq, Sp, q, Lt, m, Sp, Land, Sp, D(0), Lt, r, Lt, D(1), Sp, Land, Sp,
            TFCall("compensation", m, q, r), Lt, D(1), Sp, Rightarrow, Sp,
            Forall, Sp, s, Colon, TFCall("Support", m, q), Comma, Sp,
            Forall, Sp, mark, Colon, TFCall("Fin", k), To, Sp, TFCall("Fin", m), Comma, Sp,
            TFCall("injective", mark), Sp, Rightarrow, Sp,
            Forall, Sp, zp, Comma, zm, Colon, TFCall("Fin", k), To, Sp, F.Id("Complex"), Comma, Sp,
            pgf, Eq, TFCall("first", TFCall("forwardState", a, b, t)), Sp, Land, Sp,
            pgf, Eq, TFCall("entry", TFPow(TFCall("forwardMatrix", a, b), t), D(0), D(0))));
    }

    private static Formula TFHV(string s) => F.Id(s);
    private static Formula TFHN(byte n) => D(n);
    private static Formula TFHCall(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula TFHQ(string names, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { TFHV(s) } : new[] { Comma, TFHV(s) })]), Colon, type, Comma, Sp, body);
    private static Formula TFHFn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula TFHEqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula TFHLe(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula TFHLtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula TFHAdd(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula TFHSubF(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula TFHMul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula TFHDivF(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula TFHAndF(params Formula[] xs) => TFHJoin(xs, Land);
    private static Formula TFHJoin(Formula[] xs, Formula op)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, op, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula TFHImp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula TFHNorm(Formula a) => TFHCall("norm", a);
    private static Formula TFHFinF(Formula a) => TFHCall("Fin", a);
    private static Formula TFHSupportF => TFHCall("Support", TFHV("M"), TFHV("q"));
    private static Formula TFHMarks => TFHFn(TFHFinF(TFHV("k")), TFHFinF(TFHV("M")));
    private static Formula TFHTilts => TFHFn(TFHFinF(TFHV("k")), TFHV("Complex"));
    private static Formula TFHSmallK => Seq(Open, TFHV("k"), Eq, TFHN(1), Sp, Lor, Sp, TFHV("k"), Eq, TFHN(2), Close);
    private static Formula TFHEndpointDef() => TFHQ("X", TFHV("Type"), Seq(OpenBracket, TFHCall("Fintype", TFHV("X")), CloseBracket, Sp,
        TFHQ("c", TFHV("Complex"), TFHQ("K", TFHFn(TFHV("X"), TFHFn(TFHV("X"), TFHV("Complex"))), TFHQ("n", TFHV("Nat"), TFHQ("y", TFHV("X"),
            TFHEqn(TFHCall("endpointWeight", TFHV("c"), TFHV("K"), TFHV("n"), TFHV("y")), TFHCall("endingHistorySum", TFHV("c"), TFHV("K"), TFHV("n"), TFHV("y")))))))));
    private static Formula TFHEndpoint(string name)
    {
        Formula value = name == "endpoint_zero" ? TFHEqn(TFHCall("endpointWeight", TFHV("c"), TFHV("K"), TFHN(0), TFHV("y")), TFHV("c")) :
            name == "endpoint_next" ? TFHEqn(TFHCall("endpointWeight", TFHV("c"), TFHV("K"), TFHAdd(TFHV("n"), TFHN(1)), TFHV("y")), TFHCall("endpointConvolution", TFHV("c"), TFHV("K"), TFHV("n"), TFHV("y"))) :
            TFHEqn(TFHCall("endpointSum", TFHV("c"), TFHV("K"), TFHV("n")), TFHCall("historySum", TFHV("c"), TFHV("K"), TFHV("n")));
        if (name != "endpoint_total") value = TFHQ("y", TFHV("X"), value);
        if (name != "endpoint_zero") value = TFHQ("n", TFHV("Nat"), value);
        return TFHQ("X", TFHV("Type"), Seq(OpenBracket, TFHCall("Fintype", TFHV("X")), CloseBracket, Sp,
            TFHQ("c", TFHV("Complex"), TFHQ("K", TFHFn(TFHV("X"), TFHFn(TFHV("X"), TFHV("Complex"))), value))));
    }
    private static Formula TFHProfile(Formula body, string naturals) => TFHQ(naturals, TFHV("Nat"), TFHQ("r", TFHV("Real"), TFHQ("S", TFHSupportF, body)));


}
