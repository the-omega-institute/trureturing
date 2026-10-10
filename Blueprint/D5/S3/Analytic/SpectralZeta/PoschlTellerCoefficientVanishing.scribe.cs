using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SpectralZeta;

internal sealed class PoschlTellerCoefficientVanishingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/fucci2024poschlteller");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection of the generalized Bernoulli coefficient polynomials forces g(2,3,beta,3,1) to vanish. The admissible choice beta = pi/4 therefore refutes the nonvanishing conjecture in Fucci and Stanfill's Remark B.3.",
        H("Reflection cancels a Pöschl–Teller logarithmic coefficient"),
        Blocks(
            Node("bernoulliPower", "The real binomial power of the Bernoulli series", BernoulliPower(),
                "DLMF 24.16.1 specifies the generalized Bernoulli generating function. Its real power is the binomial series in bernoulliPowerSeries(R) minus one. descPochhammer(R,k) is the descending Pochhammer polynomial, eval is polynomial evaluation, and Nat.factorial is the factorial. The coefficient of degree n needs only k <= n, since the subtracted series has zero constant coefficient."),
            Node("generalizedBernoulliSeries", "The generalized Bernoulli generating function", GeneralizedSeries(),
                "Multiplication by the rescaled exponential inserts the factor exp(x t). PowerSeries.rescale multiplies the coefficient of degree n by x^n."),
            Node("generalizedBernoulli", "Generalized Bernoulli polynomials", GeneralizedBernoulli(),
                "The generating function uses exponential coefficients: multiplying the nth ordinary power-series coefficient by n! yields B_n^(a)(x)."),
            Node("C", "The Bernoulli correction C", Correction(),
                "Appendix B's definition of C_m is the finite sum over j = 0,...,m-1. Nat.choose is the natural binomial coefficient and bernoulli is Mathlib's rational Bernoulli number. Complex.ofReal, Nat.cast and Rat.cast display the real, natural and rational embeddings into C. Natural subtraction is truncated; in this sum m-j is positive. All displayed fractions are field division, with Lean's totalized value zero at a zero denominator."),
            Node("E", "The coefficient E", EFormula(),
                "Equation (B.17) defines E_k. Natural exponents are used literally; the source uses this expression for k >= 1."),
            Node("G", "The generalized Bernoulli coefficient G", GFormula(),
                "Appendix B defines G_k(x,y) as the real binomial coefficient times B_k^(x-y+1)(x), embedded into C. The real binomial coefficient is the evaluation of descPochhammer divided by k!."),
            Node("scriptE", "The logarithmic denominator indeterminate", ScriptE(),
                "The indeterminate Polynomial.X represents T = sin(alpha)/[-cos(alpha)+sin(alpha)(gamma_E+ln(z^(1/2))-ln 2-i pi/2)]. Thus scriptE(0,y) = 1 and scriptE(j,y) = Polynomial.C(E(j,y)/2) times Polynomial.X for j >= 1. Polynomial.C embeds a complex scalar as a constant polynomial; ite is conditional choice."),
            Node("P", "The coefficient polynomial P", PFormula(),
                "The source defines P_0 = 1 and the displayed finite sum for positive k. The numeral 4 in this formula is a constant polynomial over C. These general definitions, rather than the special displayed P_1, determine every coefficient."),
            Node("Omega0", "The constant factor Omega0", OmegaZero(),
                "Equation (B.26) gives the gamma-function factor. Real.rpow is real exponentiation, Real.cot is cotangent, and Complex.Gamma, Complex.exp and Complex.I retain their Mathlib names. The source range is 0 < nu < 1 and 0 < beta < pi with beta different from pi/2."),
            Node("Pbar", "The scaled polynomial Pbar", PBar(),
                "Equation (B.24) multiplies P_k((1+nu)/2) by Omega0(nu,beta)."),
            Node("Omega", "The recursive polynomials Omega", OmegaFormula(),
                "Equation (B.26) starts at the constant polynomial Omega0 and recursively subtracts the earlier Omega_l times P_(k+1-l)((1-nu)/2). The sum over Fin(k+1) includes l = 0,...,k, and val is the natural value of a Fin index. Natural subtraction is truncated, with k+1-l positive on that finite domain."),
            Node("sparseSeries", "A sparse formal series", SparseSeries(),
                "PowerSeries.mk constructs the series from its coefficients. dite is dependent conditional choice: Exists.choose selects an index when one exists. For q > 0 that index is unique. This total construction also has a value outside that range, which the conjecture does not use.", false),
            Node("W", "The series inside the logarithm", WFormula(),
                "Set x = z^(-1/q). A term Omega_k x^(p+kq) occupies exactly the degree p+kq. The rational nu is encoded by real field division after the natural-to-real casts; this is not natural division."),
            Node("logOnePlus", "The formal logarithm", LogFormula(),
                "The formal log(1+w) is the alternating sum of w^n/n. At positive order of w, degree d receives only n <= d. Finset.Icc(1,d) is the inclusive natural interval. The scalar acts on the coefficient polynomial by complex scalar multiplication."),
            Node("S", "The order m coefficient polynomial", SFormula(),
                "The source's logarithmic expansion defines S_m as the coefficient of x^(m+p). PowerSeries.coeff extracts that coefficient."),
            Node("g", "The logarithmic denominator coefficient", GSmall(),
                "The source's final expansion, manuscript label (B.45) and typeset equation (B.48), expands S_m in T. Polynomial.coeff(j,S) is its coefficient of T^j, namely g_(m,j)(p/q,beta)."),
            Node("admissible", "Admissible expansion indices", Admissible(),
                "The source's set [m]_(p,q) is nonempty exactly when there are natural l,k with l p + k q = m. Naturals include zero."),
            Node("order", "The largest denominator degree", OrderFormula(),
                "In the positive p,q range the displayed natural set is bounded, so sSup gives that maximum for admissible m.", quote: OrderQuote()),
            Node("claim", "The nonvanishing conjecture", ClaimFormula(),
                "The formula encodes p,q as naturals with 0 < p < q and Nat.Coprime(p,q), beta in the open interval (0,pi) excluding pi/2, and the nonempty index set with j <= order(p,q,m). This includes m = q, j = 1 also in the source's sum restricted to positive denominator degree.", quote: ClaimQuote()),
            Node("result", "Refutation by reflection", new Formula.Not(Call("claim")),
                "Take (p,q,beta,m,j) = (2,3,pi/4,3,1). The index is admissible and 1 <= order(2,3,3). In degree 5 of the formal logarithm, the linear term is Omega_1; the square and all higher powers contribute zero. Since G_0 = 1, the coefficient of T in P_1(y) is E_1(y)/2. The identity E_1(1-y) = E_1(y) exchanges (1+nu)/2 and (1-nu)/2, so this coefficient cancels in Omega_1. Consequently g(2,3,beta,3,1) = 0 for every real beta, including pi/4. The result concerns formal coefficients; it does not assert a theorem about spectral analytic continuation or the all-coprime-parameter family.", false, DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature = true, DescribeRole role = DescribeRole.Definition, DocumentBlock? quote = null) => Describe.Lean(
        DescribeId.Create("poschl-teller-" + (name == "G" ? "generalized-g" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        quote is null ? Blocks(Paragraph(Text(prose))) : Blocks(quote, Paragraph(Text(prose))), role);

    private static DocumentBlock ClaimQuote() => Paragraph(
        Text("Remark B.3, printed page 31: “From calculations performed for particular choices of "),
        Math(V("p")), Text(", "), Math(V("q")), Text(", and "), Math(Beta),
        Text(", we in fact conjecture that all of the "),
        Math(Seq(new Formula.Subscript(V("g"), Seq(V("m"), Comma, V("j"))),
            Parenthesized(Seq(V("p"), Slash, V("q"), Comma, Beta)))),
        Text(" are nonzero for the choices of "), Math(Seq(V("p"), Comma, Sp, V("q"))),
        Text(", and "), Math(Beta), Text(" considered here.”"));

    private static DocumentBlock OrderQuote()
    {
        Formula i = V("i"), ki = new Formula.Subscript(V("k"), i), li = new Formula.Subscript(V("l"), i);
        Formula sm = Seq(new Formula.Subscript(Seq(Mathcal, Grp(V("S"))), V("m")),
            Parenthesized(Seq(V("p"), Slash, V("q"), Comma, V("z"))));
        return Paragraph(Text("Printed page 31: “The order of "), Math(sm),
            Text(" is, then, "), Math(Eqn(new Formula.Subscript(V("k"), V("m")),
                Seq(Max, OpenBrace, ki, CloseBrace))), Text(" with "),
            Math(new Formula.Relation(i, FormulaRelationOperator.MemberOf, N)),
            Text(", namely the largest value of "), Math(ki), Text(" amongst the vectors "),
            Math(new Formula.Relation(Parenthesized(Seq(li, Comma, ki)), FormulaRelationOperator.MemberOf,
                new Formula.Subscript(Seq(OpenBracket, V("m"), CloseBracket), Seq(V("p"), Comma, V("q"))))), Text(".”"));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cplx => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(word));
        }
        var op = Seq(Operatorname, Grp([.. parts]));
        return args.Length == 0 ? op : new Formula.Apply(op, [.. args]);
    }
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula NatCast(Formula a, Formula type) => Cast(Call("Nat.cast", a), type);
    private static Formula RealCast(Formula a) => Call("Complex.ofReal", a);
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula Poly => Call("Polynomial", Cplx);
    private static Formula Series(Formula type) => Call("PowerSeries", type);
    private static Formula ChooseReal(Formula a, Formula k) =>
        Div(Call("Polynomial.eval", a, Call("descPochhammer", R, k)), NatCast(Call("Nat.factorial", k), R));

    private static Formula BernoulliPower()
    {
        Formula a = V("a"), n = V("n"), k = V("k");
        return All("a", R, Eqn(Call("bernoulliPower", a), Call("PowerSeries.mk",
            Fn("n", N, SumIn("k", Call("Finset.range", Add(n, D(1))),
                Mul(ChooseReal(a, k), Call("PowerSeries.coeff", n,
                    Pow(Sub(Call("bernoulliPowerSeries", R), D(1)), k))))))));
    }
    private static Formula GeneralizedSeries() => All("a", R, All("x", R,
        Eqn(Call("generalizedBernoulliSeries", V("a"), V("x")),
            Mul(Call("bernoulliPower", V("a")), Call("PowerSeries.rescale", V("x"), Call("PowerSeries.exp", R))))));
    private static Formula GeneralizedBernoulli() => All("n", N, All("a", R, All("x", R,
        Eqn(Call("generalizedBernoulli", V("n"), V("a"), V("x")),
            Mul(NatCast(Call("Nat.factorial", V("n")), R),
                Call("PowerSeries.coeff", V("n"), Call("generalizedBernoulliSeries", V("a"), V("x"))))))));
    private static Formula Correction()
    {
        Formula m = V("m"), y = V("y"), j = V("j"), twoJ = Mul(D(2), j), gap = Sub(m, j);
        return All("m", N, All("y", R, Eqn(Call("C", m, y), SumIn("j", Call("Finset.range", m),
            Mul(Mul(NatCast(Call("Nat.choose", Sub(Mul(D(2), m), D(1)), twoJ), Cplx),
                Div(Mul(Pow(D(2), Mul(D(2), m)), Pow(RealCast(y), twoJ)), NatCast(gap, Cplx))),
                Cast(Call("Rat.cast", Call("bernoulli", Mul(D(2), gap))), Cplx))))));
    }
    private static Formula EFormula()
    {
        Formula k = V("k"), y = V("y"), twoY = Mul(D(2), RealCast(y)), twoK = Mul(D(2), k);
        return All("k", N, All("y", R, Eqn(Call("E", k, y),
            Sub(Sub(Mul(D(2), Pow(twoY, Sub(twoK, D(1)))), Div(Pow(twoY, twoK), NatCast(k, Cplx))), Call("C", k, y)))));
    }
    private static Formula GFormula() => All("k", N, All("x", R, All("y", R,
        Eqn(Call("G", V("k"), V("x"), V("y")), RealCast(Mul(ChooseReal(Sub(V("x"), V("y")), V("k")),
            Call("generalizedBernoulli", V("k"), Add(Sub(V("x"), V("y")), D(1)), V("x"))))))));
    private static Formula ScriptE() => All("j", N, All("y", R,
        Eqn(Call("scriptE", V("j"), V("y")), Call("ite", Eqn(V("j"), D(0)), D(1),
            Mul(Call("Polynomial.C", Div(Call("E", V("j"), V("y")), D(2))), Call("Polynomial.X"))))));
    private static Formula PFormula()
    {
        Formula k = V("k"), y = V("y"), j = V("j"), gap = Sub(k, j);
        return All("k", N, All("y", R, Eqn(Call("P", k, y), Call("ite", Eqn(k, D(0)), D(1),
            SumIn("j", Call("Finset.range", Add(k, D(1))), Mul(Mul(Pow(D(4), gap), Call("scriptE", j, y)),
                Call("Polynomial.C", Call("G", Mul(D(2), gap), Sub(D(1), y), y))))))));
    }
    private static Formula OmegaZero()
    {
        Formula nu = V("nu"), beta = V("beta");
        return All("nu", R, All("beta", R, Eqn(Call("Omega0", nu, beta),
            Mul(Mul(Div(Mul(RealCast(Call("Real.rpow", D(2), Sub(Mul(D(2), nu), D(1)))),
                Call("Complex.Gamma", Add(D(1), RealCast(nu)))),
                Call("Complex.Gamma", new Formula.Negate(RealCast(nu)))), RealCast(Call("Real.cot", beta))),
                Call("Complex.exp", Mul(Mul(Call("Complex.I"), RealCast(Call("Real.pi"))), RealCast(nu)))))));
    }
    private static Formula PBar() => All("nu", R, All("beta", R, All("k", N,
        Eqn(Call("Pbar", V("nu"), V("beta"), V("k")),
            Mul(Call("Polynomial.C", Call("Omega0", V("nu"), V("beta"))),
                Call("P", V("k"), Div(Add(D(1), V("nu")), D(2))))))));
    private static Formula OmegaFormula()
    {
        Formula nu = V("nu"), beta = V("beta"), k = V("k"), l = V("l"), next = Add(k, D(1));
        Formula zero = All("nu", R, All("beta", R, Eqn(Call("Omega", nu, beta, D(0)), Call("Polynomial.C", Call("Omega0", nu, beta)))));
        Formula sum = Seq(Sum, Underscore, Grp(l, Colon, Call("Fin", next)), Sp, Parenthesized(
            Mul(Call("P", Sub(next, Call("val", l)), Div(Sub(D(1), nu), D(2))), Call("Omega", nu, beta, Call("val", l)))));
        Formula succ = All("nu", R, All("beta", R, All("k", N,
            Eqn(Call("Omega", nu, beta, next), Sub(Call("Pbar", nu, beta, next), sum)))));
        return new Formula.Aligned([zero, succ]);
    }
    private static Formula SparseSeries()
    {
        Formula p = V("p"), q = V("q"), a = V("A"), d = V("d"), r = V("R");
        Formula condition = Some("k", N, Eqn(d, Add(p, Mul(V("k"), q))));
        Formula body = Call("dite", Parenthesized(condition), Fn("h", Parenthesized(condition), App(a, Call("Exists.choose", V("h")))),
            Seq(Call("fun"), Sp, Underscore, Sp, Mapsto, Sp, D(0)));
        return All("R", Call("Type"), Seq(OpenBracket, Call("Semiring", r), CloseBracket, Sp,
            All("p", N, All("q", N, All("A", new Formula.TypeArrow(N, r),
                Eqn(Call("sparseSeries", p, q, a), Call("PowerSeries.mk", Fn("d", N, body))))))));
    }
    private static Formula WFormula() => All("p", N, All("q", N, All("beta", R,
        Eqn(Call("W", V("p"), V("q"), V("beta")), Call("sparseSeries", V("p"), V("q"),
            Call("Omega", Div(NatCast(V("p"), R), NatCast(V("q"), R)), V("beta")))))));
    private static Formula LogFormula()
    {
        Formula w = V("w"), d = V("d"), n = V("n");
        Formula term = Seq(Div(Pow(new Formula.Negate(D(1)), Add(n, D(1))), NatCast(n, Cplx)), Sp,
            Cdot, Sp, Call("PowerSeries.coeff", d, Pow(w, n)));
        return All("w", Series(Poly), Eqn(Call("logOnePlus", w), Call("PowerSeries.mk",
            Fn("d", N, SumIn("n", Call("Finset.Icc", D(1), d), term)))));
    }
    private static Formula SFormula() => All("p", N, All("q", N, All("beta", R, All("m", N,
        Eqn(Call("S", V("p"), V("q"), V("beta"), V("m")),
            Call("PowerSeries.coeff", Add(V("m"), V("p")), Call("logOnePlus", Call("W", V("p"), V("q"), V("beta")))))))));
    private static Formula GSmall() => All("p", N, All("q", N, All("beta", R, All("m", N, All("j", N,
        Eqn(Call("g", V("p"), V("q"), V("beta"), V("m"), V("j")),
            Call("Polynomial.coeff", V("j"), Call("S", V("p"), V("q"), V("beta"), V("m")))))))));
    private static Formula IndexEquation() => Eqn(Add(Mul(V("l"), V("p")), Mul(V("k"), V("q"))), V("m"));
    private static Formula Admissible() => All("p", N, All("q", N, All("m", N,
        IffTo(Call("admissible", V("p"), V("q"), V("m")), Some("l", N, Some("k", N, IndexEquation()))))));
    private static Formula OrderFormula() => All("p", N, All("q", N, All("m", N,
        Eqn(Call("order", V("p"), V("q"), V("m")), Call("sSup",
            Seq(OpenBrace, V("k"), Colon, Sp, N, Sp, Mid, Sp,
                Some("l", N, IndexEquation()), CloseBrace))))));
    private static Formula ClaimFormula()
    {
        Formula p = V("p"), q = V("q"), beta = V("beta"), m = V("m"), j = V("j");
        Formula conclusion = new Formula.Relation(Call("g", p, q, beta, m, j), FormulaRelationOperator.NotEqual, D(0));
        Formula indices = All("m", N, All("j", N, Imp(Call("admissible", p, q, m),
            Imp(LeqTo(j, Call("order", p, q, m)), conclusion))));
        Formula betas = All("beta", R, Imp(new Formula.Relation(beta, FormulaRelationOperator.MemberOf,
            Call("Set.Ioo", D(0), Call("Real.pi"))), Imp(new Formula.Relation(beta, FormulaRelationOperator.NotEqual,
                Div(Call("Real.pi"), D(2))), indices)));
        return IffTo(Call("claim"), All("p", N, All("q", N, Imp(Less(D(0), p), Imp(Less(p, q),
            Imp(Call("Nat.Coprime", p, q), betas))))));
    }
}
