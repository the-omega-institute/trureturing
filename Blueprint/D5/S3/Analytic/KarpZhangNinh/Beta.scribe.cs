using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangNinh;

internal sealed class BetaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangNinh/Beta.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta lifting preserves symmetric balancing for arbitrary real coefficients.",
        H("Trisection balancing and symmetric homogeneous beta lifting"), Blocks([
            Paragraph(Text("The degree N and coefficient function c are arbitrary. No coefficient sign assumption is imposed. The homogeneous polynomial is evaluated on a line of fixed coordinate sum, and its lift replaces the powers by rising factorials.")),
            Entry("polynomial", "Homogeneous monomial expansion", DescribeRole.Definition,
                BindCoefficients(All("x", Rl(), All("y", Rl(), Eq(Poly(V("x"), V("y")),
                    Sum("k", Range(), Mul(Mul(Call("c", V("k")), Pow(V("x"), V("k"))),
                        Pow(V("y"), Sub(V("N"), V("k"))))))))),
                "The polynomial is the finite sum of c(k)x^k y^(N-k), including both endpoints."),
            Entry("lift", "Rising factorial lift", DescribeRole.Definition,
                BindCoefficients(All("u", Rl(), All("v", Rl(), Eq(Lift(V("u"), V("v")),
                    Sum("k", Range(), Mul(Mul(Call("c", V("k")), Poch(V("k"), V("u"))),
                        Poch(Sub(V("N"), V("k")), V("v")))))))),
                "The same coefficient array multiplies the two complementary rising factorials."),
            Entry("polynomial_continuous", "Continuity of the homogeneous slice", DescribeRole.Theorem,
                BindCoefficients(Call("Continuous", Slice())),
                "Every homogeneous slice is continuous because it is a finite sum of products of integer powers."),
            Entry("lift_continuous", "Continuity of the lifted slice", DescribeRole.Theorem,
                BindCoefficients(All("S", Rl(), Call("Continuous", LiftSlice()))),
                "The lifted slice is a polynomial in its real parameter, so it is continuous on the full real line."),
            Entry("polynomial_symm", "Symmetry of the homogeneous expansion", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), All("x", Rl(), All("y", Rl(),
                    Eq(Poly(V("x"), V("y")), Poly(V("y"), V("x"))))))),
                "Reflection of the finite index k to N-k proves coordinate symmetry when the coefficients are symmetric."),
            Entry("lift_symm", "Symmetry of the rising factorial expansion", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), All("u", Rl(), All("v", Rl(),
                    Eq(Lift(V("u"), V("v")), Lift(V("v"), V("u"))))))),
                "The same reflected finite sum proves symmetry of the lifted polynomial."),
            Entry("lift_eq_betaMean", "Normalized beta moment identity", DescribeRole.Theorem,
                BindCoefficients(All("m", Rl(), All("d", Rl(),
                    Imp(Lt(D(0), Add(V("m"), V("d"))), Imp(Lt(D(0), Sub(V("m"), V("d"))),
                        Eq(Lift(Add(V("m"), V("d")), Sub(V("m"), V("d"))),
                            Mul(Poch(V("N"), Mul(D(2), V("m"))),
                                BetaMean(Slice(), V("m"), V("d"))))))))),
                "Integrating each monomial against the beta density gives its Gamma quotient. KummerRatio.BetaIntegral.gamma_pochhammer converts the shifted Gamma factors to rising factorials. The remaining normalizer depends only on the total shape parameter."),
            Entry("betaMean_antiOn", "Weak comparison for arbitrary monotone integrands", DescribeRole.Theorem,
                All("W", Arrow(Rl(), Rl()), Imp(Call("ContinuousOn", V("W"), Interval("Icc", D(0), D(1))),
                    Imp(All("t", Rl(), Imp(Member(V("t"), Interval("Icc", D(0), D(1))),
                        Eq(Call("W", Sub(D(1), V("t"))), Call("W", V("t"))))),
                        Imp(Call("MonotoneOn", V("W"), HalfInterval()),
                            All("m", Rl(), Imp(Lt(D(0), V("m")),
                                Call("AntitoneOn", Lambda("d", BetaMean(V("W"), V("m"), V("d"))),
                                    Interval("Ico", D(0), V("m"))))))))),
                "Adding a positive multiple of t(1-t) makes the integrand strictly increasing toward the midpoint while preserving its symmetry. IncompleteBeta.Comparison.betaMean_strictAntiOn compares the perturbed means. Linearity of the integral and the limit as the perturbation decreases to zero yield the weak comparison."),
            Entry("lift_monotoneOn", "Beta lifting preserves balancing", DescribeRole.Theorem,
                BindCoefficients(Imp(CoefficientSymmetry(), Imp(Call("MonotoneOn", Slice(), HalfInterval()),
                    All("S", Rl(), Imp(Le(D(0), V("S")),
                        Call("MonotoneOn", LiftSlice(), Interval("Icc", D(0), Frac(V("S"), D(2))))))))),
                "For positive shapes, the beta moment identity and comparison of symmetric beta means show that the lift is nondecreasing as the coordinates approach equality. Continuity extends the inequality to shape zero. A zero total has only the point zero. This preservation theorem has no positivity hypothesis on c."),
            .. HomogeneousSection.Content()])));

    private static DocumentBlock Entry(string declaration, string title, DescribeRole role, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("karp-zhang-ninh-beta-" + declaration.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Rl() => Seq(Mathbb, Grp(V("R")));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, Rl())), Sp, Mapsto, Sp, body));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Interval(string kind, Formula a, Formula b) => App(Q("Set", kind), a, b);
    private static Formula HalfInterval() => Interval("Ioc", D(0), Frac(D(1), D(2)));
    private static Formula Range() => App(Q("Finset", "range"), Add(V("N"), D(1)));
    private static Formula Poly(Formula x, Formula y) => Call("polynomial", V("c"), V("N"), x, y);
    private static Formula Lift(Formula u, Formula v) => Call("lift", V("c"), V("N"), u, v);
    private static Formula Poch(Formula n, Formula u) => App(Q("Polynomial", "eval"), u, Call("ascPochhammer", Rl(), n));
    private static Formula Slice() => Lambda("t", Poly(V("t"), Sub(D(1), V("t"))));
    private static Formula LiftSlice() => Lambda("s", Lift(V("s"), Sub(V("S"), V("s"))));
    private static Formula BetaMean(Formula w, Formula m, Formula d) => Call("betaMean", w, m, d);
    private static Formula CoefficientSymmetry() => All("k", N(), Imp(Le(V("k"), V("N")), Eq(Call("c", Sub(V("N"), V("k"))), Call("c", V("k")))));
    private static Formula BindCoefficients(Formula body) => All("c", Arrow(N(), Rl()), All("N", N(), body));
    private static Formula Sum(string name, Formula domain, Formula body) => Seq(F.Sum, Underscore, Grp(Seq(V(name), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
}

internal static class HomogeneousSection
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangNinh/Beta.";

    public static DocumentBlock[] Content() =>
        [
            Paragraph(Text("Degree variables and summation indices are natural numbers. Subtraction in indices and exponents is natural truncated subtraction. Scalar subtraction in the moment formulas takes place in the integers or reals, as specified below. The functions alpha and beta are integer-valued, and their six cases are ordered by n modulo six. No root-of-unity choice is required: Pascal's recurrence proves the six-periodic filter formula.")),
            Def("residue", "Binomial residue sums",
                Ns(["n", "r"], Eq(C("residue", V("n"), V("r")),
                    Sum("k", Range(Add(V("n"), D(1))),
                        Mul(Choose(V("n"), V("k")), Indicator(Eq(Mod(V("k"), D(3)), V("r"))))))),
                "The integer sum counts binomial coefficients in a prescribed residue class modulo three."),
            Def("periodic", "The six-periodic correction",
                Ns(["q"], Eq(C("periodic", V("q")),
                    Cases(V("q"), [D(2), D(1), Neg(D(1)), Neg(D(2)), Neg(D(1)), D(1)]))),
                "The six values are 2, 1, -1, -2, -1, 1. This is the real correction normally obtained by a cubic root-of-unity filter."),
            Thm("residue_filter", "The exact trisection filter",
                Ns(["n"], And(Eq(Mul(D(3), C("residue", V("n"), D(0))),
                        Add(Pow(D(2), V("n")), C("periodic", V("n")))),
                    And(Eq(Mul(D(3), C("residue", V("n"), D(1))),
                            Add(Pow(D(2), V("n")), C("periodic", Add(V("n"), D(4))))),
                        Eq(Mul(D(3), C("residue", V("n"), D(2))),
                            Add(Pow(D(2), V("n")), C("periodic", Add(V("n"), D(2)))))))),
                "Pascal's recurrence couples the three residue sums. Induction and the six possible residues of n determine all three correction terms simultaneously."),
            Def("weighted", "The first marked moment",
                Ns(["n", "r"], Eq(C("weighted", V("n"), V("r")),
                    Sum("k", Range(Add(V("n"), D(1))),
                        Mul(Mul(Choose(V("n"), V("k")), V("k")),
                            Indicator(Eq(Mod(V("k"), D(3)), V("r"))))))),
                "Multiplying by k marks one selected element of a binomial subset."),
            Def("second", "The second marked moment",
                Ns(["n", "r"], Eq(C("second", V("n"), V("r")),
                    Sum("k", Range(Add(V("n"), D(1))),
                        Mul(Mul(Mul(Choose(V("n"), V("k")), V("k")), Sub(V("k"), D(1))),
                            Indicator(Eq(Mod(V("k"), D(3)), V("r"))))))),
                "The factor k(k-1) marks an ordered pair of distinct selected elements. This subtraction takes place in the integers."),
            Def("A", "The first-moment difference",
                Ns(["n"], Eq(C("A", V("n")),
                    Sub(C("weighted", V("n"), D(0)),
                        Mul(D(2), C("weighted", Sub(V("n"), D(1)), D(0)))))),
                "A(n) is the first marked trisection sum at n minus twice its value at n-1."),
            Def("T", "The weighted difference",
                Ns(["n", "N"], Eq(C("T", V("n"), V("N")),
                    Sub(Mul(Sub(V("N"), D(1)), C("A", V("n"))),
                        Sub(C("second", V("n"), D(0)),
                            Mul(D(2), C("second", Sub(V("n"), D(1)), D(0))))))),
                "Using k(N-k)=(N-1)k-k(k-1), this is the weighted trisection difference. The factors N-1 and k-1 are integer differences."),
            Def("alpha", "The first correction table",
                Ns(["n"], Eq(C("alpha", V("n")), Cases(V("n"), [
                    Add(Neg(Mul(D(3), V("n"))), D(4)),
                    Add(Neg(Mul(D(3), V("n"))), D(2)), Neg(D(2)),
                    Sub(Mul(D(3), V("n")), D(4)), Sub(Mul(D(3), V("n")), D(2)), D(2)]))),
                "The correction alpha(n) is selected by n modulo six."),
            Def("beta", "The second correction table",
                Ns(["n"], Eq(C("beta", V("n")), Cases(V("n"), [
                    Add(Neg(Mul(D(3), V("n"))), D(4)), Neg(D(4)),
                    Sub(Mul(D(3), V("n")), D(8)), Sub(Mul(D(3), V("n")), D(4)),
                    D(4), Add(Neg(Mul(D(3), V("n"))), D(8))]))),
                "The correction beta(n) is selected by the same residue."),
            Thm("A_formula", "The first closed formula",
                Ns(["n"], Imp(Le(D(1), V("n")),
                    Eq(Mul(D(3), C("A", V("n"))),
                        Add(Pow(D(2), Sub(V("n"), D(1))), C("alpha", V("n")))))),
                "Removing one marked element reduces the first moment to a residue sum. Substitution of the filter formula gives the stated identity, including n=1 and n=2."),
            Thm("T_formula", "The weighted closed formula",
                Ns(["n", "N"], Imp(Le(D(1), V("n")),
                    Eq(Mul(D(3), C("T", V("n"), V("N"))),
                        Sub(Add(Mul(Sub(V("N"), V("n")), Pow(D(2), Sub(V("n"), D(1)))),
                                Mul(Sub(V("N"), D(1)), C("alpha", V("n")))),
                            Mul(Sub(V("n"), D(1)), C("beta", V("n"))))))),
                "Removing two marked elements handles the second moment. The displayed differences N-n, N-1 and n-1 in the scalar factors are integer differences."),
            Thm("A_nonneg", "Nonnegativity of the slope",
                Ns(["n"], Imp(Le(D(1), V("n")), Le(D(0), C("A", V("n"))))),
                "Small degrees are immediate. For n at least five, the Bernoulli estimate one_add_mul_le_pow at n-5 gives 2 to the power n-1 at least 3n-2, which dominates every negative correction."),
            Thm("T_nonneg", "Nonnegativity of every homogeneous coefficient",
                Ns(["n", "N"], Imp(Le(D(1), V("n")),
                    Imp(Eq(Mod(V("N"), D(3)), D(0)), Imp(Lt(V("n"), V("N")),
                        Le(D(0), C("T", V("n"), V("N"))))))),
                "The six residue cases reduce to the nonnegative slope and two exponential bounds against quadratics. For q=n-7, the first bound squares the Bernoulli estimate one_add_mul_le_pow at q/2, splits q into twice its natural quotient by two plus its remainder, and normalizes the two parity cases. The second bound applies the first at n-1 and normalizes the shifted quadratic."),
            Def("coeff", "Homogeneous binomial coefficients",
                Ns(["N", "k"], Eq(C("coeff", V("N"), V("k")),
                    Cond(Eq(Mod(V("k"), D(3)), D(0)),
                        Mul(Mul(V("k"), Sub(V("N"), V("k"))), Choose(V("N"), V("k"))), D(0)))),
                "Only exponents divisible by three contribute. The scalar N-k is the real difference, and the binomial coefficient is cast to the reals. The endpoint factors make the k=0 and k=N terms zero."),
            Def("P", "The homogeneous trisection polynomial",
                Ns(["N"], Rs(["x", "y"], Eq(C("P", V("N"), V("x"), V("y")),
                    Sum("k", Range(Add(V("N"), D(1))),
                        Mul(Mul(C("coeff", V("N"), V("k")), Pow(V("x"), V("k"))),
                            Pow(V("y"), Sub(V("N"), V("k")))))))),
                "Every monomial has total degree N. For N divisible by three, reflection of the exponent k exchanges x and y."),
            Thm("coeff_symm", "Symmetric coefficients",
                Ns(["N", "k"], Imp(Eq(Mod(V("N"), D(3)), D(0)), Imp(Le(V("k"), V("N")),
                    Eq(C("coeff", V("N"), Sub(V("N"), V("k"))), C("coeff", V("N"), V("k")))))),
                "The binomial reflection identity and divisibility by three give the required symmetry for Beta lifting."),
            Def("B", "Coefficients after shearing",
                Ns(["N", "t"], Eq(C("B", V("N"), V("t")),
                    Mul(Choose(V("N"), V("t")),
                        Sub(Mul(Sub(V("N"), D(1)), C("weighted", Sub(V("N"), V("t")), D(0))),
                            C("second", Sub(V("N"), V("t")), D(0)))))),
                "The expansion P(N,x,x+d) is the sum of B(N,t)x to the power N-t times d to the power t. Exchanging the two binomial choices proves this formula."),
            Def("D", "The balancing derivative",
                Ns(["N"], Rs(["x", "d"], Eq(C("D", V("N"), V("x"), V("d")),
                    Sum("t", Range(V("N")),
                        Mul(Mul(Mul(Mul(Sub(V("N"), V("t")), Choose(V("N"), V("t"))),
                                    C("T", Sub(V("N"), V("t")), V("N"))),
                                Pow(V("x"), Sub(Sub(V("N"), V("t")), D(1)))), Pow(V("d"), V("t"))))))),
                "Collecting adjacent coefficients of the differentiated shear expansion produces this finite sum."),
            Thm("hasDerivAt_slice", "Derivative along a constant-sum slice",
                Ns(["N"], Rs(["S", "x"],
                    C("HasDerivAt", Lambda("s", C("P", V("N"), V("s"), Sub(V("S"), V("s")))),
                        C("D", V("N"), V("x"), Sub(V("S"), Mul(D(2), V("x")))), V("x")))),
                "Differentiate the finite shear expansion. The derivative coefficient is n times the corresponding binomial coefficient times T(n,N)."),
            Def("K", "The divided derivative kernel",
                Ns(["N"], Rs(["x", "d"], Eq(C("K", V("N"), V("x"), V("d")),
                    Sum("n", Icc(D(1), Sub(V("N"), D(1))),
                        Mul(Mul(Mul(Mul(V("n"), Choose(V("N"), V("n"))), C("T", V("n"), V("N"))),
                                Pow(V("x"), Sub(V("n"), D(1)))),
                            Pow(V("d"), Sub(Sub(V("N"), V("n")), D(1)))))))),
                "This is the coefficient formula for the divided homogeneous balancing derivative. Its coefficients are nonnegative whenever N is divisible by three."),
            Thm("derivative_expansion", "Factorization by the imbalance",
                Ns(["N"], Imp(Eq(Mod(V("N"), D(3)), D(0)), Rs(["x", "d"],
                    Eq(C("D", V("N"), V("x"), V("d")), Mul(V("d"), C("K", V("N"), V("x"), V("d"))))))),
                "The coefficient at d=0 vanishes by symmetry. Reindexing the remaining terms gives d times K exactly."),
            Thm("strictMonoOn_slice", "Strict balancing on the positive half interval",
                Ns(["m"], Imp(Le(D(2), V("m")), C("StrictMonoOn",
                    Lambda("t", C("P", Mul(D(3), V("m")), V("t"), Sub(D(1), V("t")))),
                    App(Q("Set", "Ioc"), D(0), new Formula.Fraction(D(1), D(2)))))),
                "For x and d positive, the n=3 coefficient is strictly positive because T(3,N)=3(N-3), while every other summand is nonnegative. For 0<x<1/2, d=1-2x is positive. The mean-value theorem gives strict increase, including comparisons with the midpoint.")];

    private static DocumentBlock Def(string name, string title, Formula formula, string text) =>
        Entry(name, title, DescribeRole.Definition, formula, text);
    private static DocumentBlock Thm(string name, string title, Formula formula, string text) =>
        Entry(name, title, DescribeRole.Theorem, formula, text);
    private static DocumentBlock Entry(string name, string title, DescribeRole role, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("karp-zhang-ninh-homogeneous-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula D(int n) => new Formula.Number(n);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula R() => Seq(Mathbb, Grp(V("R")));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula C(string f, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(f), [.. a]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Ns(string[] names, Formula body) => All(names, N(), body);
    private static Formula Rs(string[] names, Formula body) => All(names, R(), body);
    private static Formula All(string[] names, Formula type, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, Parenthesized(Seq(V(names[i]), Colon, Sp, type)), Comma, Sp, body);
        return body;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Neg(Formula a) => new Formula.Negate(Parenthesized(a));
    private static Formula Mod(Formula a, Formula b) => App(Q("Nat", "mod"), a, b);
    private static Formula Choose(Formula a, Formula b) => App(Q("Nat", "choose"), a, b);
    private static Formula Range(Formula n) => App(Q("Finset", "range"), n);
    private static Formula Icc(Formula a, Formula b) => App(Q("Finset", "Icc"), a, b);
    private static Formula Indicator(Formula condition) => Cond(condition, D(1), D(0));
    private static Formula Cond(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(V("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(V("then")), Sp, Parenthesized(yes), Sp,
            Operatorname, Grp(V("else")), Sp, Parenthesized(no));
    private static Formula Cases(Formula n, Formula[] values)
    {
        var result = values[5];
        for (var i = 4; i >= 0; i--)
            result = Cond(Eq(Mod(n, D(6)), D(i)), values[i], result);
        return result;
    }
    private static Formula Sum(string i, Formula set, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(V(i), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Lambda(string n, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(n), Colon, Sp, R())), Sp, Mapsto, Sp, body));
}
