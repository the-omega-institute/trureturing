using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangCatalanPower;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both coefficient signs of Karp and Zhang's Conjecture 4.2.",
        H("Catalan powers preserve the two sequence classes"), Blocks(
            CoeffSection.Create(),
            IntervalSection.Create(),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-log-convex"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex"),
                H("Log-convex sequences"), StatementSource.FromAuthor(ConvexFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 1.1, page 2: “Let {fₖ}ₖ₌₀∞ be a non-negative nontrivial real sequence.” The log-convex clause reads: “If fₖ² ≤ fₖ₋₁fₖ₊₁ for all k ∈ ℕ, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).”")),
                    Paragraph(Text("Here the natural indices in the inequality start at one. The predicate keeps nonnegativity and nontriviality and imposes no interval-support condition. The literal inequalities also admit a sequence supported on {0}; that endpoint case is included. The log-concave class is the existing KarpZhangReciprocal.Result.IsLogConcave, including its interval-support condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-delta"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.delta"),
                H("The finite Turanian coefficient"), StatementSource.FromAuthor(DeltaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Printed page 8: “Forming the generalized Turánian”")),
                    new DocumentBlock.DisplayFormula(SourceTuranian()),
                    Paragraph(Text("“we will have”")),
                    new DocumentBlock.DisplayFormula(SourceCoefficient()),
                    new DocumentBlock.DisplayFormula(SourceKernel()),
                    Paragraph(Text("The coefficient a is Coeff.a, the literal quotient (t) rising factorial 2k divided by (t+1) rising factorial k times k factorial. Expanding the displayed M_k distributes 1/(k!(m-k)!) over its two products; each product is exactly Coeff.a k at its first shifted parameter times Coeff.a (m-k) at its second shifted parameter. Multiplication by h(k)h(m-k) and summation for k=0,...,m gives the Lean range (m+1) sum, with the same subtraction order. The source series starts at m=2; the finite definition also includes the vanishing degrees zero and one. Neither convergence nor growth assumptions on h are needed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.claim"),
                H("Conjecture 4.2"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4.2, page 8: Assume that {hₖ}ₖ₌₀∞ is log-concave (log-convex ) and independent of µ. Then the function µ → h(µ; x) defined in (15) is coefficient-wise log-concave (log-convex ).")),
                    Paragraph(Text("For every sequence h, nonnegative real mu, alpha and beta, and every natural coefficient degree, delta is nonnegative for the source's log-concave class and nonpositive for its log-convex class. The sequence is independent of the parameters because a single h is fixed before they are quantified."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.result"),
                H("Both signs hold in every degree"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The index law makes the full kernel sum zero. The positive derivative generator and reflected-interval cancellation give nonnegative central tails, including mu=0. The generic Abel identity KarpZhangReciprocal.Result.abel_layers writes delta as the increments of h(k)h(m-k) times these tails.")),
                    Paragraph(Text("For log-concavity, KarpZhangReciprocal.Result.balanced_step makes the increments nonnegative. For log-convexity, a zero at index one propagates to every positive index. Otherwise all entries are positive, the adjacent inequalities make successive ratios increase, and the balanced products decrease. The increments for q ≥ 1 are nonpositive; the q = 0 contribution vanishes because the full tail is zero. This includes finite and singleton log-concave supports and the log-convex sequence supported only at zero. The central term is counted once and the degrees zero and one require no special assumption."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-zhang-2023-conjecture-4-2"),
                    ResolutionKind.Proved)))));

    private static Formula SourceTuranian()
    {
        Formula x = F.Id("x");
        Formula m = F.Id("m");
        Formula h = F.Id("h");
        Formula coefficient = new Formula.Subscript(DeltaLower, m);
        Formula series(Formula t) => Seq(h, Open, t, Semi, Sp, x, Close);
        return Seq(Equal(Seq(new Formula.Subscript(Delta, h), Open,
                    Alpha, Comma, Sp, Beta, Semi, Sp, x, Close),
                Subtract(Multiply(series(Add(Mu, Alpha)), series(Add(Mu, Beta))),
                    Multiply(series(Mu), series(Add(Add(Mu, Alpha), Beta))))),
            Eq, Seq(Sum, Underscore, Grp(m, Eq, Num(2)), Caret, Grp(Infty), Sp,
                coefficient, Sp, new Formula.Power(x, m)));
    }

    private static Formula SourceCoefficient()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        return Equal(new Formula.Subscript(DeltaLower, m),
            Seq(Sum, Underscore, Grp(k, Eq, Num(0)), Caret, Grp(m), Sp,
                new Formula.Subscript(F.Id("h"), k), Sp,
                new Formula.Subscript(F.Id("h"), Subtract(m, k)), Sp,
                new Formula.Subscript(F.Id("M"), k)));
    }

    private static Formula SourceKernel()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula r = Subtract(m, k);
        Formula rising(Formula t, Formula n) => new Formula.Subscript(Parenthesized(t), n);
        Formula product(Formula u, Formula v) => new Formula.Fraction(
            Multiply(rising(u, Multiply(Num(2), k)), rising(v, Multiply(Num(2), r))),
            Multiply(rising(Add(u, Num(1)), k), rising(Add(v, Num(1)), r)));
        return Equal(new Formula.Subscript(F.Id("M"), k),
            Multiply(new Formula.Fraction(Num(1), Multiply(Seq(k, Bang), Seq(Parenthesized(r), Bang))),
                Seq(OpenBracket, Subtract(product(Add(Mu, Alpha), Add(Mu, Beta)),
                    product(Mu, Add(Add(Mu, Alpha), Beta))), CloseBracket)));
    }

    private static Formula ConvexFormula()
    {
        Formula h = F.Id("h");
        Formula k = F.Id("k");
        Formula nonnegative = All("k", F.Id("Nat"), Le(Num(0), App(h, k)));
        Formula nontrivial = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("k"), F.Id("Nat"),
            new Formula.Relation(App(h, k), FormulaRelationOperator.NotEqual, Num(0)));
        Formula local = All("k", F.Id("Nat"), Implies(Le(Num(1), k),
            Le(new Formula.Power(App(h, k), Num(2)), Multiply(App(h, Subtract(k, Num(1))), App(h, Add(k, Num(1)))))));
        return Disp(All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            Iff(App(F.Id("IsLogConvex"), h), And(nonnegative, And(nontrivial, local)))));
    }

    private static Formula DeltaFormula()
    {
        Formula h = F.Id("h");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula term = Multiply(Multiply(App(h, k), App(h, Subtract(m, k))),
            Subtract(Multiply(App(Q("Coeff", "a"), k, Add(mu, alpha)),
                    App(Q("Coeff", "a"), Subtract(m, k), Add(mu, beta))),
                Multiply(App(Q("Coeff", "a"), k, mu),
                    App(Q("Coeff", "a"), Subtract(m, k), Add(Add(mu, alpha), beta)))));
        Formula sum = Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp,
            App(Q("Finset", "range"), Add(m, Num(1)))), Sp, term);
        return Disp(All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"),
                All("m", F.Id("Nat"), Equal(App(F.Id("delta"), h, mu, alpha, beta, m), sum)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("h");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula d = App(F.Id("delta"), h, mu, alpha, beta, F.Id("m"));
        Formula assertion = All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"),
                All("m", F.Id("Nat"), Implies(Le(Num(0), mu), Implies(Le(Num(0), alpha),
                    Implies(Le(Num(0), beta), And(
                        Implies(App(Q("KarpZhangReciprocal", "Result", "IsLogConcave"), h), Le(Num(0), d)),
                        Implies(App(F.Id("IsLogConvex"), h), Le(d, Num(0))))))))))));
        return Disp(Iff(F.Id("claim"), assertion));
    }

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(F.Id(a)), Dot, Operatorname, Grp(F.Id(b)));
    private static Formula Q(string a, string b, string c) => Seq(Q(a, b), Dot, Operatorname, Grp(F.Id(c)));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}

internal static class CoeffSection
{
    public static DocumentBlock Create() => new DocumentBlock.Section(
        H("Catalan power coefficients"), Blocks(
            Node("a", "The coefficient in formula (15)", DescribeRole.Definition,
                All("n", Nat(), All("t", Real(), Eq(A(X("n"), X("t")),
                    Div(Poch(Mul(D(2), X("n")), X("t")),
                        Mul(Poch(X("n"), Add(X("t"), D(1))), Fact(X("n"))))))),
                "Formula (15), printed page 8: “We consider the series” h(µ; x) := ∑ hₖ (µ)₂ₖ / ((µ+1)ₖ k!) xᵏ. The coefficient is the literal quotient (t) at rising order 2n divided by (t+1) at rising order n and n factorial. Real division is total. Its polynomial continuation agrees with this quotient whenever t is greater than minus one, including every nonnegative parameter."),
            Node("coeffPoly", "The polynomial continuation", DescribeRole.Definition,
                Seq(Eq(Call("coeffPoly", D(0)), D(1)), Comma, Quad,
                    All("n", Nat(), Eq(Call("coeffPoly", Add(X("n"), D(1))),
                        Seq(Call("C", new Formula.Power(Fact(Add(X("n"), D(1))), Seq(Minus, D(1)))),
                            Sp, Times, Sp, X("X"), Sp, Times, Sp,
                            App(Q("Polynomial", "comp"), Call("ascPochhammer", Real(), X("n")),
                                Par(Add(X("X"), Call("C", Add(X("n"), D(2)))))))))),
                "The degree-zero polynomial is one. At degree n+1 the polynomial is X times the rising Pochhammer polynomial of order n evaluated at X+n+2, divided by (n+1) factorial."),
            Node("coeffPoly_succ_eval", "Evaluation of the continuation", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Eq(Eval(Call("coeffPoly", Add(X("n"), D(1))), X("t")),
                    Div(Mul(X("t"), Poch(X("n"), Add(Add(X("t"), X("n")), D(2)))),
                        Fact(Add(X("n"), D(1))))))),
                "Polynomial evaluation gives the product t times the rising factorial at t+n+2. This form is used to cancel the denominator of the original quotient."),
            Node("a_eq_polynomial", "Cancellation away from the poles", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(Seq(Minus, D(1)), X("t")),
                    Eq(A(X("n"), X("t")), Eval(Call("coeffPoly", X("n")), X("t")))))),
                "For t greater than minus one, all factors of (t+1) at rising order n are positive. Pochhammer multiplication splits off these factors and cancels them, including t=0."),
            Node("a_pos", "Positivity", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(D(0), X("t")), Lt(D(0), A(X("n"), X("t")))))),
                "The numerator rising factorial and both denominator factors are positive at a positive parameter, by ascPochhammer_pos and factorial positivity."),
            Node("a_zero_parameter", "The zero parameter", DescribeRole.Theorem,
                All("n", Nat(), Imp(Lt(D(0), X("n")), Eq(A(X("n"), D(0)), D(0)))),
                "At parameter zero every positive-degree coefficient vanishes. This supplies the boundary case of the interval tail inequality."),
            Node("a_nonneg", "Nonnegative parameters", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Le(D(0), X("t")), Le(D(0), A(X("n"), X("t")))))),
                "The positive-parameter result and the value at zero show nonnegativity on the entire closed nonnegative half-line."),
            Node("adjacent_ratio", "Adjacent coefficient ratios", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(D(0), X("t")),
                    Eq(A(Add(X("n"), D(1)), X("t")), Mul(A(X("n"), X("t")),
                        Div(Mul(Add(X("t"), Mul(D(2), X("n"))),
                                Add(Add(X("t"), Mul(D(2), X("n"))), D(1))),
                            Mul(Add(Add(X("t"), X("n")), D(1)), Add(X("n"), D(1))))))))),
                "The ratio a(n+1,t)/a(n,t), multiplied by n+1, is (t+2n)(t+2n+1)/(t+n+1), including n=0. Cross multiplication at two positive parameters shows that this ratio strictly increases with the parameter."),
            Node("tp2", "Strict total positivity of order two", DescribeRole.Theorem,
                TP2(false),
                "If i is less than l and 0<u<v, the cross product a(i,u)a(l,v) exceeds a(l,u)a(i,v). The adjacent ratio comparison extends through every degree gap by strictMono_nat_of_lt_succ applied to a(n,v)/a(n,u). The interval derivative uses this strict sign after reflection."),
            Node("tp2_le", "The weak cross-product order", DescribeRole.Theorem,
                TP2(true),
                "For 0<u≤v the same determinant is nonnegative. At equal parameters it is zero; otherwise strict total positivity applies."),
            IndexSection.Create()));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("kz42-coeff-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), Provenance(name),
            Blocks(Paragraph(Text(prose))), role);
    private static AssessedProvenance Provenance(string name) =>
        name == "a"
            ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer"))
            : AssessedProvenance.FromRepo();
    private static Formula X(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Fact(Formula n) => Seq(Par(n), Bang);
    private static Formula Eval(Formula p, Formula t) => App(Q("Polynomial", "eval"), t, p);
    private static Formula Poch(Formula n, Formula t) => Eval(Call("ascPochhammer", Real(), n), t);
    private static Formula A(Formula n, Formula t) => Call("a", n, t);
    private static Formula TP2(bool weak) => All("u", Real(), All("v", Real(),
        All("i", Nat(), All("l", Nat(), Imp(Lt(D(0), X("u")),
            Imp(weak ? Le(X("u"), X("v")) : Lt(X("u"), X("v")),
                Imp(Lt(X("i"), X("l")), weak
                    ? Le(Mul(A(X("l"), X("u")), A(X("i"), X("v"))), Mul(A(X("i"), X("u")), A(X("l"), X("v"))))
                    : Lt(Mul(A(X("l"), X("u")), A(X("i"), X("v"))), Mul(A(X("i"), X("u")), A(X("l"), X("v")))))))))));
}

internal static class IndexSection
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangCatalanPower/Result.";

    public static DocumentBlock Create() => new DocumentBlock.Section(H("Convolution and differentiation of Catalan-power coefficients"), Blocks(
            Paragraph(Text("Polynomial.eval t (coeffPoly n) evaluates the coefficient polynomial at t. The coefficient a(n,t) is the literal rising-factorial quotient in formula (15). The two agree for t greater than minus one. The generator b(j) is the derivative of a(j,t) at t=0. All sums are finite; natural subtraction occurs only with the subtracted index bounded by the degree.")),
            Node("index_polynomial", "The polynomial convolution law", DescribeRole.Theorem,
                All("s", Real(), All("t", Real(), All("m", Nat(),
                    Eq(SumRange("k", Add(X("m"), D(1)), Mul(Eval(X("k"), X("s")),
                            Eval(Sub(X("m"), X("k")), X("t")))),
                        Eval(X("m"), Add(X("s"), X("t"))))))),
                "Lemma 4.1(2), printed page 8, states “Index law” λ(α; x)λ(β; x) = λ(α+β; x), attributed to [17, Lemma 7]. Here the coefficient law is expressed using polynomial continuation. The identity holds for arbitrary real s and t, including the roots of denominator factors in the original quotient. The existing Catalan Lagrange coefficient transform identifies evaluation of coeffPoly n at a natural t with the coefficient of C to the natural power t. Multiplication of natural powers supplies convolution on the natural grid. Polynomial uniqueness extends first in s and then in t. The supplied Lagrange transform is reused directly; no real formal power is assumed."),
            Node("index_law", "The index law for the original coefficients", DescribeRole.Theorem,
                All("s", Real(), All("t", Real(), All("m", Nat(),
                    Imp(Le(D(0), X("s")), Imp(Le(D(0), X("t")),
                        Eq(SumRange("k", Add(X("m"), D(1)), Mul(A(X("k"), X("s")),
                                A(Sub(X("m"), X("k")), X("t")))),
                            A(X("m"), Add(X("s"), X("t"))))))))),
                "Lemma 4.1(2), printed page 8: “Index law” λ(α; x)λ(β; x) = λ(α+β; x). The lemma is attributed to [17, Lemma 7]. For nonnegative s and t, every denominator factor in formula (15) is positive. Substitution of the polynomial form into the all-real polynomial convolution proves the index law. Both zero parameters are included. The literal totalized quotient is not asserted to satisfy the law at negative poles."),
            Node("b", "The infinitesimal generator", DescribeRole.Definition,
                All("j", Nat(), Eq(Call("b", X("j")),
                    Call("deriv", Call("a", X("j")), D(0)))),
                "The generator coefficient is the derivative at zero of the original coefficient function. Its polynomial representation is valid on a neighborhood of zero."),
            Node("b_eq_centralBinom", "The generator in closed form", DescribeRole.Theorem,
                All("j", Nat(), Imp(Le(D(1), X("j")),
                    Eq(Call("b", X("j")), Div(App(Q("Nat", "choose"),
                        Par(Mul(D(2), X("j"))), X("j")), Mul(D(2), X("j")))))),
                "For every positive natural j, differentiation at zero leaves the product from j+1 through 2j-1 divided by j factorial. Rising-factorial and binomial identities convert it to Nat.choose (2j) j divided by 2j. The division is real division and 2j is positive."),
            Node("b_pos", "Every positive-degree generator coefficient is positive", DescribeRole.Theorem,
                All("j", Nat(), Imp(Le(D(1), X("j")), Lt(D(0), Call("b", X("j"))))),
                "The central binomial coefficient and the denominator 2j are positive. This positivity weights each reflected determinant in the interval-slice derivative."),
            Node("hasDerivAt_a", "Differentiation is convolution with the generator", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Le(D(0), X("t")),
                    Call("HasDerivAt", Call("a", X("n")),
                        SumIcc("j", D(1), X("n"), Mul(Call("b", X("j")),
                            A(Sub(X("n"), X("j")), X("t")))), X("t"))))),
                "At every nonnegative t, the derivative of a(n,t) is the sum of b(j)a(n-j,t), with j from one through n. Differentiate the polynomial index law in its first parameter at zero. The derivative of the degree-zero polynomial is zero, so that summand drops out. Equality with the literal quotient on the open interval t greater than minus one supplies a two-sided derivative, also at t=0. The degree-zero sum is empty.")));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("kz42-index-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), Provenance(name),
            Blocks(Paragraph(Text(text))), role);
    private static AssessedProvenance Provenance(string name) =>
        (name == "index_law" || name == "index_polynomial")
            ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer"))
            : AssessedProvenance.FromRepo();
    private static Formula X(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Eval(Formula degree, Formula argument) =>
        App(Q("Polynomial", "eval"), Par(argument), Call("coeffPoly", degree));
    private static Formula A(Formula degree, Formula argument) => Call("a", degree, argument);
    private static Formula SumRange(string index, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(X(index), InMacro,
            App(Q("Finset", "range"), Par(upper)))), Sp, body);
    private static Formula SumIcc(string index, Formula lower, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(X(index), InMacro,
            App(Q("Finset", "Icc"), lower, upper))), Sp, body);
}

internal static class IntervalSection
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangCatalanPower/Result.";

    public static DocumentBlock Create() => new DocumentBlock.Section(
        H("Reflected intervals and tail positivity"),
        Blocks(
            Paragraph(Text("All sums are finite. The coefficient a(n,t) is the rising-factorial quotient, and b(j) is its derivative at zero. Natural subtraction occurs only under the stated finite bounds. The boundary filter also handles empty signed intervals without assigning a spurious term to index zero.")),
            Entry("R", "The uncancelled left boundary", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("j", N(),
                    Eq(Call("R", V("m"), V("q"), V("j")), BoundaryBody())))),
                "R contains exactly the nonnegative integers in [max(0,q-j), min(q-1,m-q-j)], where the upper endpoint is an integer. Its filter presentation retains the condition i+j≤m-q, so the set is empty when the signed upper endpoint is negative."),
            Entry("Z", "The central convolution interval", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("u", Rl(), All("v", Rl(),
                    Eq(Z(V("u"), V("v")), IntervalSum(Product(V("k"), V("u"), V("v")))))))),
                "Z(m,q,u,v) sums a(k,u)a(m-k,v) for q≤k≤m-q. The two endpoints are included, including a singleton central interval."),
            Entry("sliceDerivative", "The reflected determinant sum", DescribeRole.Definition,
                All("m", N(), All("q", N(), All("u", Rl(), All("v", Rl(),
                    Eq(Call("sliceDerivative", V("m"), V("q"), V("u"), V("v")),
                        FluxBody(V("u"), V("v"))))))),
                "For each j from one through m, multiply b(j) by the sum over R(m,q,j) of the degree-parameter determinants with total degree m-j. This is the derivative of Z along a constant-sum line."),
            Entry("reflected_interval", "Cancellation of two reflected intervals", DescribeRole.Theorem,
                All("m", N(), All("q", N(), All("j", N(),
                    Imp(Le(Mul(D(2), V("q")), V("m")), Imp(Le(V("j"), V("m")),
                        All("w", Arrow(N(), Rl()), Eq(
                            Sub(Sum("i", Window(true), Call("w", V("i"))),
                                Sum("i", Window(false), Call("w", V("i")))),
                            Sum("i", Call("R", V("m"), V("q"), V("j")),
                                Sub(Call("w", V("i")), Call("w", Sub(Sub(V("m"), V("j")), V("i")))))))))))),
                "Restrict both intervals to 0≤i≤m-j. Reflection i↦m-j-i exchanges them. The common part cancels, and the remaining terms pair over R. The identity holds for every real-valued weight w, with no sign assumption."),
            Entry("hasDerivAt_slice", "The constant-sum slice derivative", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(Mul(D(2), V("q")), V("m")),
                    All("S", Rl(), All("r", Rl(), Imp(Lt(D(0), V("r")),
                        Imp(Lt(D(0), Sub(V("S"), V("r"))),
                            Call("HasDerivAt", Slice(), Call("sliceDerivative", V("m"), V("q"),
                                V("r"), Sub(V("S"), V("r"))), V("r"))))))))),
                "Differentiate every finite summand. The coefficient derivative identity expands each factor into a lower-degree convolution. Two explicit triangular bijections collect terms with the same j. Reflection then converts their difference into the determinant sum."),
            Entry("Z_symm", "Reflection symmetry of the interval convolution", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(Mul(D(2), V("q")), V("m")),
                    All("u", Rl(), All("v", Rl(), Eq(Z(V("u"), V("v")), Z(V("v"), V("u")))))))),
                "The map k↦m-k permutes the closed central interval and exchanges the two coefficient factors. Balancing can therefore choose the smaller parameter as the first coordinate."),
            Entry("slice_strictMonoOn", "Strict increase toward the midpoint", DescribeRole.Theorem,
                All("m", N(), All("q", N(), Imp(Le(D(1), V("q")),
                    Imp(Le(Mul(D(2), V("q")), V("m")), All("S", Rl(),
                        Imp(Lt(D(0), V("S")),
                            Call("StrictMonoOn", Slice(), App(Qualified("Set", "Ioc"), D(0),
                                new Formula.Fraction(V("S"), D(2)))))))))),
                "On the open left half of a positive constant-sum slice, every determinant is positive whenever its boundary set is nonempty. Every b(j) is positive. The j=1 boundary contains q-1, and its two degrees are strictly ordered, so the derivative is strictly positive. The mean-value theorem gives strict increase on (0,S/2], including comparisons with the midpoint."),
            Entry("tail_nonneg", "Every shifted central tail is nonnegative", DescribeRole.Theorem,
                All("m", N(), All("q", N(),
                    Imp(Le(Mul(D(2), V("q")), V("m")),
                        All("mu", Rl(), All("alpha", Rl(), All("beta", Rl(),
                            Imp(Le(D(0), V("mu")), Imp(Le(D(0), V("alpha")),
                                Imp(Le(D(0), V("beta")), Le(D(0), IntervalSum(Delta()))))))))))),
                "The case q=0 is the full convolution: both products have the same total parameter, so the index law makes their difference zero. For q positive and mu positive, keep S=2mu+alpha+beta fixed and compare mu with mu+min(alpha,beta) on (0,S/2]. Symmetry supplies the correct ordering of the two shifted parameters. If q is positive and mu=0, every index in the tail is positive, so a(k,0)=0 and the remaining product is nonnegative. No limiting argument or additional positivity hypothesis on mu is required.")));

    private static DocumentBlock Entry(string declaration, string title, DescribeRole role,
        Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("karp-zhang-interval-" + declaration.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rl() => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sum(string index, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(V(index), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, Rl())),
            Sp, Mapsto, Sp, body));
    private static Formula NatLambda(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, N())),
            Sp, Mapsto, Sp, body));
    private static Formula Range() =>
        App(Qualified("Finset", "range"), Add(Sub(V("m"), V("j")), D(1)));
    private static Formula Bounds(bool left) => left
        ? And(Le(V("q"), Add(V("i"), V("j"))), Le(Add(V("i"), V("j")), Sub(V("m"), V("q"))))
        : And(Le(V("q"), V("i")), Le(V("i"), Sub(V("m"), V("q"))));
    private static Formula Window(bool left) =>
        App(Qualified("Finset", "filter"), NatLambda("i", Bounds(left)), Range());
    private static Formula BoundaryBody() =>
        App(Qualified("Finset", "filter"),
            NatLambda("i", And(Bounds(true), Lt(V("i"), V("q")))), Range());
    private static Formula Z(Formula u, Formula v) => Call("Z", V("m"), V("q"), u, v);
    private static Formula IntervalSum(Formula body) =>
        Sum("k", App(Qualified("Finset", "Icc"), V("q"), Sub(V("m"), V("q"))), body);
    private static Formula Product(Formula k, Formula u, Formula v) =>
        Mul(Call("a", k, u), Call("a", Sub(V("m"), k), v));
    private static Formula Slice() => Lambda("x", Z(V("x"), Sub(V("S"), V("x"))));
    private static Formula FluxBody(Formula u, Formula v) =>
        Sum("j", App(Qualified("Finset", "Icc"), D(1), V("m")),
            Mul(Call("b", V("j")),
                Sum("i", Call("R", V("m"), V("q"), V("j")),
                    Sub(Mul(Call("a", V("i"), u), Call("a", Sub(Sub(V("m"), V("j")), V("i")), v)),
                        Mul(Call("a", Sub(Sub(V("m"), V("j")), V("i")), u), Call("a", V("i"), v))))));
    private static Formula Delta() =>
        Sub(Product(V("k"), Add(V("mu"), V("alpha")), Add(V("mu"), V("beta"))),
            Product(V("k"), V("mu"), Add(Add(V("mu"), V("alpha")), V("beta"))));
}
