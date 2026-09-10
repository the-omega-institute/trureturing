using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ParametricExponentialSquareCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.";
    private const string Frozen = "D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd square-weight parameters have binary parity support; parameter two has period four modulo eight.",
        H("Congruences for the Exponential Square-Weight Family"),
        Blocks(
            Paragraph(Text("For integer q, define the integral normalization b(q,n), and set "
                + "a(q,0)=1 and a(q,n)=n b(q,n) for positive n. For q nonzero, source_iff "
                + "proves that these are exactly the coefficients of the self-referential "
                + "formal equation A=exp(L). Here L=x+Sum (q n^2-1)a(q,n)x^n/(q n^2), "
                + "with the sum starting at n=2. The equation is formal, with no assertion "
                + "of analytic convergence. The integer parameter is 5, 3, 1 or 2; it is "
                + "not the square-root parameter used in the entries' reversion formulas.")),
            Paragraph(Text("All indices are natural. Subtraction in an index is natural "
                + "subtraction; coefficients and weights use integer or rational ring "
                + "subtraction. int and rat are the indicated canonical casts; mod2 and "
                + "mod8 are casts to ZMod(2) and ZMod(8). mapRat maps an integer power "
                + "series to the rationals. mk constructs a power series from its coefficients; "
                + "coeff extracts a coefficient, C is a constant series, derivative is the "
                + "formal derivative over the displayed ring, subst is formal substitution, "
                + "and expQ is the standard rational exponential power series. Ico(r,n) "
                + "means r<=j<n, and range(n) means 0<=j<n.")),
            Paragraph(Text("The imported d and a1 are the exact frozen q=1 definitions "),
                Ref(Frozen + "d"), Text(" and "), Ref(Frozen + "a"), Text(". Their parity theorem "),
                Ref(Frozen + "hanna_conjecture"), Text(" already settles A397242. It is reused "
                    + "here and receives no second problem claim. The new work is strong "
                    + "induction transporting odd parameters modulo two, and endpoint "
                    + "separation of the parameter-two convolution modulo eight.")),
            Node("b", "The integral normalization", BDefinition(),
                "The guarded recursion only calls smaller indices; b(q,0)=0 and b(q,1)=1.",
                DescribeRole.Definition),
            Node("a", "Original coefficients", ADefinition(),
                "Positive coefficients are index multiples of the integer normalization.",
                DescribeRole.Definition),
            Node("b_recurrence", "The bounded convolution", AllQN(Impl(Leq(D(2), N()),
                Eqn(B(Q(), N()), Recurrence()))),
                "Filtering the guarded range gives exactly the interval 2<=j<n."),
            Node("a_eq", "Normalization at positive indices", AllQN(Impl(Leq(D(1), N()),
                Eqn(A(Q(), N()), Mul(Call("int", N()), B(Q(), N()))))),
                "This companion exposes the positive branch for the source and congruence proofs."),
            Node("M", "Scaled logarithmic derivative", AllQ(Eqn(M(), Call("mk", Lam("n",
                If(Eqn(N(), D(0)), D(0), If(Eqn(N(), D(1)), Q(),
                    Mul(Weight(Call("int", N())), B(Q(), N())))))))),
                "M has coefficients 0, q and (q n^2-1)b(q,n), in degrees 0, 1 and n>=2.",
                DescribeRole.Definition),
            Node("log_derivative_identity", "The integral differential equation", AllQ(And(
                Eqn(Call("coeff", D(0), AS()), D(1)), Equation(AS(), M(), Z(), Q()))),
                "Separate the last coefficient and degree-one term of M A. The remaining "
                + "sum is b's recurrence, so adding the diagonal yields q n^2 b(q,n)."),
            Node("coeff_M_rat", "Exact rational weights", AllQN(Impl(Leq(D(2), N()),
                Eqn(Call("coeff", N(), Call("mapRat", M())),
                    RationalWeight(Call("rat", A(Q(), N())))))),
                "Cancel the nonzero index n after using a(q,n)=n b(q,n)."),
            Node("generating_unique", "Rational differential uniqueness", UniqueFormula(),
                "Strong induction equates all smaller convolution terms. At degree one "
                + "q nonzero forces the coefficient 1. At higher degrees the diagonal "
                + "weight cancels q n^2, leaving a coefficient difference equal to zero."),
            Node("exponent", "The source exponent", ExponentFormula(),
                "The constant term is zero, the linear coefficient is one, and all "
                + "higher divisions occur in Q.", DescribeRole.Definition),
            Node("source_iff", "Literal equivalence with the OEIS equation", SourceFormula(),
                "The forward implication differentiates exp(L) using Mathlib's chain rule "
                + "and derivative_exp, then applies generating_unique. Conversely the "
                + "integer solution and exp(L) satisfy F'=L'F with the same constant "
                + "coefficient; coefficient induction proves linear ODE uniqueness. This "
                + "establishes existence and uniqueness for every nonzero integer parameter."),
            Node("normalized_mod_two", "Transport to the frozen normalization", AllQN(Impl(
                Call("Odd", Q()), Eqn(Call("mod2", B(Q(), N())), Call("mod2", Call("d", N()))))),
                "Strong induction reduces the recurrence coefficients using q=1 in ZMod(2) "
                + "and substitutes the induction hypothesis in both smaller factors. "
                + "This is the live new witness for the odd-parameter endpoints."),
            Node("odd_parameter_parity", "Parity for every odd parameter", AllQN(Impl(
                Call("Odd", Q()), Parity(Q(), N()))),
                "Multiply the transported normalization by n and apply the frozen "
                + "hanna_conjecture. The constant coefficient is handled separately."),
            Node("normalized_mod_eight", "The stronger parameter-two invariant", Disp(Seq(
                Bind("n", Nat()), Impl(Leq(D(2), N()), Eqn(Call("mod8", B(D(2), N())),
                    If(Eqn(Call("mod", N(), D(4)), D(3)), D(6), D(2)))))),
                "For n>=3, the endpoint contributes (2n(n-1)-1)b(2,n-1). "
                + "Every interior term reduces to 4(n-j) modulo eight, whose sum is "
                + "2(n-2)(n-1)-4. Eight residue cases close the induction step. "
                + "The induction quantifies over all indices; it is not bounded enumeration."),
            Node("residues_q2", "A397346 modulo eight", ResiduesFormula(),
                "Multiplication by n turns the normalized invariant into residues 4,2,0,2 "
                + "from n=2, with period four.", DescribeRole.Theorem,
                "hanna2026a397346", "oeis-a397346-square-weight-mod-eight"),
            Node("parity_q5", "A397345 parity", Disp(Seq(Bind("n", Nat()), Parity(D(5), N()))),
                "Specialize the odd-parameter theorem using 5=2*2+1. The source_iff "
                + "theorem identifies this coefficient sequence with the NAME equation.",
                DescribeRole.Theorem, "hanna2026a397family", "oeis-a397345-square-weight-parity"),
            Node("parity_q3", "A397348 parity", Disp(Seq(Bind("n", Nat()), Parity(D(3), N()))),
                "Specialize using 3=2*1+1, with the same literal source correspondence.",
                DescribeRole.Theorem, "hanna2026a397348", "oeis-a397348-square-weight-parity"),
            Node("family_conjectures", "The four dispatched endpoints", FamilyFormula(),
                "This conjunction packages the three new endpoints and the already frozen "
                + "A397242 parity theorem. It is a companion, not an additional resolution. "
                + "No asymptotic limits, priority claim or further modulus is asserted."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, string? bibkey = null, string? slug = null) =>
        Describe.Lean(DescribeId.Create("a397family-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            bibkey is null ? AssessedProvenance.FromRepo() :
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Recurrence/" + bibkey)),
            Blocks(Paragraph(Text(prose))), role,
            slug is null ? null : new OpenProblemResolutionClaim(
                ProblemSlugRef.Create(slug), ResolutionKind.Proved));

    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Multiply, Par(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Impl(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula Iffn(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
    private static Formula If(Formula test, Formula yes, Formula no) => Par(Seq(
        Named("if"), Sp, Par(test), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no));
    private static Formula Fun(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Bind(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lam(string name, Formula value) => Par(Seq(F.Id(name), Sp, Mapsto, Sp, value));
    private static Formula AllQ(Formula f) => Disp(Seq(Bind("q", Z()), f));
    private static Formula AllQN(Formula f) => Disp(Seq(Bind("q", Z()), Bind("n", Nat()), f));
    private static Formula A(Formula q, Formula n) => Call("a", q, n);
    private static Formula B(Formula q, Formula n) => Call("b", q, n);
    private static Formula M() => Call("M", Q());
    private static Formula AS() => Call("mk", Call("a", Q()));
    private static Formula Weight(Formula j) => Sub(Mul(Q(), Pow(j, D(2))), D(1));
    private static Formula RationalWeight(Formula value) => new Formula.Fraction(
        Mul(Sub(Mul(Call("rat", Q()), Pow(Call("rat", N()), D(2))), D(1)), value), Call("rat", N()));
    private static Formula Summand() => Mul(Mul(Mul(Weight(Call("int", F.Id("j"))),
        Call("int", Sub(N(), F.Id("j")))), B(Q(), F.Id("j"))), B(Q(), Sub(N(), F.Id("j"))));
    private static Formula Sum(Formula set, Formula term) => Seq(new Formula.Subscript(F.Sum,
        Seq(F.Id("j"), Sp, InMacro, Sp, set)), Sp, Par(term));
    private static Formula Recurrence() => Add(Mul(Mul(Q(), Call("int", Sub(N(), D(1)))),
        B(Q(), Sub(N(), D(1)))), Sum(Call("Ico", D(2), N()), Summand()));
    private static Formula BDefinition() => AllQN(Eqn(B(Q(), N()), If(Leq(D(2), N()),
        Add(Mul(Mul(Q(), Call("int", Sub(N(), D(1)))), B(Q(), Sub(N(), D(1)))),
            Sum(Call("range", N()), If(And(Leq(D(2), F.Id("j")),
                Seq(F.Id("j"), Sp, Lt, Sp, N())), Summand(), D(0)))),
        If(Eqn(N(), D(1)), D(1), D(0)))));
    private static Formula ADefinition() => AllQN(Eqn(A(Q(), N()), If(Eqn(N(), D(0)),
        D(1), Mul(Call("int", N()), B(Q(), N())))));
    private static Formula Equation(Formula series, Formula m, Formula ring, Formula q) =>
        Eqn(Mul(Call("C", q), Mul(F.Id("X"), Call("derivative", ring, series))), Mul(m, series));
    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f"), m = F.Id("m");
        Formula At(Formula n) => new Formula.Apply(f, [n]);
        Formula shape = Seq(Bind("n", Nat()), Impl(Leq(D(2), N()),
            Eqn(Call("coeff", N(), m), RationalWeight(At(N())))));
        Formula conclusion = Seq(Bind("n", Nat()), Eqn(At(N()), Call("rat", A(Q(), N()))));
        Formula ode = Equation(Call("mk", f), m, Rat(), Call("rat", Q()));
        Formula hypotheses = Impl(Seq(Q(), Sp, Neq, Sp, D(0)),
            Impl(Eqn(At(D(0)), D(1)), Impl(Eqn(Call("coeff", D(0), m), D(0)),
            Impl(Eqn(Call("coeff", D(1), m), Call("rat", Q())), Impl(shape, Impl(ode, conclusion))))));
        return AllQ(Seq(Bind("f", Fun(Nat(), Rat())),
            Bind("m", Call("PowerSeries", Rat())), hypotheses));
    }
    private static Formula ExponentFormula() => AllQ(Seq(Bind("f", Fun(Nat(), Rat())),
        Eqn(Call("exponent", Q(), F.Id("f")), Call("mk", Lam("n", If(Eqn(N(), D(0)), D(0),
            If(Eqn(N(), D(1)), D(1), new Formula.Fraction(
                Mul(Sub(Mul(Call("rat", Q()), Pow(Call("rat", N()), D(2))), D(1)), Call("f", N())),
                Mul(Call("rat", Q()), Pow(Call("rat", N()), D(2)))))))))));
    private static Formula SourceFormula() => AllQ(Seq(Bind("f", Fun(Nat(), Rat())),
        Impl(Seq(Q(), Sp, Neq, Sp, D(0)), Iffn(Eqn(Call("mk", F.Id("f")),
            Call("subst", Named("expQ"), Call("exponent", Q(), F.Id("f")))),
            Seq(Bind("n", Nat()), Eqn(Call("f", N()), Call("rat", A(Q(), N()))))))));
    private static Formula Support(Formula n) => Seq(Exists, Sp, F.Id("k"), Colon, Sp, Nat(),
        Comma, Sp, Eqn(Add(n, D(1)), Pow(D(2), F.Id("k"))));
    private static Formula Parity(Formula q, Formula n) => Iffn(Call("Odd", A(q, n)), Support(n));
    private static Formula Residues() => If(Eqn(Call("mod", N(), D(4)), D(2)), D(4),
        If(Eqn(Call("mod", N(), D(4)), D(0)), D(0), D(2)));
    private static Formula ResiduesBody() => Seq(Bind("n", Nat()), Impl(Leq(D(2), N()),
        Eqn(Call("mod", A(D(2), N()), D(8)), Residues())));
    private static Formula ResiduesFormula() => Disp(ResiduesBody());
    private static Formula FamilyFormula() => Disp(And(Seq(Bind("n", Nat()), Parity(D(5), N())),
        And(Seq(Bind("n", Nat()), Parity(D(3), N())), And(Seq(Bind("n", Nat()),
            Iffn(Call("Odd", Call("a1", N())), Support(N()))), ResiduesBody()))));
}
