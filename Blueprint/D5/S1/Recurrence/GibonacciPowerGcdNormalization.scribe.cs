using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GibonacciPowerGcdNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GibonacciPowerGcdNormalization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mbirikaspilker2022gibonaccipowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer seed content scales the gcd of all shifted power windows by its exponent.",
        H("Gibonacci Power-Window GCD Normalization"),
        Blocks(
            Paragraph(Text("Mbirika and Spilker's Question 6.2 concerns the gcd of infinitely many "
                + "finite power sums. The seeds are arbitrary signed integers except for the pair "
                + "(0,0); either individual seed may vanish. The window length is any positive "
                + "natural number, and every natural exponent at least three is included.")),
            Node("gibonacci", "The seeded integer recurrence", GibonacciFormula(),
                "Here fibRecZ is Mathlib's order-two linear recurrence over the integers with "
                + "coefficients (1,1), and mkSol assigns its unique solution to the initial vector "
                + "(a,b). Thus the sequence starts at indices zero and one, with the recurrence "
                + "G(n+2)=G(n+1)+G(n).", DescribeRole.Definition),
            Node("windowSum", "The exact source window", WindowFormula(),
                "The endpoints are inclusive: the terms have indices t+1 through t+k. The "
                + "definition also permits k=0 and any natural exponent; the theorem uses the "
                + "positive lengths and exponents at least three of the source question.",
                DescribeRole.Definition),
            Node("familyGcd", "The nonnegative gcd of a whole integer family", FamilyFormula(),
                "NatSetGcd denotes Mathlib's Nat.setGcd. It is applied to the full range of "
                + "natural absolute values and cast to the integers. Its universal divisibility "
                + "property includes every integer divisor, including zero and negative divisors. "
                + "No finite prefix or nonzero-family assumption enters this definition.",
                DescribeRole.Definition),
            Node("powerGcd", "The infinite power-window gcd", PowerFormula(),
                "This family ranges over every natural shift, starting at zero. In particular, "
                + "zero-valued windows and windows of odd powers of signed terms are included.",
                DescribeRole.Definition),
            Node("result", "Normalization by the gcd of the seeds", ResultFormula(),
                "The symbol ediv is integer division, and d is the integer cast of the natural "
                + "gcd of the seeds. The reconstruction equalities prove that both quotients are "
                + "exact; their gcd is one. Both recurrences, both nonnegativity assertions and "
                + "both all-integer-divisor specifications are part of the conclusion. "
                + "The proof uses LinearRecurrence.toInit to scale the entire seeded solution, "
                + "then mul_pow and Finset.mul_sum to scale each window. Nat.dvd_setGcd_iff "
                + "and Int.natAbs_dvd_natAbs characterize the infinite gcd. Divisibility "
                + "antisymmetry and cancellation by the positive scalar d raised to e give "
                + "the displayed equality. These are applications of general Mathlib algebra "
                + "to the source question; no assertion of literature priority is made.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("gibonacci-power-gcd-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula For(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, V(v), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula LeqTo(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Divides(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula If(Formula x, Formula y) => Seq(Par(x), Sp, Rightarrow, Sp, Par(y));
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
    private static Formula And(params Formula[] items) =>
        items.Skip(1).Aggregate(Par(items[0]), (a, b) => Seq(a, Sp, Land, Sp, Par(b)));
    private static Formula G(Formula a, Formula b, Formula n) => Op("gibonacci", a, b, n);
    private static Formula W(Formula a, Formula b, Formula k, Formula e, Formula t) =>
        Op("windowSum", a, b, k, e, t);
    private static Formula C(Formula a, Formula b, Formula k, Formula e) => Op("powerGcd", a, b, k, e);
    private static Formula SeedBind(Formula body) => For("a", Z, For("b", Z, body));

    private static Formula GibonacciFormula() => Disp(SeedBind(Eqn(
        Seq(Op("gibonacci", V("a"), V("b")), Colon, Sp, N, Sp, To, Sp, Z),
        Op("mkSol", V("fibRecZ"), Seq(OpenBracket, V("a"), Comma, V("b"), CloseBracket)))));

    private static Formula WindowFormula() => Disp(SeedBind(For("k", N, For("e", N, For("t", N,
        Eqn(W(V("a"), V("b"), V("k"), V("e"), V("t")),
            Seq(Sum, Underscore, Grp(Eqn(V("i"), D(1))), Caret, Grp(V("k")), Sp,
                Pow(G(V("a"), V("b"), Add(V("t"), V("i"))), V("e")))))))));

    private static Formula FamilyFormula() => Disp(For("f", Seq(N, Sp, To, Sp, Z),
        Eqn(Op("familyGcd", V("f")), Op("IntCast", Op("NatSetGcd",
            Seq(OpenBrace, Op("natAbs", Op("f", V("t"))), Sp, Mid, Sp,
                V("t"), InMacro, N, CloseBrace))))));

    private static Formula PowerFormula()
    {
        Formula family = Seq(Open, V("t"), Colon, N, Close, Sp, Mapsto, Sp,
            W(V("a"), V("b"), V("k"), V("e"), V("t")));
        Formula equality = Eqn(C(V("a"), V("b"), V("k"), V("e")), Op("familyGcd", family));
        return Disp(SeedBind(For("k", N, For("e", N, equality))));
    }

    private static Formula Recurrence(Formula a, Formula b) => And(
        Eqn(G(a, b, D(0)), a), Eqn(G(a, b, D(1)), b),
        For("n", N, Eqn(G(a, b, Add(V("n"), D(2))),
            Add(G(a, b, Add(V("n"), D(1))), G(a, b, V("n"))))));

    private static Formula Specification(Formula a, Formula b) => For("r", Z,
        IffOf(Divides(V("r"), C(a, b, V("k"), V("e"))),
            For("t", N, Divides(V("r"), W(a, b, V("k"), V("e"), V("t"))))));

    private static Formula ResultFormula()
    {
        Formula a = V("a"), b = V("b"), k = V("k"), e = V("e"), d = V("d");
        Formula aq = Op("ediv", a, d), bq = Op("ediv", b, d);
        Formula nonzero = Seq(Par(Seq(a, Sp, Neq, Sp, D(0))), Sp, Lor, Sp,
            Par(Seq(b, Sp, Neq, Sp, D(0))));
        Formula conclusion = And(
            Seq(D(0), Sp, Lt, Sp, d),
            Eqn(Mul(d, aq), a), Eqn(Mul(d, bq), b), Eqn(Op("gcd", aq, bq), D(1)),
            Recurrence(a, b), Recurrence(aq, bq),
            LeqTo(D(0), C(a, b, k, e)), LeqTo(D(0), C(aq, bq, k, e)),
            Specification(a, b), Specification(aq, bq),
            Eqn(C(a, b, k, e), Mul(Pow(d, e), C(aq, bq, k, e))));
        return Disp(SeedBind(If(nonzero, For("k", N, If(LeqTo(D(1), k),
            For("e", N, If(LeqTo(D(3), e), For("d", Z,
                If(Eqn(d, Op("IntCast", Op("gcd", a, b))), conclusion)))))))));
    }
}
