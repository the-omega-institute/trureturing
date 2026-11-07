using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class OeisA252505FourthPowerFreeConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/oeis2026a252505");
    private static readonly Formula N = F.Id("n");
    private static readonly Formula Dv = F.Id("d");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native counting and inverse definitions for the whole A252505 convolution.",
        H("The whole A252505 identity and its native counting bridges"),
        Blocks(
            Paragraph(Text("The universal convolution is open in Lean. The statements below give the unchanged target and its native counting and recursion interfaces. No settling theorem or Proved open-problem resolution is asserted.")),
            Def("FourthPowerFree", "The prime fourth-power exclusion",
                All("d", Iff(Call("FourthPowerFree", Dv), All("p",
                    Implies(Call("Nat.Prime", F.Id("p")),
                        Not(Divides(Pow(F.Id("p"), D(4)), Dv)))))),
                "For a positive divisor d, every prime p is excluded when p^4 divides d. No restriction on the size or number of prime factors is imposed."),
            Def("a", "The actual fourth-power-free divisor count",
                All("n", Eq(Call("a", N), Cast(App(Q("Finset", "card"),
                    App(Q("Finset", "filter"), Fun("d", Call("FourthPowerFree", Dv)), Divisors(N))), "Int"))),
                "OEIS A252505 NAME counts the positive fourth-power-free divisors. Nat.divisors contains exactly those positive divisors when n is positive. The count is cast to Int."),
            Def("UnitFractionPair", "The original rational equation",
                All("n", All("x", All("y", Iff(Call("UnitFractionPair", N, Pair(F.Id("x"), F.Id("y"))),
                    And(Lt(D(0), F.Id("x")), And(Lt(D(0), F.Id("y")),
                        And(Le(F.Id("x"), F.Id("y")), Eq(Frac(D(1), Cast(N, "Rat")),
                            Add(Frac(D(1), Cast(F.Id("x"), "Rat")),
                                Frac(D(1), Cast(F.Id("y"), "Rat"))))))))))),
                "Both denominators are positive naturals; their order is non-strict, so x=y is included. The equation is an equality in Rat."),
            Def("b", "The actual unit-fraction pair count",
                All("n", Eq(Call("b", N), Cast(App(Q("Nat", "card"),
                    App(F.Id("Subtype"), Fun("xy", Call("UnitFractionPair", N, F.Id("xy"))))), "Int"))),
                "OEIS A018892 is represented by the cardinality of the original solution subtype of Nat times Nat, rather than by an assumed divisor formula. The factor-pair equivalence proves this subtype finite for every positive n."),
            Def("tau", "The ordinary positive divisor count",
                All("n", Eq(Call("tau", N), App(Q("Finset", "card"), Divisors(N)))),
                "tau(n) is the number of positive divisors, including one and n when n is positive."),
            Def("h", "The ordinary ceiling divisor sum",
                All("n", Eq(Call("h", N), Sum(Divisors(N), "d",
                    Cast(Ceil(Frac(Cast(Call("tau", Dv), "Rat"), D(2))), "Int")))),
                "OEIS A140773 sums the ceiling of tau(d)/2 over all positive divisors d. The cast to Rat precedes division; Nat.ceil agrees with the ordinary ceiling because this rational is nonnegative."),
            Def("g", "The integer parity",
                All("n", Eq(Call("g", N), new Formula.Modulo(Call("h", N), D(2)))),
                "OEIS A369255 is the Int remainder h(n) modulo two, hence zero or one."),
            Def("c", "The canonical inverse with the source recursion",
                And(Eq(Call("c", D(1)), D(1)), All("n",
                    Implies(Lt(D(1), N), Eq(Call("c", N), Neg(Sum(
                        App(Q("Nat", "properDivisors"), N), "d",
                        Multiply(Call("g", App(Q("Nat", "div"), N, Dv)), Call("c", Dv)))))))),
                "The implementation directly reuses ArithmeticFunction.dirichletInverse over Int. Its value at one is one, and dirichletInverseFun_apply_ne supplies precisely this proper-divisor recursion. The private c_recursion proof verifies both clauses. The positive-domain uniqueness theorem below identifies it with the independently specified A378214; index zero is outside the target."),
            Def("InverseRecursion", "The independent recursive specification",
                AllFunction("v", Eq(Call("InverseRecursion", F.Id("v")), And(Eq(Call("v", D(1)), D(1)),
                    All("n", Implies(Lt(D(1), N), Eq(Call("v", N),
                        Neg(Sum(App(Q("Nat", "properDivisors"), N), "d",
                            Multiply(Call("g", App(Q("Nat", "div"), N, Dv)), Call("v", Dv)))))))))),
                "This predicate fixes the positive-domain values and imposes no value at zero."),
            Def("claim", "The unchanged complete conjecture",
                Eq(F.Id("claim"), All("n", Implies(Le(D(1), N),
                    Eq(Call("a", N), Sum(Divisors(N), "d",
                        Multiply(Call("b", Dv), Call("c", App(Q("Nat", "div"), N, Dv)))))))),
                "OEIS A252505 FORMULA: a(n) = Sum_{d|n} A018892(d)*A378214(n/d). [Conjectured]. This definition includes n=1, arbitrary prime support and every exponent. It is an unproved proposition in this module."),
            Def("factorPairs", "Finite ordered factor pairs",
                All("n", Eq(Call("factorPairs", N),
                    App(Q("Finset", "filter"), Fun("uv", Le(Call("Prod.fst", F.Id("uv")),
                        Call("Prod.snd", F.Id("uv")))),
                        App(Q("Nat", "divisorsAntidiagonal"), Pow(N, D(2)))))),
                "These are all positive pairs u<=v with uv=n^2. The equality case is retained."),
            Thm("unit_fraction_count", "Actual solutions equal the finite factor-pair count",
                All("n", Implies(Lt(D(0), N), Eq(Call("b", N),
                    Cast(App(Q("Finset", "card"), Call("factorPairs", N)), "Int")))),
                "Clearing nonzero rational denominators gives xy=n(x+y), which forces x>n and y>n. Subtract n from both entries. The inverse adds n to each factor; both inverse laws and the non-strict order are checked."),
            Thm("unit_fraction_divisor_formula", "The faithful divisor formula",
                All("n", Implies(Lt(D(0), N),
                    Eq(Multiply(D(2), Call("b", N)),
                        Add(Cast(Call("tau", Pow(N, D(2))), "Int"), D(1))))),
                "Swap the two factors. Each off-diagonal orbit has two entries; the unique fixed pair is (n,n). Thus 2b(n)=tau(n^2)+1. This derives the formula from the rational solution definition, including x=y=2n."),
            Thm("fourth_power_free_divisor_count", "The complete capped exponent count",
                All("n", Implies(Lt(D(0), N), Eq(Call("a", N),
                    Cast(App(Q("Finset", "prod"), App(Q("Nat", "primeFactors"), N),
                        Fun("p", Add(Call("min", App(Q("Nat", "factorization"), N, F.Id("p")), D(3)), D(1)))), "Int")))),
                "The canonical divisor/factorization equivalence restricts to exactly those exponent vectors with each coordinate at most three. Counting their finite box gives the product. Empty prime support gives one."),
            Thm("ceiling_sum_exponent_box", "The full ceiling staircase",
                All("n", Implies(Lt(D(0), N), Eq(Call("h", N),
                    Sum(App(Q("Finset", "Iic"), App(Q("Nat", "factorization"), N)), "f",
                        Cast(Ceil(Frac(Cast(App(Q("Finset", "card"),
                            App(Q("Finset", "Iic"), F.Id("f"))), "Rat"), D(2))), "Int"))))),
                "Every divisor corresponds to one exponent vector f bounded by the factorization of n; its own divisor count is the cardinality of Iic f. Both correspondences reuse the pinned Mathlib divisor-box map."),
            Thm("inverse_recursion_unique", "Uniqueness on the full positive domain",
                AllFunction("v", Implies(Call("InverseRecursion", F.Id("v")),
                    All("n", Implies(Lt(D(0), N), Eq(Call("v", N), Call("c", N)))))),
                "Strong induction uses only positive proper divisors, each strictly smaller than n. The n=1 clause comes directly from the specification. The arbitrary value v(0) is immaterial."),
            Paragraph(Text("The remaining whole gap is b=a*g for the independently defined functions. A finite-prime-support series proof must still encode divisor convolution, prove its series identities, prove the zero-or-one coefficient law, and descend the integral identity before reducing modulo two. Final inverse cancellation is then required. These missing steps are not certified by the native bridges above."))
        )));

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("a252505-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula AllFunction(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        new Formula.TypeArrow(F.Id("Nat"), F.Id("Int")), body);
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id("Nat"), body);
    private static Formula Fun(string name, Formula body) => Parenthesized(Seq(
        F.Id("fun"), Sp, F.Id(name), Sp, Mapsto, Sp, body));
    private static Formula Sum(Formula set, string name, Formula body) =>
        App(Q("Finset", "sum"), set, Fun(name, body));
    private static Formula Divisors(Formula n) => App(Q("Nat", "divisors"), n);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        name.Contains('.') ? App(Q(name.Split('.')[0], name.Split('.')[1]), args)
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula x, string type) => Parenthesized(Seq(x, Colon, F.Id(type)));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Ceil(Formula x) => App(Q("Nat", "ceil"), x);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Divides(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Not(Formula x) => Seq(F.Id("Not"), Sp, Parenthesized(x));
    private static Formula Neg(Formula x) => Subtract(D(0), x);
}
