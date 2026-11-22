using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelTailFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure and mixed prime-predecessor families",
        H("Pure and mixed prime-predecessor families"), Blocks(
            Node("same_parity_geometric_budget", "Two parity families have a strict budget",
                ParityBudget(),
                "The two finite families correspond to odd-odd and even-even positive " +
                "exponents. For r>1 their combined mass is strictly less than " +
                "r(2r+1)/(3(r^2-1)). Finite families omit positive terms of the convergent " +
                "geometric series, so equality is impossible."),
            Node("even_first_geometric_budget", "Even first exponents have a strict budget",
                EvenBudget(),
                "With the first exponent positive and even, the mass is strictly less " +
                "than r/(3(r-1)). No bound on either finite set of exponents is required."),
            Node("even_first_budget_le_same_parity", "Comparison of the uniform budgets",
                All("r", Rat(), Imp(Lt(D(1), V("r")),
                    Lt(Div(V("r"), Mul(D(3), Sub(V("r"), D(1)))), Budget(V("r"))))),
                "For r>1 the even-first budget is strictly smaller than the combined " +
                "parity budget. The boundary r=1 cannot be admitted: rational division " +
                "by zero makes both displayed expressions zero."),
            Node("pure_tail_bound", "The exact endpoint of the pure budget", PureBound(),
                "For r>=5 the pure budget is at most 55/72, with equality exactly at r=5. " +
                "Thus the constant is attained at the endpoint of this range."),
            Node("mixed_tail_bound", "A cardinality-sensitive mixed budget", MixedBound(),
                "For r>=131 and at most forty-two denominators q-1>=2r(r+2), the mass " +
                "is at most card(Q)/(2(r+2)), and this is at most 21/133. The first " +
                "bound retains the actual number of terms, including the empty set."),
            Node("pure_prime_exponent_parity", "An exact parity criterion", Parity(),
                "When r is nonzero modulo 3 and q-1=2^a r^b, avoidance of 3 by q is " +
                "equivalent to the stated parity alternatives. Neither q nor r needs " +
                "to be prime. Exponents zero are included. If r is 1 modulo 3, a must " +
                "be even; if r is 2 modulo 3, a and b must have the same parity."),
            Node("pure_prime_tail_budget", "A strict pure-family mass bound", Pure(),
                "For an odd r>=5 not divisible by 3, a finite prime family with " +
                "q-1=2^a r^b and b>0 has mass strictly below the parity budget. " +
                "The same budget is at most 55/72. If r is 1 modulo 3, the mass is " +
                "strictly below the smaller budget r/(3(r-1)). The base r need not be prime."),
            Node("large_support_tail_of_dichotomy", "Combining pure and mixed families",
                Dichotomy(),
                "For an odd r>=131 not divisible by 3, at most forty-two primes whose " +
                "predecessors are either pure or at least 2r(r+2) have mass strictly " +
                "below the sum of the pure budget and card(M)/(2(r+2)), where M is " +
                "the non-pure subfamily. When r is 1 modulo 3, the pure budget improves " +
                "to r/(3(r-1)). Replacing card(M) by 42 gives a uniform bound. The mass " +
                "bound is the strict inequality 1261/1368<1."))));


    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-tailfamily-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula PairSet() => Call("Finset", Call("Prod", Nat(), Nat()));
    private static Formula Term(Formula r, Formula first, Formula second) =>
        Div(r, Mul(Pow(D(2), first), Pow(r, second)));
    private static Formula ParityBudget()
    {
        var r = V("r"); var a = Call("fst", V("z")); var b = Call("snd", V("z"));
        var odd = Sum("z", V("S"),
            Term(r, Add(Mul(D(2), a), D(1)), Add(Mul(D(2), b), D(1))));
        var even = Sum("z", V("T"),
            Term(r, Add(Mul(D(2), a), D(2)), Add(Mul(D(2), b), D(2))));
        return All("S", PairSet(), All("T", PairSet(), All("r", Rat(),
            Imp(Lt(D(1), r), Lt(Add(odd, even), Budget(r))))));
    }
    private static Formula EvenBudget()
    {
        var r = V("r"); var a = Call("fst", V("z")); var b = Call("snd", V("z"));
        var mass = Sum("z", V("S"),
            Term(r, Add(Mul(D(2), a), D(2)), Add(b, D(1))));
        return All("S", PairSet(), All("r", Rat(), Imp(Lt(D(1), r),
            Lt(mass, Div(r, Mul(D(3), Sub(r, D(1))))))));
    }
    private static Formula PureBound()
    {
        var r = V("r"); var c = Div(D(5,5), D(7,2));
        return All("r", Rat(), Imp(Le(D(5), r), And(Le(Budget(r), c),
            new Formula.Logic(Eq(Budget(r), c), FormulaLogicOperator.Iff, Eq(r, D(5))))));
    }
    private static Formula MixedBound()
    {
        var q = V("q"); var r = V("r"); var s = V("Q");
        var denominator = Mul(D(2), Mul(r, Add(r, D(2))));
        var large = All("q", Nat(), Imp(Mem(q, s), Le(denominator, Sub(q, D(1)))));
        var actual = Div(Call("card", s), Mul(D(2), Add(r, D(2))));
        var mass = Sum("q", s, Div(r, Sub(q, D(1))));
        return All("Q", SetNat(), All("r", Nat(), Imp(Le(D(1,3,1), r),
            Imp(Le(Call("card", s), D(4,2)), Imp(large,
                And(Le(mass, actual), Le(actual, Div(D(2,1), D(1,3,3)))))))));
    }
    private static Formula Mod(Formula a, Formula b) => Call("mod", a, b);
    private static Formula Parity()
    {
        var r = V("r"); var q = V("q"); var a = V("a"); var b = V("b");
        var first = And(Eq(Mod(r, D(3)), D(1)), Eq(Mod(a, D(2)), D(0)));
        var second = And(Eq(Mod(r, D(3)), D(2)), Eq(Mod(a, D(2)), Mod(b, D(2))));
        var alternatives = new Formula.Logic(first, FormulaLogicOperator.Or, second);
        var result = new Formula.Logic(Ne(Mod(q, D(3)), D(0)),
            FormulaLogicOperator.Iff, alternatives);
        return All("r", Nat(), All("q", Nat(), All("a", Nat(), All("b", Nat(),
            Imp(Ne(Mod(r, D(3)), D(0)),
                Imp(Eq(Sub(q, D(1)), Mul(Pow(D(2), a), Pow(r, b))), result))))));
    }
    private static Formula Budget(Formula r) =>
        Div(Mul(r, Add(Mul(D(2), r), D(1))), Mul(D(3), Sub(Pow(r, D(2)), D(1))));
    private static Formula PrimeFamily(Formula s) =>
        All("q", Nat(), Imp(Mem(V("q"), s), Call("Prime", V("q"))));
    private static Formula Form(Formula q, Formula r) => Ex("a", Nat(), Ex("b", Nat(),
        And(Lt(D(0), V("b")), Eq(Sub(q, D(1)), Mul(Pow(D(2), V("a")), Pow(r, V("b")))))));
    private static Formula Mass(Formula s, Formula r) => Sum("q", s, Div(r, Sub(V("q"), D(1))));
    private static Formula Pure()
    {
        var s = V("Q"); var r = V("r");
        var form = All("q", Nat(), Imp(Mem(V("q"), s), Form(V("q"), r)));
        var branch = Imp(Eq(Mod(r, D(3)), D(1)),
            Lt(Mass(s, r), Div(r, Mul(D(3), Sub(r, D(1))))));
        var conclusion = And(Lt(Mass(s, r), Budget(r)),
            And(Le(Budget(r), Div(D(5,5), D(7,2))), branch));
        return All("Q", SetNat(), All("r", Nat(), Imp(Call("Odd", r),
            Imp(Ne(Call("mod", r, D(3)), D(0)), Imp(Le(D(5), r),
                Imp(PrimeFamily(s), Imp(form, conclusion)))))));
    }
    private static Formula Dichotomy()
    {
        var s = V("Q"); var r = V("r"); var q = V("q");
        var mixed = Le(Mul(D(2), Mul(r, Add(r, D(2)))), Sub(q, D(1)));
        var form = All("q", Nat(), Imp(Mem(q, s),
            new Formula.Logic(Form(q, r), FormulaLogicOperator.Or, mixed)));
        var total = Add(Budget(r), Div(D(4,2), Mul(D(2), Add(r, D(2)))));
        var m = Seq(OpenBrace, q, Sp, InMacro, Sp, s, Sp, Mid, Sp,
            Neg, Sp, Form(q, r), CloseBrace);
        var actual = Div(Call("card", m), Mul(D(2), Add(r, D(2))));
        var branch = Imp(Eq(Mod(r, D(3)), D(1)),
            Lt(Mass(s, r), Add(Div(r, Mul(D(3), Sub(r, D(1)))), actual)));
        var conclusion = And(Lt(Mass(s, r), total),
            And(Lt(Mass(s, r), Div(D(1,2,6,1), D(1,3,6,8))),
                And(Lt(Mass(s, r), Add(Budget(r), actual)), branch)));
        return All("Q", SetNat(), All("r", Nat(), Imp(Call("Odd", r),
            Imp(Ne(Call("mod", r, D(3)), D(0)), Imp(Le(D(1,3,1), r),
                Imp(Le(Call("card", s), D(4,2)), Imp(PrimeFamily(s),
                    Imp(form, conclusion))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula SetNat() => Call("Finset", Nat());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
