using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelTailFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least odd predecessor prime controls the tail",
        H("The least odd predecessor prime controls the tail"), Blocks(
            Node("large_support_tail", "A strict mass bound from least-prime control", Tail(),
                "Let r>=131 be prime and let Q contain at most forty-two primes q. " +
                "Assume r divides every q-1 and no odd prime divisor of any q-1 is " +
                "smaller than r. Then the total mass r/(q-1) is strictly less than " +
                "the pure geometric budget plus card(M)/(2(r+2)), where M consists of " +
                "the non-pure predecessors. If r is 1 modulo 3 the pure budget is " +
                "r/(3(r-1)). The bound with 42 in place of card(M) also holds, as does " +
                "the strict bound 1261/1368. Factoring q-1 splits it into a pure power family " +
                "and a family containing a second odd prime at least r+2."))));


    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-tailfactorization-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Tail()
    {
        var q = V("q"); var r = V("r"); var s = V("s"); var set = V("Q");
        var primes = All("q", Nat(), Imp(Mem(q, set), Call("Prime", q)));
        var divides = All("q", Nat(), Imp(Mem(q, set), Dvd(r, Sub(q, D(1)))));
        var least = All("q", Nat(), Imp(Mem(q, set), All("s", Nat(),
            Imp(Call("Prime", s), Imp(Ne(s, D(2)),
                Imp(Dvd(s, Sub(q, D(1))), Le(r, s)))))));
        var mass = Sum("q", set, Div(r, Sub(q, D(1))));
        var pure = Div(Mul(r, Add(Mul(D(2), r), D(1))),
            Mul(D(3), Sub(Pow(r, D(2)), D(1))));
        var total = Add(pure, Div(D(4,2), Mul(D(2), Add(r, D(2)))));
        var form = Ex("a", Nat(), Ex("b", Nat(), And(Lt(D(0), V("b")),
            Eq(Sub(q, D(1)), Mul(Pow(D(2), V("a")), Pow(r, V("b")))))));
        var m = Seq(OpenBrace, q, Sp, InMacro, Sp, set, Sp, Mid, Sp, Neg, Sp,
            form, CloseBrace);
        var actual = Div(Call("card", m), Mul(D(2), Add(r, D(2))));
        var branch = Imp(Eq(Call("mod", r, D(3)), D(1)),
            Lt(mass, Add(Div(r, Mul(D(3), Sub(r, D(1)))), actual)));
        var conclusion = And(Lt(mass, total),
            And(Lt(mass, Div(D(1,2,6,1), D(1,3,6,8))),
                And(Lt(mass, Add(pure, actual)), branch)));
        return All("Q", SetNat(), All("r", Nat(), Imp(Call("Prime", r),
            Imp(Le(D(1,3,1), r), Imp(Le(Call("card", set), D(4,2)),
                Imp(primes, Imp(divides, Imp(least, conclusion))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
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
    private static Formula Dvd(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Divides, b);
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
