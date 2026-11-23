using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorStripDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing bounded prime powers", H("Removing bounded prime powers"), Blocks(
            Node("strip_spec", "Repeated division removes all occurrences", Spec(),
                "Nondivisibility by p^(k+1) is equivalent to the following complete stripping data: " +
                "the result is positive and at most m, " +
                "is indivisible by p, and multiplying it by a suitable p-power recovers m. " +
                "The recovered exponent is at most k; zero divisors are included. Without the " +
                "fuel condition, p=2, m=2 and k=0 leave a factor of p in the result."),
            Node("strip_factored_iff", "Removing one allowed prime", Factored(),
                "For p prime or at most one, assume p is at most one, belongs to s, m is zero, or p^(k+1) does not divide m. " +
                "Zero and one leave the input and its prime support unchanged. The stripped result has " +
                "prime support in s exactly when m has support in s union {p}. The " +
                "statement does not require p to be absent from s. Composite generators cannot be admitted in general: " +
                "stripping 6 from 6 can return 1 although its prime support is not contained in {6}. " +
                "For prime p absent from s, an unremoved p-factor prevents membership on the left."),
            Node("isSmooth_iff", "The Boolean support test", Smooth(),
                "For a list of primes, zeros and ones, assume m is zero or no listed prime p has p^65 dividing m. " +
                "The smoothness test succeeds exactly when m is nonzero and all its prime " +
                "factors occur in the list. Neither ordering nor absence of repeated primes " +
                "is required. The primewise bound makes 64 divisions sufficient. Without it, " +
                "the list [2] and m=2^65 leave the test false despite the permitted support. " +
                "Generators above one must be prime; generators such as 6 can hide other prime factors."))));

    private static Formula Fuel(Formula p, Formula k, Formula m) =>
        Seq(Neg, Sp, Open, Dvd(Pow(p, Call("add", k, D(1))), m), Close);

    private static Formula Spec()
    {
        var p = V("p"); var m = V("m"); var k = V("k");
        var t = Call("strip", k, p, m);
        var power = Exists("e", Nat(), And(Le(V("e"), k),
            Eq(m, Mul(Pow(p, V("e")), t))));
        var result = And(Lt(D(0), t), And(Le(t, m),
            And(Seq(Neg, Sp, Open, Dvd(p, t), Close), power)));
        return All("p", Nat(), All("m", Nat(), All("k", Nat(),
            new Formula.Logic(Fuel(p, k, m), FormulaLogicOperator.Iff, result))));
    }

    private static Formula Factored()
    {
        var p = V("p"); var m = V("m"); var k = V("k"); var s = V("s");
        var fuel = new Formula.Logic(Le(p, D(1)), FormulaLogicOperator.Or,
            new Formula.Logic(Mem(p, s), FormulaLogicOperator.Or,
                new Formula.Logic(Eq(m, D(0)), FormulaLogicOperator.Or, Fuel(p, k, m))));
        var support = new Formula.Logic(
            Mem(Call("strip", k, p, m), Call("factoredNumbers", s)),
            FormulaLogicOperator.Iff,
            Mem(m, Call("factoredNumbers", Call("insert", p, s))));
        return All("p", Nat(), All("m", Nat(), All("k", Nat(),
            All("s", Call("Finset", Nat()), Imp(new Formula.Logic(Call("Prime", p),
                FormulaLogicOperator.Or, Le(p, D(1))), Imp(fuel, support))))));
    }

    private static Formula Smooth() =>
        All("l", Call("List", Nat()), All("m", Nat(),
            Imp(All("p", Nat(), Imp(Mem(V("p"), V("l")),
                new Formula.Logic(Call("Prime", V("p")), FormulaLogicOperator.Or, Le(V("p"), D(1))))),
                Imp(new Formula.Logic(Eq(V("m"), D(0)), FormulaLogicOperator.Or,
                    All("p", Nat(), Imp(Mem(V("p"), V("l")), Imp(Call("Prime", V("p")),
                        Seq(Neg, Sp, Open, Dvd(Pow(V("p"), D(6, 5)), V("m")), Close))))),
                    new Formula.Logic(Eq(Call("isSmooth", V("l"), V("m")), Call("true")),
                        FormulaLogicOperator.Iff,
                        Mem(V("m"), Call("factoredNumbers", Call("toFinset", V("l")))))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("smooth-predecessor-" +
            name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
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
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
