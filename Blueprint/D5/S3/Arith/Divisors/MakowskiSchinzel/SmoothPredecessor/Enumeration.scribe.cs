using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted enumeration of smooth multiples",
        H("Weighted enumeration of smooth multiples"), Blocks(
            Node("factoredMultiples", "Bounded multiples with prescribed quotient support",
                Multiples(), "The finite set contains the positive m at most X divisible " +
                "by c for which every prime divisor of m/c belongs to s. Membership in " +
                "factoredNumbers also requires the quotient to be nonzero.", true),
            Node("powSum_eq_sum_range", "The truncated power fold", PowerFold(),
                "Exactly when n is at most one, p is at least one, c is at most X, or f(0)=0, the recursive fold " +
                "sums f(c p^e) for exponents below n whose multiples are at most X. " +
                "For n at most one only the initial multiple is visited; otherwise the condition " +
                "prevents a later multiple from returning below X after the fold has stopped, " +
                "or gives zero weight to every returned zero multiple. " +
                "For n=2, p=0, X=0, c=1 and constant weight 1, the fold is zero but the sum is one."),
            Node("sum_factoredMultiples_insert", "Prime-power branch partition", Partition(),
                "The set factoredMultiples(s,X,c) contains the integers m from 1 through X " +
                "such that c divides m and m/c has every prime factor in s. For a prime p " +
                "outside s, the N power branches partition the corresponding set with p inserted " +
                "when c is zero or X < c p^N. This bound excludes all later exponents. " +
                "The unique factorization equivalence supplies both coverage and uniqueness. " +
                "Primality gives this decomposition; excluding p from s prevents overlapping " +
                "branches. Without the cutoff, a multiple requiring exponent N is omitted."),
            Node("smoothSum_eq_sum", "Correctness of the smooth fold", SmoothFold(),
                "For distinct primes, assume c is positive or w(0)=0, and either c=0 or X < c p^64 for every listed p. The smooth fold " +
                "is the weighted sum of bounded multiples whose quotient has prime support " +
                "in that list. The condition c <= X is needed only for the empty prime list, where " +
                "the fold returns w(c); it can be dropped when w(c)=0. The weights need not be multiplicative. Repeated " +
                "generators count some integers more than once. A zero start contributes zero " +
                "exactly when w(0)=0, since its set of positive multiples is empty. Each primewise cutoff ensures that no omitted exponent " +
                "contributes a bounded multiple."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false) =>
        Describe.Lean(DescribeId.Create("smooth-predecessor-enumeration-" +
            name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Multiples()
    {
        var s = V("s"); var x = V("X"); var c = V("c"); var m = V("m");
        Formula body = new Formula.Logic(Call("Mem", m, Call("factoredMultiples", s, x, c)),
            FormulaLogicOperator.Iff, And(Le(D(1), m), And(Le(m, x),
                And(Call("Divides", c, m),
                    Call("Mem", Call("natDiv", m, c), Call("factoredNumbers", s))))));
        body = All("m", Nat(), body);
        body = All("c", Nat(), body);
        body = All("X", Nat(), body);
        return All("s", Call("Finset", Nat()), body);
    }

    private static Formula PowerFold()
    {
        var n = V("n"); var f = V("f"); var p = V("p"); var x = V("X"); var c = V("c");
        var term = Mul(c, Pow(p, V("e")));
        Formula body = Eq(Call("powSum", n, f, p, x, c),
            Sum("e", Call("range", n), Call("ite", Le(term, x),
                new Formula.Apply(f, [term]), D(0))));
        body = new Formula.Logic(body, FormulaLogicOperator.Iff,
            new Formula.Logic(Le(n, D(1)), FormulaLogicOperator.Or,
                new Formula.Logic(Le(D(1), p), FormulaLogicOperator.Or,
                    new Formula.Logic(Le(c, x), FormulaLogicOperator.Or,
                        Eq(new Formula.Apply(f, [D(0)]), D(0))))));
        body = All("c", Nat(), body);
        body = All("X", Nat(), body);
        body = All("p", Nat(), body);
        body = All("f", Arrow(), body);
        return All("n", Nat(), body);
    }

    private static Formula Partition()
    {
        var n = V("N"); var w = V("w"); var s = V("s"); var p = V("p"); var x = V("X"); var c = V("c");
        Formula body = Eq(Sum("e", Call("range", n), Sum("m",
                Call("factoredMultiples", s, x, Mul(c, Pow(p, V("e")))),
                new Formula.Apply(w, [V("m")]))),
            Sum("m", Call("factoredMultiples", Call("insert", p, s), x, c),
                new Formula.Apply(w, [V("m")])));
        body = Imp(new Formula.Logic(Eq(c, D(0)), FormulaLogicOperator.Or,
            Lt(x, Mul(c, Pow(p, n)))), body);
        body = Imp(Call("NotMem", p, s), body);
        body = Imp(Call("Prime", p), body);
        body = All("c", Nat(), body);
        body = All("X", Nat(), body);
        body = All("p", Nat(), body);
        body = All("s", Call("Finset", Nat()), body);
        body = All("N", Nat(), body);
        return All("w", Arrow(), body);
    }

    private static Formula SmoothFold()
    {
        var w = V("w"); var ps = V("ps"); var x = V("X"); var c = V("c");
        var primes = All("p", Nat(), Imp(Call("Mem", V("p"), ps), Call("Prime", V("p"))));
        Formula body = Eq(Call("smoothSum", w, ps, x, c),
            Sum("m", Call("factoredMultiples", Call("toFinset", ps), x, c),
                new Formula.Apply(w, [V("m")])));
        body = Imp(new Formula.Logic(Eq(c, D(0)), FormulaLogicOperator.Or,
            All("p", Nat(), Imp(Call("Mem", V("p"), ps),
                Lt(x, Mul(c, Pow(V("p"), D(6,4))))))), body);
        body = Imp(Imp(Eq(ps, Call("nil")), new Formula.Logic(Le(c, x),
            FormulaLogicOperator.Or, Eq(new Formula.Apply(w, [c]), D(0)))), body);
        body = Imp(new Formula.Logic(Lt(D(0), c), FormulaLogicOperator.Or,
            Eq(new Formula.Apply(w, [D(0)]), D(0))), body);
        body = All("c", Nat(), body);
        body = All("X", Nat(), body);
        body = Imp(Call("Nodup", ps), body);
        body = Imp(primes, body);
        body = All("ps", Call("List", Nat()), body);
        return All("w", Arrow(), body);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Arrow() => new Formula.TypeArrow(Nat(), Nat());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, body);
}
