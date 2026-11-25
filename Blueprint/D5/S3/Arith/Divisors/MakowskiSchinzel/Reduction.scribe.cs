using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal counterexamples and radical monotonicity",
        H("Minimal counterexamples and radical monotonicity"), Blocks(
            Node("alpha", "The normalized ratio", All("n", Nat(),
                Eq(Call("alpha", V("n")),
                    Div(Call("sigma", D(1), Call("totient", V("n"))), V("n")))),
                "The ratio is rational. Division by zero gives alpha(0)=0.", true),
            Node("eta", "Distinct non-Fermat odd prime factors", All("n", Nat(),
                Eq(Call("eta", V("n")), Call("card", Call("nonFermatFactors", V("n"))))),
                "The finite support consists of primes q dividing n with q different from 2 " +
                "and q-1 not a power of 2. Multiplicity is discarded, and eta(0)=eta(1)=0.",
                true),
            Node("alpha_factorization", "The totient-product factorization", Factorization(),
                "For every natural n, alpha(n) is the abundancy index of its totient times " +
                "the product of 1-1/p over its distinct prime divisors. The zero case is " +
                "included. The abundancy index of a positive integer m is sigma(m)/m."),
            Node("alpha_radical_le", "The radical gives a lower ratio", All("n", Nat(),
                Imp(Ne(V("n"), D(0)), Le(Call("alpha", Call("radical", V("n"))),
                    Call("alpha", V("n"))))),
                "Passing to the radical preserves the prime support and decreases the " +
                "totient's abundancy index by divisibility. The result compares the " +
                "normalized ratios independently of the prime exponents. The nonzero condition " +
                "is necessary: radical(0)=1, alpha(1)=1 and alpha(0)=0."),
            Node("alpha_two_mul", "Adjoining the factor two", All("m", Nat(),
                Imp(Call("Odd", V("m")), Eq(Call("alpha", Mul(D(2), V("m"))),
                    Div(Call("alpha", V("m")), D(2))))),
                "For odd m, adjoining two preserves the totient and halves the " +
                "normalized sigma-totient ratio. The oddness premise cannot be dropped: at m=2 " +
                "the two sides are 3/4 and 1/4. The identity also holds at m=0."),
            Node("exists_minimal_odd_counterexample", "A squarefree minimal counterexample",
                Minimal(),
                "For a class P closed under divisors of odd members, an odd counterexample " +
                "yields an odd, " +
                "squarefree minimal counterexample in P. Every proper divisor has ratio " +
                "at least 1. Every smaller odd member of P also has ratio at least 1. " +
                "No closure condition is imposed on even members of P."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-reduction-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Factorization() => All("n", Nat(),
        Eq(Call("alpha", V("n")), Mul(Call("abundancyIndex", Call("totient", V("n"))),
            Prod("p", Call("primeFactors", V("n")), Sub(D(1), Div(D(1), V("p")))))));
    private static Formula Minimal()
    {
        var p = V("P"); var m = V("m"); var n = V("n");
        Formula Pred(Formula k) => new Formula.Apply(p, [k]);
        var closed = All("a", Nat(), All("b", Nat(), Imp(Call("Odd", V("b")),
            Imp(Dvd(V("a"), V("b")), Imp(Pred(V("b")), Pred(V("a")))))));
        var exists = Ex("n", Nat(), And(Call("Odd", n),
            And(Pred(n), Lt(Call("alpha", n), D(1)))));
        var proper = All("d", Nat(), Imp(Dvd(V("d"), m), Imp(Lt(V("d"), m),
            Le(D(1), Call("alpha", V("d"))))));
        var global = All("d", Nat(), Imp(Call("Odd", V("d")), Imp(Pred(V("d")),
            Imp(Lt(V("d"), m), Le(D(1), Call("alpha", V("d")))))));
        var result = Ex("m", Nat(), And(Call("Odd", m), And(Pred(m),
            And(Call("Squarefree", m), And(Lt(Call("alpha", m), D(1)), And(proper, global))))));
        return All("P", new Formula.TypeArrow(Nat(), V("Prop")),
            Imp(closed, Imp(exists, result)));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
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
    private static Formula Dvd(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
