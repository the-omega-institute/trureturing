using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelPrimeDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime sources in a minimal counterexample",
        H("Prime sources in a minimal counterexample"), Blocks(
            Describe.Lean(
                DescribeId.Create("makowski-schinzel-abundancy-prime-power-product"),
                DeclarationHandle.Create(Prefix + "abundancy_prime_power_product"),
                H("Abundancy of distinct prime powers"),
                StatementSource.FromAuthor(Disp(PrimePowerProduct())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a finite set of bases and arbitrary nonnegative exponents, the " +
                    "abundancy of their product equals the product of the finite reciprocal " +
                    "geometric factors, provided every base with nonzero exponent is prime. " +
                    "Zero exponents impose no primality condition and contribute one. " +
                    "Primality cannot be omitted: the singleton base 1 at exponent 1 has " +
                    "abundancy 1 but geometric factor 2. The identity includes the empty set."))),
                DescribeRole.Theorem),
            Node("primeSources", "Sources of a totient prime", Sources(),
                "The sources are the prime divisors q of n for which r divides q-1.", true),
            Node("prime_deletion_necessary", "The prime-source deletion obstruction",
                Deletion(),
                "Assume a nonzero m has ratio below 1, while every strictly smaller " +
                "divisor has ratio at least 1. For each prime r dividing its totient, " +
                "the product of q/(q-1) over all sources strictly exceeds the geometric " +
                "sum through their number. Minimality forces m to be squarefree. " +
                "Deleting all sources leaves a proper divisor whose totient is coprime " +
                "to r, and each deleted source contributes a factor of r to phi(m)."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-primedeletion-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Sources() => All("n", Nat(), All("r", Nat(),
        All("q", Nat(), new Formula.Logic(
            Mem(V("q"), Call("primeSources", V("n"), V("r"))),
            FormulaLogicOperator.Iff,
            And(Mem(V("q"), Call("primeFactors", V("n"))),
                Dvd(V("r"), Sub(V("q"), D(1))))))));
    private static Formula Deletion()
    {
        var m = V("m"); var r = V("r"); var sources = Call("primeSources", m, r);
        var minimal = All("d", Nat(), Imp(Dvd(V("d"), m), Imp(Lt(V("d"), m),
            Le(D(1), Call("alpha", V("d"))))));
        var result = Lt(Call("geom", r, Call("card", sources)),
            Prod("q", sources, Div(V("q"), Sub(V("q"), D(1)))));
        return All("m", Nat(), All("r", Nat(), Imp(Ne(m, D(0)),
            Imp(Call("Prime", r), Imp(Dvd(r, Call("totient", m)),
                Imp(Lt(Call("alpha", m), D(1)), Imp(minimal, result)))))));
    }

    private static Formula PrimePowerProduct()
    {
        var s = V("S"); var e = V("e"); var p = V("p");
        var ep = Call("e", p);
        var prime = All("p", Nat(), Imp(Mem(p, s), Imp(Ne(ep, D(0)), Call("Prime", p))));
        var left = Call("abundancyIndex", Prod("p", s, new Formula.Power(p, ep)));
        var right = Prod("p", s, Call("geom", p, ep));
        return All("S", Call("Finset", Nat()),
            All("e", new Formula.TypeArrow(Nat(), Nat()), Imp(prime,
                new Formula.Relation(left, FormulaRelationOperator.Equal, right))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
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
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
