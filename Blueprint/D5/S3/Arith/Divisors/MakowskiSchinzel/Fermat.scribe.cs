using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelFermatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fermat products and power-of-two totients",
        H("Fermat products and power-of-two totients"), Blocks(
            Node("fermat_product_bound", "An arbitrary finite set of Fermat indices",
                FermatBound(),
                "For every finite set I of nonnegative indices, the product of the Fermat " +
                "numbers plus 1 is at most 2 raised to one plus the sum of their powers " +
                "of 2. Equality holds exactly for I=range(card(I)). No primality or " +
                "upper bound on " +
                "the indices is assumed."),
            Node("odd_le_sigma_totient_of_two_pow", "The power-of-two totient case",
                All("n", Nat(), All("E", Nat(), Imp(Call("Odd", V("n")),
                    Imp(Eq(Call("totient", V("n")), Pow(D(2), V("E"))),
                        Le(V("n"), Call("sigma", D(1), Call("totient", V("n")))))))),
                "An odd integer with power-of-two totient is squarefree and is a product " +
                "of distinct Fermat primes. The product estimate proves n<=sigma(phi(n)). " +
                "The case n=1 is included. Oddness is necessary for this stronger " +
                "inequality: n=2 has totient 1 and sigma(1)=1. No assertion that all Fermat " +
                "primes are known is needed."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-fermat-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula FermatBound()
    {
        var set = V("I");
        var left = Add(Prod("a", set, Call("fermatNumber", V("a"))), D(1));
        var right = Pow(D(2), Add(Sum("a", set, Pow(D(2), V("a"))), D(1)));
        var equality = new Formula.Logic(Eq(left, right), FormulaLogicOperator.Iff,
            Eq(set, Call("range", Call("card", set))));
        return All("I", SetNat(), And(Le(left, right), equality));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula SetNat() => Call("Finset", Nat());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
