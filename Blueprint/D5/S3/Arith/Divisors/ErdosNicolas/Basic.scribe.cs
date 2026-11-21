using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/Basic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal divisor differences and the original claim", H("Reciprocal divisor differences and the original claim"), Blocks(
            Node("pairSum", "Unordered reciprocal gaps", PairFormula(),
                "Each unordered pair of distinct natural points is counted once. Subtraction is natural subtraction, and reciprocals and sums lie in the rationals. The conditional excludes all zero gaps.", true),
            Node("hHat", "The divisor difference sum", All("n", Nat(),
                Eq(Call("Hhat", V("n")), Call("pairSum", Call("divisors", V("n"))))),
                "On p. 390 of the cited source, the positive divisors are ordered d₁<⋯<dτ(n), and Ĥ(n) is the sum of 1/(dⱼ−dᵢ) over i<j. Nat.divisors gives the same finite set for positive n. Its value at zero is the empty set, outside the conjecture's range.", true, true),
            Node("hHat_prime_pow_le", "The prime-power bound",
                All("p", Nat(), All("a", Nat(), Imp(Call("Prime", V("p")),
                    Le(Call("Hhat", new Formula.Power(V("p"), V("a"))), V("a"))))),
                "Each positive-exponent row contributes at most one, so the reciprocal gap sum is at most the exponent. This is one less than the number of divisors of the prime power."),
            Node("ErdosNicolasClaim", "The published conjecture", Eq(V("ErdosNicolasClaim"), Claim()),
                "Page 390, verbatim: “We conjecture that for n > 5040, we have Ĥ(n) < τ(n).” The quantifier is over every natural n above 5040, with no restriction on its prime exponents or divisor count.", true, true))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false, bool literature = false) => Describe.Lean(
        DescribeId.Create("erdosnicolas-basic-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula PairFormula() => All("S", SetNat(),
        Eq(Call("pairSum", V("S")), SumOver("d", V("S"), SumOver("e", V("S"),
            Call("ite", Lt(V("d"), V("e")), Div(D(1), Sub(V("e"), V("d"))), D(0))))));
    private static Formula Claim() => All("n", Nat(),
        Imp(Lt(D(5,0,4,0), V("n")), Lt(Call("Hhat", V("n")), Card(Call("divisors", V("n"))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp,
            Seq(Open, body, Close));
    private static Formula SetNat() => Call("Finset", Nat());
    private static Formula Card(Formula set) => Call("card", set);
}
