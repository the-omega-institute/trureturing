using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion products and reciprocal mass", H("Deletion products and reciprocal mass"), Blocks(
            Node("prod_one_add_le_geom", "A geometric majorant for a finite product",
                ProductBound(),
                "Nonnegative increments with total at most t have product of 1+x bounded " +
                "by the finite geometric sum through the size of the set. Equality holds " +
                "exactly when the set is empty, t=0, or the set is a singleton whose " +
                "increment equals t. Negative increments cannot be allowed uniformly: " +
                "x=-3 on a " +
                "two-element set and t=0 give product 4 and geometric sum 1."),
            Node("necessary_mass", "The strict necessary mass inequality", Mass(),
                "If a deletion product exceeds its geometric factor at a positive r, " +
                "the sum of r/(q-1) must exceed 1. This conclusion is strict. The deletion " +
                "inequality itself forces every q to exceed 1: q=0 or q=1 would make " +
                "the product zero. No separate denominator hypothesis is needed. " +
                "Positivity of r is necessary: r=0 and Q={2} give deletion product 2 " +
                "above geometric factor 1, but reciprocal mass 0."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-deletion-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula ProductBound()
    {
        var s = V("S"); var x = V("x"); var t = V("t");
        var positive = All("i", Nat(), Imp(Mem(V("i"), s), Le(D(0), Call("x", V("i")))));
        var total = Sum("i", s, Call("x", V("i")));
        var budget = Le(total, t);
        var product = Prod("i", s, Add(D(1), Call("x", V("i"))));
        var geometric = Sum("j", Call("range", Add(Call("card", s), D(1))), Pow(t, V("j")));
        var singleton = And(Eq(Call("card", s), D(1)), Eq(total, t));
        var cases = new Formula.Logic(Eq(Call("card", s), D(0)), FormulaLogicOperator.Or,
            new Formula.Logic(Eq(t, D(0)), FormulaLogicOperator.Or, singleton));
        var equality = new Formula.Logic(Eq(product, geometric), FormulaLogicOperator.Iff, cases);
        var result = And(Le(product, geometric), equality);
        return All("S", SetNat(), All("x", new Formula.TypeArrow(Nat(), Rat()),
            All("t", Rat(), Imp(positive, Imp(budget, result)))));
    }
    private static Formula Mass()
    {
        var r = V("r"); var q = V("q"); var s = V("Q");
        var deletion = Lt(Call("geom", r, Call("card", s)),
            Prod("q", s, Div(q, Sub(q, D(1)))));
        var mass = Lt(D(1), Sum("q", s, Div(r, Sub(q, D(1)))));
        return All("r", Nat(), Imp(Lt(D(0), r), All("Q", SetNat(),
            Imp(deletion, mass))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula SetNat() => Call("Finset", Nat());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
