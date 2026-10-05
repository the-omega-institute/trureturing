using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class OddPalindromeRadiusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every scale and every positive center has a complete reflection test.", H("Exact Odd-Palindrome Radii"), Blocks(
        Describe.Lean(DescribeId.Create("pd-oddpalindromeradius-odd-palindrome-radius"),
            DeclarationHandle.Create(Prefix + "odd_palindrome_radius"), H("The complete positive-center radius law"),
            StatementSource.FromAuthor(RadiusFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The center is the positive one-based index 2^r u, with odd u. The tested radius is strictly below the center, so every left index remains positive. For u=1 all available reflections agree. Otherwise the first disagreement is at q=2^r when the maximum adjacent valuation is even, and at 3q when it is odd. The word uses zero-based indexing, hence the subtraction of one from both positive endpoints. Natural subtraction is truncated, and mod is natural remainder."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula RadiusFormula()
    {
        var q = Pow(D(2), V("r"));
        var center = Mul(q, V("u"));
        var window = Call("ofFn", Lam("i", Call("Fin", Add(Mul(D(2), V("R")), D(1))),
            Call("upd", Add(Call("NatSub", Call("NatSub", center, V("R")), D(1)), Call("val", V("i"))))));
        var palindrome = Call("Palindrome", window);
        var s = Call("max", Call("padicValNat", D(2), Call("NatSub", V("u"), D(1))),
            Call("padicValNat", D(2), Add(V("u"), D(1))));
        var radius = Ite(Eqn(V("u"), D(1)), q,
            Ite(Eqn(Call("mod", s, D(2)), D(0)), q, Mul(D(3), q)));
        var body = Imp(And(Eqn(Call("mod", V("u"), D(2)), D(1)), LtF(V("R"), center)),
            IffF(palindrome, LtF(V("R"), radius)));
        return Disp(All("r", N(), All("u", N(), All("R", N(), body))));
    }

}
