using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class TightFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/TightFactorization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed-weight lower bound is attained precisely when the prefix can be reduced to zero through tight palindrome cuts.", H("Tight Palindromic Factorizations"), Blocks(
        Describe.Lean(DescribeId.Create("pd-tightfactorization-tight-factorization-iff"),
            DeclarationHandle.Create(Prefix + "tight_factorization_iff"), H("Equality is equivalent to a tight cut path"),
            StatementSource.FromAuthor(TightFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The list starts at the prefix endpoint n and ends at zero. Each successive pair decreases the endpoint, removes a nonempty palindromic suffix, and lowers the signed weight of the rounded half by exactly one. An optimal factorization supplies such a path when equality holds; conversely, a tight path constructs a factorization meeting the lower bound. NatSub denotes truncated natural subtraction and NatDiv denotes natural integer division."))), DescribeRole.Theorem))));

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


    private static Formula RoundedWeight(Formula n) => Call("signedWeight", Cast(Call("NatDiv", Add(n, D(1)), D(2)), Z()));
    private static Formula TightFormula()
    {
        var n = V("n"); var cuts = V("cuts"); var s = V("s"); var t = V("t");
        var prefix = Call("ofFn", Lam("i", Call("Fin", n), Call("upd", Call("val", V("i")))));
        var window = Call("ofFn", Lam("i", Call("Fin", Call("NatSub", s, t)),
            Call("upd", Add(t, Call("val", V("i"))))));
        var rel = Lam("s", N(), Lam("t", N(), And(LtF(t, s), Call("Palindrome", window),
            Eqn(RoundedWeight(s), Add(RoundedWeight(t), D(1))))));
        var path = Call("cons", n, cuts);
        return Disp(All("n", N(), IffF(Eqn(Call("PL", prefix), RoundedWeight(n)),
            Ex("cuts", ListOf(N()), And(Eqn(Call("getLastOpt", path), Call("some", D(0))),
                Call("IsChain", path, rel))))));
    }
}
