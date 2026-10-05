using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PrefixArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/PrefixArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The f charges on accepted paths equal the signed-weight difference of the encoded rounded halves.", H("Arithmetic Meaning of the Marked-Prefix Product"), Blocks(
        Describe.Lean(DescribeId.Create("pd-prefixarithmetic-prefix-path-signed-weight-difference"),
            DeclarationHandle.Create(Prefix + "prefix_path_signed_weight_difference"), H("Path charge is the exact signed-weight difference"),
            StatementSource.FromAuthor(ArithmeticFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Both marker modes project to an accepted base path while retaining each f, q, n-bit, j-bit label. The encoded shifted endpoints and their source parities therefore have the stated signed-weight difference. cast denotes the natural-to-integer embedding and toNat converts an integer table index to a natural number. Recognition of legal cuts, marker configurations, and Q charges remains separate from this f-weight identity."))), DescribeRole.Theorem))));

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


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Entry(Formula s, int k) => Call("getD", Call("getElemOption", s, new Formula.Number(k)), D(0));
    private static Formula ArithmeticFormula()
    {
        var automaton = Call("prefixAutomaton", V("charge"));
        var a = V("a");
        var rawN = Call("foldr", Lam("a", Alphabet(), Lam("x", Z(),
            Add(Call("fst", Call("snd", Call("snd", a))), Mul(D(2), V("x"))))), D(0), V("xs"));
        var rawJ = Call("foldr", Lam("a", Alphabet(), Lam("x", Z(),
            Add(Call("snd", Call("snd", Call("snd", a))), Mul(D(2), V("x"))))), D(0), V("xs"));
        var state = Call("fst", Call("baseTable", Call("toNat", Entry(Call("fst", Call("prefixTable", Call("val", V("s")))), 0))));
        var cost = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(4,2,6,2)), CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, Call("Fin", D(4,2,6,2)), CloseBracket, Sp, Mapsto, Sp, Call("fst", a));
        var identity = Eqn(Call("pathCharge", cost, V("p")),
            Sub(Cast(Call("signedWeight", Add(rawN, Entry(state,2))), Z()),
                Cast(Call("signedWeight", Add(rawJ, Entry(state,3))), Z())));
        var body = All("p", Call("Path", automaton, V("s"), V("t"), V("xs")), identity);
        body = Imp(And(Mem(V("s"), Call("start", automaton)), Mem(V("t"), Call("accept", automaton))), body);
        return Disp(All("charge", Ty("Bool"), All("s", Call("Fin", D(4,2,6,2)),
            All("t", Call("Fin", D(4,2,6,2)), All("xs", ListOf(Alphabet()), body)))));
    }
}
