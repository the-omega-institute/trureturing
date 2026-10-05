using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The f charges on accepted paths equal the signed-weight difference of the encoded rounded halves.", H("Arithmetic Meaning of the Base Transducer"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basearithmetic-base-path-signed-weight-difference"),
            DeclarationHandle.Create(Prefix + "base_path_signed_weight_difference"), H("Path charge is the exact signed-weight difference"),
            StatementSource.FromAuthor(ArithmeticFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The third and fourth edge coordinates encode successive binary digits, least significant first, above the endpoint's bit zero. Folding a + 2 x reconstructs the shifted integer. Source components 2 and 3 supply the fixed bit-zero parities, so adding them reconstructs the two rounded halves. The carry identities and the forced even remainder after a nonzero signed digit give the signed-weight change at each edge; path induction telescopes it. cast denotes the natural-to-integer embedding. This theorem identifies f weights and does not assert that all legal palindrome cuts have already been represented by accepted paths."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Entry(Formula s, int k) => Call("getD", OptionalIndex(s, new Formula.Number(k)), D(0));
    private static Formula ArithmeticFormula()
    {
        var automaton = Call("baseAutomaton", V("charge"));
        var a = V("a");
        var rawN = Call("foldr", Lam("a", Alphabet(), Lam("x", Z(),
            Add(Call("fst", Call("snd", Call("snd", a))), Mul(D(2), V("x"))))), D(0), V("xs"));
        var rawJ = Call("foldr", Lam("a", Alphabet(), Lam("x", Z(),
            Add(Call("snd", Call("snd", Call("snd", a))), Mul(D(2), V("x"))))), D(0), V("xs"));
        var state = Call("fst", Call("baseTable", Call("val", V("s"))));
        var cost = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp, Mapsto, Sp, Call("fst", a));
        var identity = Eqn(Call("pathCharge", cost, V("p")),
            Sub(Cast(Call("signedWeight", Add(rawN, Entry(state,2))), Z()),
                Cast(Call("signedWeight", Add(rawJ, Entry(state,3))), Z())));
        var body = All("p", Call("Path", automaton, V("s"), V("t"), V("xs")), identity);
        body = Imp(And(Mem(V("s"), Call("start", automaton)), Mem(V("t"), Call("accept", automaton))), body);
        return Disp(All("charge", Ty("Bool"), All("s", Call("Fin", D(1,4,9,2)),
            All("t", Call("Fin", D(1,4,9,2)), All("xs", ListOf(Alphabet()), body)))));
    }
}
