using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class CanonicalSignedDigitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse signed binary expansions are uniquely determined by their value at any fixed digit length.", H("Uniqueness of Nonadjacent Signed Digits"), Blocks(
        Describe.Lean(DescribeId.Create("pd-canonicalsigneddigits-nonadjacent-digits-unique"),
            DeclarationHandle.Create(Prefix + "nonadjacent_digits_unique"), H("Equal values force identical digit lists"),
            StatementSource.FromAuthor(UniqueFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/menezesvanoorschotvanstone1996sparse")),
            Blocks(Paragraph(Text("Fact 14.124(i), page 628: \"Every integer e has a unique sparse signed-digit representation.\" The lists here are ordered from the least significant digit upward, have the same length, and retain zero padding. Each digit belongs to minus one, zero, or one, and every adjacent pair has a zero. Equal radix-two values force equal low digits by parity and modulo-four rigidity; induction then identifies the complete lists."))), DescribeRole.Theorem))));

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


    private static Formula Coefficients(Formula digits) => All("z", Z(), Imp(Mem(V("z"), digits),
        new Formula.Logic(Eqn(V("z"), NegF(D(1))), FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(V("z"), D(0)), FormulaLogicOperator.Or, Eqn(V("z"), D(1))))));
    private static Formula Sparse(Formula digits) => Call("IsChain", digits, Lam("a", Z(), Lam("b", Z(),
        new Formula.Logic(Eqn(V("a"), D(0)), FormulaLogicOperator.Or, Eqn(V("b"), D(0))))));
    private static Formula Value(Formula digits) => Call("foldr", Lam("z", Z(), Lam("x", Z(),
        Add(V("z"), Mul(D(2), V("x"))))), D(0), digits);
    private static Formula UniqueFormula()
    {
        var ds = V("digits"); var es = V("other");
        var assumptions = And(Coefficients(ds), Coefficients(es), Sparse(ds), Sparse(es),
            Eqn(Call("length", ds), Call("length", es)), Eqn(Value(ds), Value(es)));
        return Disp(All("digits", ListOf(Z()), All("other", ListOf(Z()), Imp(assumptions, Eqn(ds, es)))));
    }
}
