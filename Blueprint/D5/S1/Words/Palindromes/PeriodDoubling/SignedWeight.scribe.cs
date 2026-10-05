using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SignedWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal minimum over signed-power representations satisfies exact scaling and recurrences.", H("Signed Binary Weight"), Blocks(
        Describe.Lean(DescribeId.Create("pd-signedweight-signedweight"),
            DeclarationHandle.Create(Prefix + "signedWeight"), H("Minimum signed-power weight"),
            StatementSource.FromAuthor(WeightFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A representation is a finite list of pairs consisting of a Boolean sign and a natural exponent. A true sign contributes the positive power; a false sign contributes the negative power. Repetitions are permitted. The natural infimum is the minimum number of terms summing to the integer x."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-signedweight-signed-weight-arithmetic"),
            DeclarationHandle.Create(Prefix + "signed_weight_arithmetic"), H("Exact arithmetic of the minimum"),
            StatementSource.FromAuthor(ArithmeticFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Optimal signed representations exist for every integer. Scaling removes a zero low digit. An odd integer has a positive or negative unit term, giving the exact two-branch recurrence. The argument constructs optimal lists and bounds every signed representation, including repetitions."))), DescribeRole.Theorem))));

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


    private static Formula WeightFormula()
    {
        var term = Lam("t", Product(Ty("Bool"), N()), Ite(Call("fst", V("t")),
            Pow(Cast(D(2), Z()), Call("snd", V("t"))),
            NegF(Pow(Cast(D(2), Z()), Call("snd", V("t"))))));
        var representation = Ex("l", ListOf(Product(Ty("Bool"), N())), And(
            Eqn(Call("length", V("l")), V("k")),
            Eqn(Call("sum", Call("map", term, V("l"))), V("x"))));
        var feasible = Seq(OpenBrace, V("k"), Colon, N(), Sp, Mid, Sp, representation, CloseBrace);
        return Disp(All("x", Z(), Eqn(Call("signedWeight", V("x")), Call("sInf", feasible))));
    }
    private static Formula W(Formula x) => Call("signedWeight", x);
    private static Formula ArithmeticFormula()
    {
        var neg = All("x", Z(), Eqn(W(NegF(V("x"))), W(V("x"))));
        var triangle = All("x", Z(), All("y", Z(),
            LeF(W(Add(V("x"), V("y"))), Add(W(V("x")), W(V("y"))))));
        var even = All("x", Z(), Eqn(W(Mul(D(2), V("x"))), W(V("x"))));
        var odd = All("x", Z(), Eqn(W(Add(Mul(D(2), V("x")), D(1))),
            Add(D(1), Call("min", W(V("x")), W(Add(V("x"), D(1)))))));
        return Disp(And(Eqn(W(D(0)), D(0)), Eqn(W(D(1)), D(1)), neg, triangle, even, odd));
    }

}
