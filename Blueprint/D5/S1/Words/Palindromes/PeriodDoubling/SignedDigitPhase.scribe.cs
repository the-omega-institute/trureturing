using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SignedDigitPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The last nonzero signed coefficient gives the literal negative phase.", H("Signed Tail Phase"), Blocks(
        Describe.Lean(DescribeId.Create("pd-signeddigitphase-signed-digits-negative-phase"),
            DeclarationHandle.Create(Prefix + "signed_digits_negative_phase"), H("Dominance of the highest signed coefficient"),
            StatementSource.FromAuthor(PhaseFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The finite signed binary list is read least significant first. Every coefficient is minus one, zero or plus one. Its highest nonzero digit dominates all lower positions, so 2T minus the Boolean parity is negative exactly when the last nonzero sign is negative, or when the tail is empty and the parity is one. Nonadjacency is unnecessary. The empty list and absent last element use default zero. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Seq(Open, a, Sp, Bang, Eq, Sp, b, Close);

    private static Formula LastOption(Formula xs) =>
        Ite(Eqn(xs, ListNil()), Ty("none"), Call("some",
            new Formula.Apply(Seq(Operatorname, Grp(V("List"), Dot, V("getLast"))), [xs])));
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);


    private static Formula PhaseFormula()
    {
        var d=V("ds");
        var coeff=All("z",Z(),Imp(Mem(V("z"),d),new Formula.Logic(Eqn(V("z"),NegF(D(1))),FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(V("z"),D(0)),FormulaLogicOperator.Or,Eqn(V("z"),D(1))))));
        var value=Call("foldr",Seq(LambdaLower,Sp,V("z"),Colon,Z(),Sp,V("x"),Colon,Z(),Sp,Mapsto,Sp,
            Add(V("z"),Mul(D(2),V("x")))),D(0),d);
        var nz=Call("filter",Lam("z",Z(),BooleanNe(V("z"), D(0))),d);
        var phase=LtF(Sub(Mul(D(2),value),Cast(Call("toNat",V("delta")),Z())),D(0));
        var sign=new Formula.Logic(LtF(Call("getD",LastOption(nz),D(0)),D(0)),FormulaLogicOperator.Or,
            And(Eqn(nz,ListNil()),Eqn(V("delta"),Ty("true"))));
        return Disp(All("ds",ListOf(Z()),All("delta",Ty("Bool"),Imp(coeff,IffF(phase,sign)))));
    }
}
