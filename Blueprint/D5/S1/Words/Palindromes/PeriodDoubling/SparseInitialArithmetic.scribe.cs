using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SparseInitialArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse Family Initial Arithmetic", H("Sparse Family Initial Arithmetic"), Blocks(
        Describe.Lean(DescribeId.Create("pd-sparseinitialarithmetic-sparse-initial-arithmetic"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/SparseInitialArithmetic.sparse_initial_arithmetic"),
            H("Sparse Family Initial Arithmetic"), StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For any natural a and b, the literal sparse-family integer is even. Its rounded-half signed weight is a+b, it belongs to class S, its signed-digit charge is 2a plus a mod 2 plus b, and its a upper positive digits form a marked prefix at position 2b+1 above the displayed nonnegative tail. The nonadjacent expansion is identified with the canonical triple-binary digits using uniqueness with zero padding. div and mod denote natural integer quotient and remainder; cast records natural-to-integer coercions."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);




    private static Formula MainFormula()
    {
        var a=V("a"); var b=V("b");
        var high=Call("sum",Call("range",a),Lam("i",N(),Pow(D(2),Add(Add(Mul(D(2),b),D(2)),Mul(D(3),V("i"))))));
        var low=Call("sum",Call("range",b),Lam("j",N(),Pow(D(2),Add(Mul(D(2),V("j")),D(1)))));
        var n=Add(high,low);
        var tail=Cast(Call("sum",Call("range",b),Lam("k",N(),Pow(D(2),Mul(D(2),V("k"))))),Z());
        var body=And(Eqn(Call("mod",n,D(2)),D(0)),Eqn(Call("signedWeight",Cast(Call("div",Add(n,D(1)),D(2)),Z())),Add(a,b)),Call("classS",n),Eqn(Call("signedDigitCharge",n),Add(Add(Mul(D(2),a),Call("mod",a,D(2))),b)),Call("markedPrefix",n,a,Add(Mul(D(2),b),D(1)),tail));
        return Disp(All("a",N(),All("b",N(),body)));
    }
}
