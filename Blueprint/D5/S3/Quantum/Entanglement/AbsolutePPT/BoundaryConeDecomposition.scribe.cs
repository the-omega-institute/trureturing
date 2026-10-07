using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class BoundaryConeDecompositionDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula E => Arrow(Fin(Int(9)),R);
    private static Formula Good(Formula u) => Call("Good",u);
    private static Formula First() => Eq(Id("firstRow"),Seq(OpenBracket,Int(-1),Comma,Int(-2),Comma,Int(-3),Comma,Int(-2),Comma,Int(-1),Comma,Int(0),Comma,Int(1),Comma,Int(2),Comma,Int(3),CloseBracket));
    private static Formula Second() => Eq(Id("secondRow"),Seq(OpenBracket,Int(-1),Comma,Int(-1),Comma,Int(-1),Comma,Int(-1),Comma,Int(-1),Comma,Int(-1),Comma,Int(0),Comma,Int(1),Comma,Int(2),CloseBracket));
    private static Formula Rays() => Eq(Id("rays"),Seq(OpenBracket,
Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(3), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(1), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(1), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(3), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(3), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(0), Comma, Int(3), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(1), Comma, Int(0), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(1), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(3), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(0), Comma, Int(2), CloseBracket),
        Comma, Seq(OpenBracket, Int(0), Comma, Int(0), Comma, Int(0), Comma, Int(2), Comma, Int(0), Comma, Int(0), Comma, Int(1), Comma, Int(0), Comma, Int(1), CloseBracket),CloseBracket));
    private static Formula Statement()
    {
        var u=Id("u");var w=Id("w");var t=Id("t");var y=Id("y");var j=Id("j");
        var add=All("u",E,All("w",E,Imp(And(Good(u),Good(w)),Good(Add(u,w)))));
        var smul=All("t",R,All("u",E,Imp(And(Le(Int(0),t),Good(u)),Good(Mul(t,u)))));
        var hr=All("r",Fin(Int(33)),Good(Call("rays",Id("r"))));
        var hn=All("j",Fin(Int(9)),Le(Int(0),Call("y",j)));
        var hL=Le(Int(0),Sum("j",Fin(Int(9)),Mul(Call("y",j),Call("firstRow",j))));
        var hC=Le(Int(0),Sum("j",Fin(Int(9)),Mul(Call("y",j),Call("secondRow",j))));
        return All("Good",Arrow(Parenthesized(E),Id("Prop")),Imp(And(Good(Int(0)),add,smul,hr),
            All("y",E,Imp(And(hn,hL,hC),Good(y)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two boundary mass inequalities yield a finite conical decomposition into thirty-three explicitly listed rays.",
        H("Boundary cone decomposition"),Blocks(
            Desc("BoundaryConeDecomposition","firstRow","Bottom-six mass row",First(),"This is a function Fin 9 → ℝ, displayed in increasing Fin index order."),
            Desc("BoundaryConeDecomposition","secondRow","Bottom-three mass row",Second(),"This is a function Fin 9 → ℝ, displayed in increasing Fin index order."),
            Desc("BoundaryConeDecomposition","rays","Thirty-three boundary rays",Rays(),"The displayed table has type Fin 33 → (Fin 9 → ℝ). Every row has nine real entries; the outer index order is 0 through 32."),
            Desc("BoundaryConeDecomposition","finite_cone_transfer","Transfer from the ray table",Statement(),
                "A predicate containing zero and closed under addition and nonnegative scalar multiplication contains every nonnegative vector satisfying the two row inequalities whenever it contains all thirty-three rays. Two successive positive-negative mass decompositions express each admissible vector as a nonnegative combination of the listed rays.",DescribeRole.Theorem))));
}
