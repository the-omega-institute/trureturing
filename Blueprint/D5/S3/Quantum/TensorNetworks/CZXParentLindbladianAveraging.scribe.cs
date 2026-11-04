using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class CZXParentLindbladianAveragingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting coordinate averages on finite binary configurations.",
        H("CZX coordinate averaging"),
        Blocks(
            Node("avg", "The coordinate average", Avg(), "Avg is the noncommutative product of the commuting binary-coordinate averaging endomorphisms over a finite set of sites.", Repo),
            Node("avg_empty", "The empty average", AvgEmpty(), "The average over no coordinates is the identity endomorphism.", Repo, DescribeRole.Theorem),
            Node("avg_mul", "Multiplication of averages", AvgMul(), "Multiplying the averages over two finite site sets gives the average over their union, using idempotence and commutation of the coordinate averages.", Repo, DescribeRole.Theorem),
            Node("avg_commute", "Commutation of averages", AvgCommute(), "Averages over arbitrary finite site sets commute because every coordinate average commutes with every other one.", Repo, DescribeRole.Theorem),
            Node("avg_pair_apply", "A two-coordinate average", AvgPairApply(), "For distinct sites k and l, applying the average over their pair gives the four equally weighted updates of the two coordinates.", Repo, DescribeRole.Theorem),
            Node("avg_map", "Averages commute with linear maps", AvgMap(), "A complex-linear map can be moved through a coordinate average by map-additivity, map-scalar multiplication, and induction over the finite product.", Repo, DescribeRole.Theorem),
            Node("avg_univ", "The full coordinate average", AvgUniv(), "Averaging over every site gives the uniform average over all binary configurations, with normalization two to the power n.", Repo, DescribeRole.Theorem)
        ), []));

    private static AssessedProvenance Repo => AssessedProvenance.FromRepo();
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("czx-avg-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Local(string name) => Q(Prefix.Replace('/', '.') + name);

    private static Formula Q(string name)
    {
        var parts=name.Split('.'); var items=new List<Formula> { Operatorname, Grp(F.Id(parts[0])) };
        for (var i=1;i<parts.Length;i++) items.AddRange([Dot,Grp(F.Id(parts[i]))]);
        return Seq(items.ToArray());
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula T(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, T(F.Id(name), type), Comma, Sp, body);
    private static Formula Typeclass(string name, params Formula[] args) => Seq(OpenBracket, Call(name, args), CloseBracket);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a),b);
    private static Formula Inv(Formula a) => Pow(a,Seq(Minus,D(1)));
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar),Sp,Cdot,Sp,Parenthesized(value));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a),Parenthesized(b));
    private static Formula SumOver(Formula v, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum,Seq(v,Colon,Sp,domain)),Sp,body);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Nat() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Config(Formula n) => Arrow(Fin(n),Fin(D(2)));
    private static Formula FunctionSpace(Formula n, Formula V) => Arrow(Config(n),V);
    private static Formula Finset(Formula n) => Call("Finset",Fin(n));
    private static Formula Update(Formula x, Formula k, Formula b) => Call("Function.update",x,k,b);
    private static Formula AvgCall(Formula n, Formula s) => At(Local("avg"),n,s);
    private static Formula VBinders(Formula body) => Seq(Forall,Sp,T(F.Id("V"),F.Id("Type")),Comma,Sp,Typeclass("AddCommGroup",F.Id("V")),Comma,Sp,Typeclass("Module",Complex(),F.Id("V")),Comma,Sp,body);
    private static Formula WBinders(Formula body) => Seq(Forall,Sp,T(F.Id("V"),F.Id("Type")),Comma,Sp,Typeclass("AddCommGroup",F.Id("V")),Comma,Sp,Typeclass("Module",Complex(),F.Id("V")),Comma,Sp,Forall,Sp,T(F.Id("W"),F.Id("Type")),Comma,Sp,Typeclass("AddCommGroup",F.Id("W")),Comma,Sp,Typeclass("Module",Complex(),F.Id("W")),Comma,Sp,body);

    private static Formula Avg()
    {
        Formula n=F.Id("n"),s=F.Id("s"),k=F.Id("k"),V=F.Id("V");
        Formula action=Lam("f",FunctionSpace(n,V),Lam("x",Config(n),Smul(Inv(T(D(2),Complex())),SumOver(F.Id("b"),Fin(D(2)),At(F.Id("f"),Update(F.Id("x"),k,F.Id("b")))))));
        Formula product=Call("Finset.noncommProd",s,Lam("k",Fin(n),action));
        return VBinders(All("n",Nat(),All("s",Finset(n),Eqn(AvgCall(n,s),product))));
    }
    private static Formula AvgEmpty() { var n=F.Id("n"); return VBinders(All("n",Nat(),Eqn(AvgCall(n,Call("Finset.empty")),CastOne()))); }
    private static Formula AvgMul() { var n=F.Id("n"); var s=F.Id("s"); var t=F.Id("t"); var eq=Eqn(Mul(AvgCall(n,s),AvgCall(n,t)),AvgCall(n,Call("Finset.union",s,t))); return VBinders(All("n",Nat(),All("s",Finset(n),All("t",Finset(n),eq)))); }
    private static Formula AvgCommute() { var n=F.Id("n"); var s=F.Id("s"); var t=F.Id("t"); var eq=Call("Commute",AvgCall(n,s),AvgCall(n,t)); return VBinders(All("n",Nat(),All("s",Finset(n),All("t",Finset(n),eq)))); }
    private static Formula AvgPairApply()
    { var n=F.Id("n"); var k=F.Id("k"); var l=F.Id("l"); var f=F.Id("f"); var x=F.Id("x"); var set=Call("Finset.insert",k,Call("Finset.singleton",l)); var lhs=At(At(AvgCall(n,set),f),x); var updates=Update(Update(x,k,F.Id("b")),l,F.Id("c")); var inner=SumOver(F.Id("c"),Fin(D(2)),At(f,updates)); var sums=SumOver(F.Id("b"),Fin(D(2)),inner); var rhs=Smul(Inv(T(D(4),Complex())),sums); var eq=Eqn(lhs,rhs); var statement=All("n",Nat(),All("k",Fin(n),All("l",Fin(n),Imp(Ne(k,l),All("f",FunctionSpace(n,F.Id("V")),All("x",Config(n),eq)))))); return VBinders(statement); }
    private static Formula AvgMap()
    { var n=F.Id("n"); var s=F.Id("s"); var l=F.Id("l"); var f=F.Id("f"); var x=F.Id("x"); var lhs=At(l,At(At(AvgCall(n,s),f),x)); var mapped=Lam("y",Config(n),At(l,At(f,F.Id("y")))); var rhs=At(At(AvgCall(n,s),mapped),x); var eq=Eqn(lhs,rhs); var statement=All("n",Nat(),All("s",Finset(n),All("l",Call("LinearMap",Complex(),F.Id("V"),F.Id("W")),All("f",FunctionSpace(n,F.Id("V")),All("x",Config(n),eq))))); return WBinders(statement); }
    private static Formula AvgUniv()
    { var n=F.Id("n"); var f=F.Id("f"); var x=F.Id("x"); var lhs=At(At(AvgCall(n,Call("Finset.univ")),f),x); var rhs=Smul(Inv(T(Pow(D(2),n),Complex())),SumOver(F.Id("y"),Config(n),At(f,F.Id("y")))); return VBinders(All("n",Nat(),All("f",FunctionSpace(n,F.Id("V")),All("x",Config(n),Eqn(lhs,rhs))))); }
    private static Formula CastOne() => T(D(1),Call("Module.End",Complex(),FunctionSpace(F.Id("n"),F.Id("V"))));
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower,Sp,T(F.Id(name),type),Sp,Mapsto,Sp,Parenthesized(body));
}
