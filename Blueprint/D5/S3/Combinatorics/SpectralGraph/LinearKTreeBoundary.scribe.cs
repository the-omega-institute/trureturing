using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class LinearKTreeBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary.";
    public DocumentDefinition Create()
    {
        Formula n=V("n"), a=V("A"), b=V("b"), i=V("i"), j=V("j"), r=V("r"), f=V("f"), d=V("D"), q=V("Q"), u=V("u");
        Formula band=All("n",Nat(),All("b",Nat(),All("A",Mat(Fin(n)),Eqn(Call("IsBanded",b,a),
            All("i",Fin(n),All("j",Fin(n),Imp(LtOf(b,App(Qualified("Nat","dist"),Val(i),Val(j))),Eqn(App(a,i,j),D(0)))))))));
        Formula rev=All("N",Nat(),All("A",Mat(Fin(V("N"))),Eqn(Call("IsReversalInvariant",a),
            All("i",Fin(V("N")),All("j",Fin(V("N")),Eqn(App(a,App(Qualified("Fin","rev"),i),App(Qualified("Fin","rev"),j)),App(a,i,j)))))));
        Formula increment=All("R",Fn(Nat(),Real()),All("c",Fn(Nat(),Real()),All("d",Real(),All("C",Real(),
            Imp(Tendsto(V("c"),V("C")),Imp(Eventually("n",Eqn(App(V("R"),n),Add(Mul(Cast(n),V("d")),App(V("c"),n)))),
                Tendsto(Lam("n",Nat(),Sub(App(V("R"),Add(n,D(1))),App(V("R"),n))),V("d"))))))));
        Formula defect=FiniteBind(All("Q",Mat(V("I")),Imp(App(Qualified("Matrix","IsSymm"),q),
            Imp(Call("IsUnit",q),All("u",Fn(V("I"),Real()),All("D",Real(),Imp(Ne(d,D(0)),
                Eqn(DotVec(u,MulVec(Inv(q),u)),Add(new Formula.Fraction(DotVec(u,u),d),
                    new Formula.Fraction(Add(DotVec(u,Defect(q,u,d)),DotVec(Defect(q,u,d),MulVec(Inv(q),Defect(q,u,d)))),Pow(d,D(2))))))))))));
        Formula total=All("r",Nat(),All("N",Nat(),Imp(LeqOf(r,V("N")),All("f",Fn(Nat(),Real()),
            Imp(Vanishes(r,f),Eqn(SumFin("i",V("N"),Add(App(f,Val(i)),App(f,Val(App(Qualified("Fin","rev"),i))))),
                Mul(D(2),SumFin("i",r,App(f,Val(i))))))))));
        Formula bound=All("r",Nat(),All("N",Nat(),Imp(LeqOf(r,V("N")),All("f",Fn(Nat(),Real()),
            Imp(Vanishes(r,f),LeqOf(Pow(new Formula.Norm(App(Qualified("WithLp","toLp"),D(2),
                Lam("i",Fin(V("N")),Add(App(f,Val(i)),App(f,Val(App(Qualified("Fin","rev"),i))))))),D(2)),
                Mul(D(4),SumFin("i",r,Pow(App(f,Val(i)),D(2))))))))));
        Formula row=FiniteBind(All("A",Mat(V("I")),Imp(App(Qualified("Matrix","IsHermitian"),a),
            Imp(All("i",V("I"),All("j",V("I"),LeqOf(D(0),App(a,i,j)))),All("D",Real(),
                Imp(All("i",V("I"),LeqOf(SumOver("j",V("I"),App(a,i,j)),d)),LeqOf(a,Smul(d,Typed(D(1),Mat(V("I")))))))))));
        Formula richardson=FiniteBind(All("Q",Mat(V("I")),All("D",Real(),Imp(LeqOf(D(1),d),
            Imp(LeqOf(Typed(D(1),Mat(V("I"))),q),Imp(LeqOf(q,Smul(d,Typed(D(1),Mat(V("I"))))),
                LeqOf(new Formula.Norm(Sub(Typed(D(1),Mat(V("I"))),Smul(Inv(d),q))),Sub(D(1),Inv(d)))))))));
        return DocumentDefinition.Create(ScribeNode.Create("Finite propagation and endpoint moments of banded matrices.",H("Boundary locality for straight linear k-trees"),Blocks(
            Node("band","Banded matrices","IsBanded",band,"An entry is zero when the distance between its indices exceeds b.",DescribeRole.Definition,AssessedProvenance.FromRepo()),
            Node("reversal","Reversal symmetry","IsReversalInvariant",rev,"Reversing both indices preserves each matrix entry.",DescribeRole.Definition,AssessedProvenance.FromRepo()),
            Node("moments","Eventual constancy of boundary moments","boundary_moments_stabilize",MomentBody(),"A fixed power reaches only a finite distance. Once both endpoints are farther apart than that distance, their cross terms vanish; the same-endpoint terms agree with one fixed finite section. Reversal symmetry makes the two endpoint contributions equal.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("increment","Consecutive differences of an affine asymptotic","increment_limit_of_affine_correction",increment,"A convergent correction contributes zero to the limit of consecutive differences.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("defect","Exact inverse defect expansion","inverse_defect_expansion",defect,"For c = D u - Q u, the inverse quadratic form splits into a bulk term and a defect correction.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("sum","Constant boundary sum","boundary_sum_constant",total,"Reflection preserves the sum, and support in the first r positions reduces it to a fixed finite sum.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("norm","Uniform boundary norm bound","boundary_norm_bound",bound,"The squared norm of the two endpoint vectors is at most four times the squared norm of one endpoint profile.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("row","Order bound from nonnegative row sums","nonnegative_row_bound",row,"Symmetry and 2xy ≤ x²+y² bound the quadratic form by the maximum row sum.",DescribeRole.Theorem,AssessedProvenance.FromRepo()),
            Node("richardson","Geometric contraction bound","richardson_norm_bound",richardson,"The order interval I ≤ Q ≤ D I places the spectrum of I - D⁻¹ Q in the interval from zero to 1 - D⁻¹.",DescribeRole.Theorem,AssessedProvenance.FromRepo()))));
    }
    private static Formula MomentBody()
    {
        Formula a=V("A"), b=V("b"), r=V("r"), q=V("q"), f=V("f"), n=V("N"), m=V("M"), i=V("i"), j=V("j"), u=V("u"), v=V("v"), l=V("L");
        Formula coeff=All("N",Nat(),All("M",Nat(),All("i",Fin(n),All("j",Fin(n),All("u",Fin(m),All("v",Fin(m),
            Imp(Eqn(Val(i),Val(u)),Imp(Eqn(Val(j),Val(v)),Imp(LeqOf(Add(Val(i),q),n),Imp(LeqOf(Add(Val(u),q),m),Eqn(App(App(a,n),i,j),App(App(a,m),u,v))))))))))));
        Formula profile=Lam("i",Fin(n),Add(App(f,Val(i)),App(f,Val(App(Qualified("Fin","rev"),i)))));
        Formula conclusion=All("L",Nat(),Ex("C",Real(),Eventually("N",Eqn(DotVec(profile,MulVec(Pow(App(a,n),l),profile)),V("C")))));
        return All("A",DependentFn("N",Nat(),Mat(Fin(n))),All("b",Nat(),All("r",Nat(),All("q",Nat(),All("f",Fn(Nat(),Real()),
            Imp(Vanishes(r,f),Imp(All("N",Nat(),Call("IsBanded",b,App(a,n))),
                Imp(All("N",Nat(),Call("IsReversalInvariant",App(a,n))),Imp(coeff,conclusion)))))))));
    }
    private static DocumentBlock Node(string id,string title,string name,Formula f,string prose,DescribeRole role,AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("linear-k-tree-boundary-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance,Blocks(Paragraph(Text(prose))),role);
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname,Grp(V(s)));
    private static Formula Qualified(string a,string b) => Seq(C(a),Dot,C(b));
    private static Formula Call(string s,params Formula[] a) => a.Length==0?C(s):App(C(s),a);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Nat() => C("Nat");
    private static Formula Real() => C("Real");
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Mat(Formula i) => Call("Matrix",i,i,Real());
    private static Formula Val(Formula i) => Call("val",i);
    private static Formula Typed(Formula x,Formula t) => Parenthesized(Seq(x,Colon,Sp,t));
    private static Formula Cast(Formula x) => Typed(x,Real());
    private static Formula Fn(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula DependentFn(string n,Formula a,Formula b) => Fn(Typed(V(n),a),b);
    private static Formula All(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula Lam(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,V(n),Colon,Sp,t,Sp,Mapsto,Sp,b));
    private static Formula Eqn(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula LeqOf(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula LtOf(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a,Formula b) => new Formula.Power(a,b);
    private static Formula Inv(Formula a) => Pow(a,new Formula.Negate(D(1)));
    private static Formula Smul(Formula a,Formula b) => App(Qualified("HSMul","hSMul"),a,b);
    private static Formula MulVec(Formula a,Formula b) => App(Qualified("Matrix","mulVec"),a,b);
    private static Formula DotVec(Formula a,Formula b) => Call("dotProduct",a,b);
    private static Formula Defect(Formula q,Formula u,Formula d) => Sub(Smul(d,u),MulVec(q,u));
    private static Formula SumFin(string n,Formula size,Formula body) => SumOver(n,Fin(size),body);
    private static Formula SumOver(string n,Formula t,Formula body) => App(Qualified("Finset","sum"),Qualified("Finset","univ"),Lam(n,t,body));
    private static Formula Eventually(string n,Formula p) => App(Qualified("Filter","Eventually"),Lam(n,Nat(),p),Qualified("Filter","atTop"));
    private static Formula Tendsto(Formula f,Formula x) => App(Qualified("Filter","Tendsto"),f,Qualified("Filter","atTop"),Call("nhds",x));
    private static Formula Vanishes(Formula r,Formula f) => All("i",Nat(),Imp(LeqOf(r,V("i")),Eqn(App(f,V("i")),D(0))));
    private static Formula FiniteBind(Formula f) => All("I",C("Type"),Seq(OpenBracket,Call("Fintype",V("I")),CloseBracket,Sp,OpenBracket,Call("DecidableEq",V("I")),CloseBracket,Sp,f));
}
