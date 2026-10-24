using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangNinh;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Single sign change of the paired triple-Pochhammer kernels.",
        H("Paired Pochhammer kernels"), Blocks(
            Node("a", "The positive-degree coefficient", DescribeRole.Definition, AFormula(),
                "Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = ∑ₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.” The coefficient in positive degree is the displayed rising-factorial quotient. Its degree-zero extension is zero because the series starts at one.", true),
            Node("raw", "The unpaired Turanian kernel", DescribeRole.Definition, RawFormula(),
                "The two products are the degree-k and degree-(m-k) factors in the two Cauchy products. Natural subtraction is used only for indices in the finite coefficient sum."),
            Node("paired", "The reflected kernel", DescribeRole.Definition, PairedFormula(),
                "Reflection sends k to m-k. The central index contributes once, while every other paired term is the sum of both reflected terms."),
            Node("pairPoch", "The factorial-free paired difference", DescribeRole.Definition, PairFormula(),
                "The four rising-factorial products are the paired kernel before positive factorial denominators are removed."),
            Node("a_continuous", "Polynomial parameter dependence", DescribeRole.Theorem,
                All("n", N(), Call("Continuous", Call("a", X("n")))),
                "Every coefficient is a polynomial divided by a fixed positive factorial. Continuity supplies the boundary values of parameter inequalities."),
            Node("paired_sign_step", "Strict backward propagation", DescribeRole.Theorem, StepFormula(),
                "If the paired difference is nonpositive, the larger unmixed product exceeds both mixed products. Comparing the four reciprocal multipliers after moving one factor from the shorter length to the longer length makes the preceding paired difference strictly negative."),
            Node("paired_sign", "At most one sign change", DescribeRole.Theorem, SignFormula(),
                "Backward propagation between rising-factorial lengths 3i and 3j excludes a positive triple-Pochhammer pair followed by a negative one. Positive factorial denominators preserve signs; the middle pair has an additional positive factor of two."))));

    private static DocumentBlock Node(string name, string title, DescribeRole role,
        Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("kz38-kernel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Kernel." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula AFormula()
    {
        Formula n = X("n"), t = X("t");
        return All("n", N(), All("t", R(), Eq(Call("a", n, t),
            Call("ite", Eq(n, D(0)), D(0),
                Div(Poch(Mul(D(3), n), t), Fact(NSub(Mul(D(3), n), D(1))))))));
    }

    private static Formula RawFormula()
    {
        Formula mu=X("mu"), alpha=X("alpha"), beta=X("beta"), m=X("m"), k=X("k");
        Formula expression=Sub(Mul(Call("a", k, Add(mu,alpha)), Call("a", NSub(m,k), Add(mu,beta))),
            Mul(Call("a", k, mu), Call("a", NSub(m,k), Add(Add(mu,alpha),beta))));
        return Parameters(All("m",N(),All("k",N(),Eq(Call("raw",mu,alpha,beta,m,k),expression))));
    }

    private static Formula PairedFormula()
    {
        Formula mu=X("mu"), alpha=X("alpha"), beta=X("beta"), m=X("m"), k=X("k");
        Formula raw=Call("raw",mu,alpha,beta,m,k);
        Formula other=Call("raw",mu,alpha,beta,m,NSub(m,k));
        return Parameters(All("m",N(),All("k",N(),Eq(Call("paired",mu,alpha,beta,m,k),
            Call("ite",Eq(Mul(D(2),k),m),raw,Add(raw,other))))));
    }

    private static Formula PairFormula()
    {
        Formula a=X("a"), b=X("b"), c=X("c"), n=X("N"), k=X("k");
        Formula value=Sub(Sub(Add(Mul(Poch(k,Add(a,b)),Poch(NSub(n,k),Add(a,c))),
            Mul(Poch(k,Add(a,c)),Poch(NSub(n,k),Add(a,b)))),
            Mul(Poch(k,a),Poch(NSub(n,k),Add(Add(a,b),c)))),
            Mul(Poch(k,Add(Add(a,b),c)),Poch(NSub(n,k),a)));
        return ABC(All("N",N(),All("k",N(),Eq(Call("pairPoch",a,b,c,n,k),value))));
    }

    private static Formula StepFormula()
    {
        Formula a=X("a"), b=X("b"), c=X("c"), n=X("N"), k=X("k");
        Formula conclusion=Lt(Call("pairPoch",a,b,c,n,NSub(k,D(1))),D(0));
        conclusion=Imp(Le(Call("pairPoch",a,b,c,n,k),D(0)),conclusion);
        conclusion=Imp(Le(Mul(D(2),k),n),conclusion);
        conclusion=Imp(Le(D(1),k),conclusion);
        return ABC(All("N",N(),All("k",N(),PositiveABC(conclusion))));
    }

    private static Formula SignFormula()
    {
        Formula mu=X("mu"),alpha=X("alpha"),beta=X("beta"),m=X("m"),i=X("i"),j=X("j");
        Formula conclusion=Le(D(0),Call("paired",mu,alpha,beta,m,j));
        conclusion=Imp(Lt(D(0),Call("paired",mu,alpha,beta,m,i)),conclusion);
        conclusion=Imp(Lt(i,j),conclusion);
        conclusion=All("j",N(),Imp(Le(j,new Formula.Apply(Seq(Operatorname,Grp(Seq(X("Nat"),Dot,X("div")))),[m,D(2)])),conclusion));
        conclusion=All("i",N(),Imp(Le(i,new Formula.Apply(Seq(Operatorname,Grp(Seq(X("Nat"),Dot,X("div")))),[m,D(2)])),conclusion));
        return Parameters(All("m",N(),Imp(Lt(D(0),mu),Imp(Lt(D(0),alpha),Imp(Lt(D(0),beta),conclusion)))));
    }

    private static Formula Parameters(Formula f)=>All("mu",R(),All("alpha",R(),All("beta",R(),f)));
    private static Formula ABC(Formula f)=>All("a",R(),All("b",R(),All("c",R(),f)));
    private static Formula PositiveABC(Formula f)=>Imp(Lt(D(0),X("a")),Imp(Lt(D(0),X("b")),Imp(Lt(D(0),X("c")),f)));
    private static Formula X(string name)=>F.Id(name);
    private static Formula R()=>F.Id("Real");
    private static Formula N()=>F.Id("Nat");
    private static Formula Call(string name,params Formula[] args)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula All(string name,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a,Formula b)=>new Formula.Fraction(a,b);
    private static Formula Parenthesized(Formula a)=>Seq(Open,a,Close);
    private static Formula Fact(Formula n)=>Seq(Parenthesized(n),Bang);
    private static Formula NSub(Formula a,Formula b)=>new Formula.Apply(Seq(Operatorname,Grp(Seq(X("Nat"),Dot,X("sub")))),[a,b]);
    private static Formula Poch(Formula n,Formula t)=>new Formula.Apply(Seq(Operatorname,Grp(Seq(X("Polynomial"),Dot,X("eval")))),[t,Call("ascPochhammer",R(),n)]);
}
