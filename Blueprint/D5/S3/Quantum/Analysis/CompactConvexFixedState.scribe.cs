using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CompactConvexFixedStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Invariant compact convex sets contain fixed states and the full fixed dual forces uniqueness.",H("Compact convex fixed states and the entire real fixed dual"),Blocks(
        Paragraph(Text("These are the general invariant-set and real-dual predecessors used by the asynchronous maximum argument for Quantum Origin V, Section 79. The matrix-only ChannelFixedState result is not substituted for the arbitrary real carrier. All topological statements concern the displayed finite-dimensional real norm topology.")),
        Describe.Lean(DescribeId.Create("mass-compactconvexfixedstate-exists-fixed-mem"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/CompactConvexFixedState.exists_fixed_mem"),H("Fixed points inside invariant compact convex sets"),StatementSource.FromAuthor(Disp(Existence())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Phi is any real linear endomorphism of a finite-dimensional real normed space. Each nonempty compact convex invariant B contains a fixed point. Orbit Cesaro averages stay in B. The pinned Mathlib Birkhoff-average endpoint estimate tends to zero, and compactness supplies a subsequential fixed limit. No fixed-point theorem or mixing premise is added."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("mass-compactconvexfixedstate-fixed-eq-mass-smul"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/CompactConvexFixedState.fixed_eq_mass_smul"),H("Every fixed vector has its original scalar mass"),StatementSource.FromAuthor(Disp(Uniqueness())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The condition on f ranges over every real linear functional. Rank-nullity and the unchanged rank of the dual map bound the real fixed space by one dimension. A fixed sigma of mass one spans it, and applying the original u determines the scalar. Sigma may be on the cone boundary; this statement needs no cone or interior hypothesis."))),DescribeRole.Theorem))));

    private static Formula V(string s)=>F.Id(s);
    private static Formula R=>Call("Real");
    private static Formula One=>D(1);
    private static Formula Zero=>D(0);
    private static Formula Call(string s,params Formula[] a)=>new Formula.FunctionCall(FormulaIdentifier.Create(s),[..a]);
    private static Formula At(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula App(string s,params Formula[] a)=>At(V(s),a);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Lam(string s,Formula t,Formula b)=>Seq(Grp(V(s),Colon,t),Mapsto,Sp,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Eqf(Formula a,Formula b)=>Equal(a,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Ne(Formula a,Formula b)=>Seq(a,Sp,Neq,Sp,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Addf(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Smul(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula In(Formula x,Formula s)=>Call("Mem",x,s);
    private static Formula Chain(params Formula[] a){var b=a[^1];for(var i=a.Length-2;i>=0;i--)b=And(a[i],b);return b;}
    private static Formula Assuming(Formula b,params Formula[] p){for(var i=p.Length-1;i>=0;i--)b=Imp(p[i],b);return b;}
    private static Formula Lm(Formula a,Formula b)=>Call("LinearMap",R,a,b);
    private static Formula Dual(Formula a)=>Call("Dual",R,a);
    private static Formula Span(Formula s)=>Call("span",R,s);
    private static Formula Top(Formula a)=>Call("top",Call("Submodule",R,a));
    private static Formula Space(string n,Formula b,bool nontrivial=false){var a=V(n);var body=Seq(OpenBracket,Call("NormedAddCommGroup",a),CloseBracket,Sp,OpenBracket,Call("NormedSpace",R,a),CloseBracket,Sp,OpenBracket,Call("FiniteDimensional",R,a),CloseBracket,Sp,nontrivial?Seq(OpenBracket,Call("Nontrivial",a),CloseBracket,Sp,b):b);return All("v"+n,Call("Universe"),All(n,Call("Type",V("v"+n)),body));}
    private static Formula Indices(Formula b)=>All("vI",Call("Universe"),All("I",Call("Type",V("vI")),Seq(OpenBracket,Call("Fintype",V("I")),CloseBracket,Sp,OpenBracket,Call("DecidableEq",V("I")),CloseBracket,Sp,b)));
    private static Formula Strict(string c,string u,string a)=>All("x",V(a),Assuming(Lt(Zero,App(u,V("x"))),In(V("x"),V(c)),Ne(V("x"),Zero)));
    private static Formula FullDual(string p,string u,string a)=>All("f",Dual(V(a)),Imp(Eqf(Call("comp",V("f"),V(p)),V("f")),Ex("c",R,Eqf(V("f"),Smul(V("c"),V(u))))));
    private static Formula Base(string c,string u)=>Call("base",V(c),V(u));
    private static Formula Cube=>Call("pi",Call("univ",V("I")),Lam("i",V("I"),V("K")));
    private static Formula WeightPos=>All("i",V("I"),Lt(Zero,App("alpha",V("i"))));
    private static Formula WeightSum=>Eqf(Call("sum",V("alpha")),One);
    private static Formula ProductMass(string u,Formula a)=>Call("prod",Lam("i",V("I"),App(u,At(a,V("i")))));
    private static Formula Update(Formula a,Formula i)=>Call("update",a,i,App("Phi",At(a,i)));

    private static Formula Existence()=>Space("A",All("Phi",Lm(V("A"),V("A")),All("B",Call("Set",V("A")),Assuming(Ex("x",V("A"),And(In(V("x"),V("B")),Eqf(App("Phi",V("x")),V("x")))),Call("IsCompact",V("B")),Call("Nonempty",V("B")),Call("Convex",R,V("B")),Call("MapsTo",V("Phi"),V("B"),V("B"))))));
    private static Formula Uniqueness()=>Space("A",All("Phi",Lm(V("A"),V("A")),All("u",Dual(V("A")),Assuming(All("sigma",V("A"),Assuming(All("x",V("A"),Imp(Eqf(App("Phi",V("x")),V("x")),Eqf(V("x"),Smul(App("u",V("x")),V("sigma"))))),Eqf(App("Phi",V("sigma")),V("sigma")),Eqf(App("u",V("sigma")),One))),Eqf(Call("comp",V("u"),V("Phi")),V("u")),FullDual("Phi","u","A")))));

}
