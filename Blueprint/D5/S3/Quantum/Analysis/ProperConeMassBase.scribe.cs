using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class ProperConeMassBaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("A strictly positive mass gives the entire compact convex spanning state base.",H("The entire proper-cone state base"),Blocks(
        Paragraph(Text("This supplies the entire compact state base required in Quantum Origin V, definitions 79.1 and 79.2, from the original closed generating cone and original strictly positive mass. No self-duality, Jordan representation, preferred coordinates, or interior stationary state is assumed.")),
        Describe.Lean(DescribeId.Create("mass-properconemassbase-base"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/ProperConeMassBase.base"),H("The full normalized cone base"),StatementSource.FromAuthor(Disp(BaseDefinition())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("base(C,u) is exactly the set of all x in C with u(x)=1. It is not a chosen frame, a finite sample, or an interior subset."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("mass-properconemassbase-entire-base-geometry"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/ProperConeMassBase.entire_base_geometry"),H("Compactness, nonemptiness, convexity and full span"),StatementSource.FromAuthor(Disp(Geometry())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("A proper cone here is Mathlib closed cone data; strict positivity on every nonzero cone element also excludes a line. Generating means real linear span equals the entire nonzero carrier. Normalize any nonzero cone element to obtain a state. On the cone intersection with the unit sphere, compactness and strict positivity give a positive minimum of u. It bounds every normalized state in norm. Closedness then gives compactness. Each nonzero positive vector is its mass times a normalized state, so the entire base spans."))),DescribeRole.Theorem))));

    private static Formula V(string s)=>F.Id(s);
    private static Formula R=>Call("Real");
    private static Formula One=>D(1);
    private static Formula Zero=>D(0);
    private static Formula Call(string s,params Formula[] a)=>new Formula.FunctionCall(FormulaIdentifier.Create(s),[..a]);
    private static Formula At(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula App(string s,params Formula[] a)=>At(V(s),a);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Lam(string s,Formula t,Formula b)=>Seq(Grp(V(s),Colon,t),Mapsto,Sp,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eqf(Formula a,Formula b)=>Equal(a,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Ne(Formula a,Formula b)=>Seq(a,Sp,Neq,Sp,b);
    private static Formula In(Formula x,Formula s)=>Call("Mem",x,s);
    private static Formula Chain(params Formula[] a){var b=a[^1];for(var i=a.Length-2;i>=0;i--)b=And(a[i],b);return b;}
    private static Formula Assuming(Formula b,params Formula[] p){for(var i=p.Length-1;i>=0;i--)b=Imp(p[i],b);return b;}
    private static Formula Dual(Formula a)=>Call("Dual",R,a);
    private static Formula Span(Formula s)=>Call("span",R,s);
    private static Formula Top(Formula a)=>Call("top",Call("Submodule",R,a));
    private static Formula Space(string n,Formula b,bool nontrivial=false,bool finite=true)
    {
        var a=V(n);
        if(nontrivial) b=Seq(OpenBracket,Call("Nontrivial",a),CloseBracket,Sp,b);
        if(finite) b=Seq(OpenBracket,Call("FiniteDimensional",R,a),CloseBracket,Sp,b);
        b=Seq(OpenBracket,Call("NormedAddCommGroup",a),CloseBracket,Sp,OpenBracket,Call("NormedSpace",R,a),CloseBracket,Sp,b);
        return All("v"+n,Call("Universe"),All(n,Call("Type",V("v"+n)),b));
    }
    private static Formula Strict(string c,string u,string a)=>All("x",V(a),Assuming(Lt(Zero,App(u,V("x"))),In(V("x"),V(c)),Ne(V("x"),Zero)));
    private static Formula Base(string c,string u)=>Call("base",V(c),V(u));
    private static Formula Scope(Formula b)=>Space("A",All("C",Call("ProperCone",R,V("A")),All("u",Dual(V("A")),b)),true);
    private static Formula BaseDefinition()=>Space("A",All("C",Call("ProperCone",R,V("A")),All("u",Dual(V("A")),Eqf(Base("C","u"),Call("setOf",Lam("x",V("A"),And(In(V("x"),V("C")),Eqf(App("u",V("x")),One))))))),finite:false);
    private static Formula Geometry()=>Scope(Assuming(Chain(Call("Nonempty",Base("C","u")),Call("IsCompact",Base("C","u")),Call("Convex",R,Base("C","u")),Eqf(Span(Base("C","u")),Top(V("A")))),Eqf(Span(V("C")),Top(V("A"))),Strict("C","u","A")));

}
