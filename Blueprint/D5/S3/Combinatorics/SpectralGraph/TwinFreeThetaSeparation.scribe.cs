using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class TwinFreeThetaSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite twin-free theta separating family.",H("An infinite twin-free theta separating family"),Blocks(
            Node("claim","The infinite-family question","claim",Eqn(Call("claim"),Some("orders",Fn(C("Nat"),C("Nat")),Some("graphs",Fn(Parenthesized(Seq(V("i"),Colon,Sp,C("Nat"))),Call("SimpleGraph",Call("Fin",App(V("orders"),V("i"))))),And(All("i",C("Nat"),And(DotName(App(V("graphs"),V("i")),"Connected"),And(Call("TwinFree",App(V("graphs"),V("i"))),Or(And(Eqn(Call("mmL",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i")))),Ne(Call("mmQ",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i"))))),And(Eqn(Call("mmQ",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i")))),Ne(Call("mmL",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i"))))))))),All("i",C("Nat"),All("j",C("Nat"),Implies(Ne(V("i"),V("j")),NotOf(Call("Nonempty",App(DotName(App(V("graphs"),V("i")),"Iso"),App(V("graphs"),V("j")))))))))))),AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/alfuraidan2026laplacian")),"Problem 30 (p. 27): \u201cDo there exist infinite families of connected twin-free graphs satisfying exactly one of the two equalities mm_L(G)=dim(G), mm_Q(G)=dim(G)? The computational census shows that finite twin-free examples occur in both directions.\u201d The carrier of graph i is Fin (orders i). Pairwise nonisomorphism expresses infinitude; the disjunction allows either equality direction in each member.",DescribeRole.Definition),
            Node("result","An infinite separating family","result",Some("orders",Fn(C("Nat"),C("Nat")),Some("graphs",Fn(Parenthesized(Seq(V("i"),Colon,Sp,C("Nat"))),Call("SimpleGraph",Call("Fin",App(V("orders"),V("i"))))),And(All("i",C("Nat"),And(DotName(App(V("graphs"),V("i")),"Connected"),And(Call("TwinFree",App(V("graphs"),V("i"))),Or(And(Eqn(Call("mmL",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i")))),Ne(Call("mmQ",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i"))))),And(Eqn(Call("mmQ",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i")))),Ne(Call("mmL",App(V("graphs"),V("i"))),Call("metricDimension",App(V("graphs"),V("i"))))))))),All("i",C("Nat"),All("j",C("Nat"),Implies(Ne(V("i"),V("j")),NotOf(Call("Nonempty",App(DotName(App(V("graphs"),V("i")),"Iso"),App(V("graphs"),V("j"))))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/alfuraidan2026laplacian")),"Take orders i=6(i+1)+9 and graphs i=thetaGraph (6(i+1)+4). Every graph is connected and twin-free, its metric dimension and Laplacian maximum multiplicity equal 2, and its signless maximum multiplicity is at most 1. Distinct orders exclude isomorphisms.",DescribeRole.Theorem,new OpenProblemResolutionClaim(ProblemSlugRef.Create("aks2610"),ResolutionKind.Proved)))));
    private static DocumentBlock Node(string id,string title,string name,Formula f,AssessedProvenance provenance,string prose,DescribeRole role,OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("twinfreethetaseparation-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance,Blocks(Paragraph(Text(prose))),role,resolution);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula DotName(Formula a,string name) => Seq(Parenthesized(a),Dot,C(name));
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Call(string s,params Formula[] a) => a.Length == 0 ? C(s) : App(C(s),a);
    private static Formula All(string s,Formula t,Formula b) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,b);
    private static Formula Some(string s,Formula t,Formula b) => Seq(Exists,Sp,V(s),Colon,Sp,t,Comma,Sp,b);
    private static Formula Eqn(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Or(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Or,Parenthesized(b));
    private static Formula Implies(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula NotOf(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Fn(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);
}
