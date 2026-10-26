using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class SemicompleteHamiltonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/bangjensengutin2009digraphs");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spanning cycles in semicomplete directed relations",
        H("Spanning cycles in semicomplete directed relations"), Blocks(
        Node("cyclic-insertion", "A change of orientation gives an insertion edge", Insertion(), "cyclic_insertion",
            "For the cyclic list c::l, suppose every vertex is comparable with x, and there are both incoming and outgoing arcs at x. Then a consecutive cyclic pair u,v satisfies D(u,x) and D(x,v). No simplicity or irreflexivity is needed for this split."),
        Node("outside-uniform", "Outside vertices have a uniform orientation", Uniform(), "outside_uniform_of_no_insertion",
            "If there is no such insertion edge, comparability forces every vertex of the cyclic list to point to x with every reverse arc absent, or forces x to point to every vertex with every reverse arc absent. Reciprocal arcs are allowed by the ambient relation; the absent directions are consequences of failed insertion."),
        Node("hamilton", "A simple spanning directed cycle through any vertex", Hamilton(), "finite_semicomplete_hamilton",
            "S is a finite vertex set of size at least two. Every D arc has both endpoints in S. Distinct vertices of S are comparable, and every ordered pair is joined by an actual ReflTransGen D path. The result enumerates every vertex exactly once and closes by one further occurrence of the specified a. Directed two-cycles and arbitrary reciprocal arcs are included."),
        Paragraph(Text("Erase loops from a return path to obtain an initial simple cycle. Maximize its length among the finitely bounded simple cycles. A one-vertex insertion would increase that length. The uniform-orientation lemma therefore partitions outside vertices into receiving and sending classes. Strong connectivity gives a first exit from the cycle and then an actual receiving-to-sending outside arc. Splicing those two distinct outside vertices into a cycle edge increases the length. Thus the maximal cycle spans S; literal rotation places a first.")),
        Paragraph(Text("The original-coordinate port construction applies this theorem to the reverse of its actual blue-target arc relation. The longest-cycle argument is classical; this presentation makes no graph-theory novelty claim.")) )));

    private static DocumentBlock Node(string id, string title, Formula statement, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V => Id("V");
    private static Formula D => Id("D");
    private static Formula L => Id("l");
    private static Formula C => Id("c");
    private static Formula X => Id("x");
    private static Formula Rel(Formula a, Formula b) => Call("apply", D, a, b);
    private static Formula Cycle => Call("cons", C, L);
    private static Formula Closed => Call("append", Cycle, Call("singleton", C));
    private static Formula Split() => Ex("p", Call("List", V), Ex("u", V, Ex("v", V, Ex("s", Call("List", V),
        And(Equal(Closed, Call("append", Id("p"), Call("cons", Id("u"), Call("cons", Id("v"), Id("s"))))),
            Rel(Id("u"), X), Rel(X, Id("v")))))));
    private static Formula Semi => In("v", Cycle, Or(Rel(Id("v"), X), Rel(X, Id("v"))));
    private static Formula Common(Formula f) => All("V", Call("Type"), All("D", Call("Relation", V),
        All("c", V, All("x", V, All("l", Call("List", V), f)))));
    private static Formula Insertion() => FormulaDsl.Disp(Common(To(And(Semi,
        ExIn("v", Cycle, Rel(Id("v"), X)), ExIn("v", Cycle, Rel(X, Id("v")))), Split())));
    private static Formula Uniform() => FormulaDsl.Disp(Common(To(And(Semi, new Formula.Not(Split())),
        Or(In("v", Cycle, And(Rel(Id("v"), X), new Formula.Not(Rel(X, Id("v"))))),
            In("v", Cycle, And(Rel(X, Id("v")), new Formula.Not(Rel(Id("v"), X))))))));
    private static Formula Hamilton()
    {
        var s = Id("S"); var a = Id("a"); var t = Id("t"); var v = Id("s");
        var endpoints = All("s", V, All("t", V, To(Rel(v,t), And(Member(v,s),Member(t,s)))));
        var semi = All("s", V, All("t", V, To(And(Member(v,s),Member(t,s),NotEqual(v,t)),Or(Rel(v,t),Rel(t,v)))));
        var strong = All("s", V, All("t", V, To(And(Member(v,s),Member(t,s)),Call("ReflTransGen",D,v,t))));
        var w = Call("cons", a, L);
        var conclusion = Ex("l", Call("List",V), And(Call("Nodup",w),Equal(Call("toFinset",w),s),
            Le(Num(2),Call("length",w)),Call("IsChain",D,Call("append",w,Call("singleton",a)))));
        return FormulaDsl.Disp(All("V",Call("Type"), WithEquality(V, All("S",Call("Finset",V), All("D",Call("Relation",V), All("a",V,
            To(And(endpoints,Le(Num(2),Call("card",s)),semi,strong,Member(a,s)),conclusion)))))));
    }
    private static Formula WithEquality(Formula v, Formula body) => FormulaDsl.Seq(FormulaDsl.OpenBracket,Call("DecidableEq",v),FormulaDsl.CloseBracket,FormulaDsl.Comma,FormulaDsl.Sp,body);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula In(string n, Formula s, Formula b) => All(n,V,To(Member(Id(n),s),b));
    private static Formula ExIn(string n, Formula s, Formula b) => Ex(n,V,And(Member(Id(n),s),b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula To(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] a) { var r=a[^1]; for(var i=a.Length-2;i>=0;i--) r=new Formula.Logic(a[i],FormulaLogicOperator.And,r); return r; }
}
