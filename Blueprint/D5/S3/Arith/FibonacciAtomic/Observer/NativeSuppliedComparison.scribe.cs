using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativeSuppliedComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSuppliedComparison",H("Fixed skeleton query separation"),Blocks(
            Paragraph(Text("Fix one public full ordered skeleton S. Its chart numbers every original leaf once, in order, and its address map retains the actual depth of each leaf. The source u(S,x) fills that same chart with alpha for false and beta for true. Correct(M,S,T) quantifies every independent assignment x and every entry t from zero through T. For each there is a finite first-halt Run, and every such Run outputs the original XOR. Static(M,S,T) says that every promised Run has zero genuine Updates. Neither predicate supplies the actual lag to the controller, imposes a common runtime, or excludes unreachable Update rows.")),
            Paragraph(Text("The controller's entire mutable state is its state word. A state selects one fixed literal or a source-blind internal instruction, a genuine Update with constant acknowledgement, or a fixed-output halt. Run retains the query state together with its absolute actual epoch. The replay theorem compares the same evolving original sources at those epochs, retaining arbitrary finite internal work. The installed query and halt sets count every state of their respective instruction types, whether or not a promised source reaches it.")),
            Describe("same-run-distinct-queries","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.same_run_distinct_queries",
                "Distinct words on each actual run",SameRun(),
                "Each coordinate is compared with its one-label flip in the identical original chart at the identical entry. If all Read replies on the chosen run agreed, exact replay would give the same fixed halt on opposite original parities. A literal can depend only on the unique original leaf cone it enters; a literal ending inside the skeleton has no label dependence. Numbered-row locality includes absent replies. Pairwise prefix disjointness of the original cones therefore makes the chosen query states injective, even when a query state recurs at a different source epoch."),
            Describe("installed-lower-bound","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.installed_lower_bound",
                "All installed states",Installed(false),
                "There are at least h query states, where h is the leaf count of S. Both original XOR values occur across the full assignment family, so two distinct fixed-output halt states are installed. The query and halt sets are disjoint. The two halts occur across assignments; they are not asserted to occur on one run."),
            Describe("static-installed-lower-bound","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison.static_installed_lower_bound",
                "Static entry cover",Installed(true),
                "For each original index and each t from zero through T, compare the all-zero assignment with its single-coordinate flip. Every separating query has actual epoch t, because that promised run has zero Updates. Removing that leaf's own address leaves a suffix separating atomic ranks t and t plus one. The guarded atomic window places these entries among at most three consecutive ranks for a fixed suffix. Encoding an entry by its selected query and one of three offsets proves that the cone has at least r=(T+3)/3 query states. Summing over disjoint original cones gives h times r query states and two additional halts. This is a union of installed words over entries, with no assertion of h times r Reads on one run."))));

    private static Formula SameRun() {
        var e=V("E");var m=V("M");var s=V("S");var t=V("t");var cap=V("T");var x=V("x");var qs=V("q");
        var h=C("length",s);var pick=V("p");var i=V("i");var ep=V("n");var word=C("p",i);var lit=C("literal",m,word);
        var src=C("source",C("chartOf",s),x);var flip=C("source",C("chartOf",s),C("flip",x,i));
        var sep=Ex("n",V("Nat"),A(Member(C("pair",word,ep),qs),A(C("IsPrefix",C("address",C("chartOf",s),i),lit),
            Ne(C("readout",lit,C("iterate",ep,src)),C("readout",lit,C("iterate",ep,flip))))));
        var result=Ex("p",Arrow(C("Fin",h),e),A(C("Injective",pick),All("i",C("Fin",h),sep)));
        var run=C("Run",m,src,C("initial",m),t,qs,V("u"),V("f"),V("b"));
        var body=Imp(C("Correct",m,s,cap),Imp(Le(t,cap),Imp(run,result)));
        return All("E",V("Type"),All("M",C("Controller",e),All("S",V("Source"),All("T",V("Nat"),
            All("x",Arrow(C("Fin",h),V("Bool")),All("t",V("Nat"),All("q",C("List",C("Product",e,V("Nat"))),
            All("u",V("Nat"),All("f",e,All("b",V("Bool"),body))))))))));
    }
    private static Formula Installed(bool stationary) {
        var e=V("E");var m=V("M");var s=V("S");var t=V("T");var h=C("length",s);
        var count=stationary ? Times(h,C("div",PlusOf(t,D(3)),D(3))) : h;
        var body=stationary ? A(Le(count,C("card",C("queries",m))),Le(PlusOf(count,D(2)),C("card",e))) :
            A(Le(count,C("card",C("queries",m))),A(Le(D(2),C("card",C("halts",m))),Le(PlusOf(count,D(2)),C("card",e))));
        if(stationary) body=Imp(C("Static",m,s,t),body);
        return All("E",V("Type"),Finite(e,All("M",C("Controller",e),All("S",V("Source"),All("T",V("Nat"),Imp(C("Correct",m,s,t),body))))));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula f) => Seq(Open,f,Close);
    private static Formula C(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,P(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,P(b));
    private static Formula A(Formula a,Formula b) => Seq(P(a),Sp,Land,Sp,P(b));
    private static Formula Imp(Formula a,Formula b) => Seq(P(a),Sp,Implies,Sp,P(b));
    private static Formula Ne(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula PlusOf(Formula a,Formula b) => Seq(P(a),Sp,Plus,Sp,P(b));
    private static Formula Times(Formula a,Formula b) => Seq(P(a),P(b));
    private static Formula Arrow(Formula a,Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Member(Formula a,Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula Finite(Formula e,Formula b) => Seq(OpenBracket,C("Fintype",e),CloseBracket,Comma,Sp,b);
    private static DocumentBlock.Describe Describe(string id,string declaration,string title,Formula statement,string text) =>
        DescribeNode(id,declaration,title,statement,text);
    private static DocumentBlock.Describe DescribeNode(string id,string declaration,string title,Formula statement,string text) =>
        global::StrataLint.Scribe.Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(declaration),H(title),
            StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
}
