using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.CNF;
internal sealed class OccurrenceCompilerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite CNF occurrence graphs with exact native continuation prefixes.",
        H("Literal Occurrence Compilation and Arbitrary Continuations"), Blocks(
            Paragraph(Text("A Formula(n) is an ordered finite list of clauses over Fin(n). A clause is an ordered list of variable-polarity pairs. Every clause width is allowed. The source representation Conventional.Formula has finite binary-word names; BinaryNames.denseFormula renumbers exactly its distinct appearing names using the original rightmost-occurrence deduplication order. It retains every clause, polarity and occurrence. Repeated variables, repeated clauses, tautologies, empty clauses and the empty conjunction are included.")),
            Paragraph(Text("The fixed literal for index i is the original NativeBooleanAssignmentBanks.literal(n,i): RLL followed by the i-th word among the first n lexicographic words of length Nat.clog 2 (max 2 n). The same actual source u is used at every occurrence. assignment(n,u,i) is true precisely when readout(literal(n,i),substitution(u)) is branch. Positive literals accept branch alone; negative literals accept alpha, beta and absent. No restriction on replies, source height or source profile is imposed.")),
            Paragraph(Text("Targets are internal(i), success and failure. A Read record stores one complete literal address and a successor for each of the four replies. records(base,f) concatenates one record for every occurrence in input order, including unreachable occurrences. Within a clause, an accepting reply selects the next clause entry and another reply selects the next literal or failure. The empty conjunction entry is success. An empty clause entry is failure. These entries are compile-time labels and require zero transitions.")),
            Paragraph(Text("occurrences(f) is the sum of the clause lengths. evaluate(f,u) is the ordinary conjunction of the clause evaluations under assignment(n,u). resolve(place,S,F) maps internal(i) to place(i) and the two external labels to S and F. Installed(C,place,S,F,rs) requires each record (i,r) in rs to map to a native running state q with place(i)=inl(q), C.addr(q)=r.address and C.next(q,reply)=resolve(place,S,F,r.next(reply)) for every reply. Thus installation concerns the actual native Controller fields, rather than an abstract transition list.")),
            Describe.Lean(DescribeId.Create("installed-occurrence-prefix"), DeclarationHandle.Create(Prefix+"installed_prefix"),
                H("Prefix in Any Controller Containing the Records"), StatementSource.FromAuthor(Disp(PrefixStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here K=Q+H is the original Controller state space. step(C,u,inl(q)) is some(C.next(q,readout(C.addr(q),substitution(u)))); step(C,u,inr(h)) is none. EvalsToInTime counts these actual native Read transitions and can end at a running state. Nonempty removes the choice of a particular bounded-run certificate from the proposition. The statement requires no termination or transition property of S or F, which can coincide or label loop Reads. The proof takes one actual transition for a tested literal, stops on its first satisfying reply, and composes the resulting clause prefixes.")),
                    Paragraph(Text("The record identifiers are exactly 0 through occurrences(f)-1. The installed table premise includes every record, even when an entry or an earlier reply makes it unreachable. For a concrete disjoint installation these records are distinct running states. The general prefix statement also applies to any faithful relocation satisfying Installed."))), DescribeRole.Theorem),
            Paragraph(Text("plug(rs,C,S,F) has running states Fin(length(rs))+Q and the same Halt type H. embed maps an old running state q to inl(inr(q)) and an old Halt h to inr(h). The new state inl(i) stores rs[i]'s literal and resolves its four successors. placement(rs,F,i) is inl(inl(i)) when i is in range, and embed(F) otherwise. Valid(entry,rs) says every internal entry label is in range, and every internal successor j of a record i satisfies i<j<length(rs). This proves that compiled references never use the total extension outside the fragment.")),
            Paragraph(Text("For a conventional formula f, sourceAssignment(f,u,name) applies the original source assignment to NativeBooleanAssignmentBanks.localIndex(occurrences(f),name). The assignment domain is exactly the appearing-name subtype. Its size depends on distinct spellings, not the numeric magnitude of a name. slotMap(rs,F) abbreviates the function i:Fin(length(rs)) mapped to placement(rs,F,value(i)). Let dense=denseFormula(f), rs=records(0,dense), and linked=plug(rs,C,S,F) in the following statement. M is length(Conventional.occurrences(f)); these definitions also apply when M=0.")),
            Describe.Lean(DescribeId.Create("native-occurrence-compiler"), DeclarationHandle.Create(Prefix+"native_occurrence_compiler"),
                H("Exact Installed Compiler on Every Actual Source"), StatementSource.FromAuthor(Disp(NativeStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There are exactly M distinct new running states, one per original literal occurrence. Every original ambient literal, every original successor after the label embedding, and the entire Halt output function are preserved. The endpoint is the embedded supplied S when the original formula is true under sourceAssignment(f,u), and the embedded supplied F otherwise. Empty entries are aliases, so a continuation Read or Halt can already be the endpoint at zero calls. Reaching a continuation does not consume its transition or assert that it terminates.")),
                    Paragraph(Text("Forward internal indices and the clause induction bound the prefix by M charged occurrence calls on the one stationary source. All four successors are specified independently of the observed reply. The statement is unbounded symbolic correctness for arbitrary finite CNFs and arbitrary supplied native tables. These conclusions specify native control flow; serialized byte bounds and finite-machine construction time require additional results. The source interpretation and lexicographic literals reuse the original definitions; no assignment-realizability theorem is needed."))), DescribeRole.Theorem)
        )));

    private static Formula PrefixStatement()
    {
        var f=V("f");var u=V("u");var rs=Call("records",D(0),f);var m=Call("occurrences",f);
        var place=V("place");var s=V("S");var no=V("F");var c=V("C");
        var statement=Imp(Call("Installed",c,place,s,no,rs),And(
            EqOf(Call("length",rs),m),EqOf(Call("map",V("fst"),rs),Call("range",m)),
            Call("Nonempty",Call("EvalsToInTime",Call("step",c,u),
                Call("resolve",place,s,no,Call("entry",D(0),f)),
                Call("some",Choose(Call("evaluate",f,u),s,no)),m))));
        statement=All("f",Call("Formula",V("n")),statement);
        statement=All("u",V("Source"),statement);
        statement=All("S,F",V("K"),statement);
        statement=All("place",Fn(V("Nat"),V("K")),statement);
        statement=All("C",Call("Controller",V("Q"),V("H")),statement);
        statement=All("Q,H",V("Type"),statement);
        return All("n",V("Nat"),statement);
    }
    private static Formula NativeStatement()
    {
        var f=V("f");var c=V("C");var s=V("S");var no=V("F");var u=V("u");
        var rs=V("rs");var dense=V("dense");var linked=V("linked");var m=V("M");
        var place=Call("placement",rs,no);var es=Call("embed",s);var ef=Call("embed",no);
        var preserved=All("q",V("Q"),And(
            EqOf(Call("addr",linked,Call("inr",V("q"))),Call("addr",c,V("q"))),
            All("r",V("Reply"),EqOf(Call("next",linked,Call("inr",V("q")),V("r")),
                Call("embed",Call("next",c,V("q"),V("r")))))));
        var outcome=Choose(Call("Conventional.evaluate",f,Call("sourceAssignment",f,u)),s,no);
        var statement=And(
            EqOf(Call("length",rs),m),EqOf(Call("map",V("fst"),rs),Call("range",Call("length",rs))),
            Call("Valid",Call("entry",D(0),dense),rs),Call("Injective",Call("slotMap",rs,no)),
            Call("Installed",linked,place,es,ef,rs),preserved,
            EqOf(Call("out",linked),Call("out",c)),
            Call("Nonempty",Call("EvalsToInTime",Call("step",linked,u),
                Call("resolve",place,es,ef,Call("entry",D(0),dense)),
                Call("some",Call("embed",outcome)),m)));
        statement=All("u",V("Source"),statement);
        statement=All("S,F",Call("Sum",V("Q"),V("H")),statement);
        statement=All("C",Call("Controller",V("Q"),V("H")),statement);
        statement=All("Q,H",V("Type"),statement);
        return All("f",V("Conventional.Formula"),statement);
    }
    private static Formula V(string n)=>Seq(n.Split('.').Select((word,i)=>
        i==0?F.Id(word):Seq(Dot,F.Id(word))).ToArray());
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] xs)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..xs]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula Fn(Formula a,Formula b)=>Seq(Par(a),Sp,To,Sp,b);
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] fs)=>Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula Choose(Formula p,Formula a,Formula b)=>Call("ite",p,a,b);
    private static Formula All(string names,Formula t,Formula body)=>Seq(Forall,Sp,
        Seq(names.Split(',').Select((n,i)=>i==0?V(n):Seq(Comma,Sp,V(n))).ToArray()),Colon,Sp,t,Comma,Sp,Par(body));
}
