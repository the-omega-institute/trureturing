using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiveHoleCompilerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFiveHoleCompiler", H("Exact finite compilation of whole five-hole strata"), Blocks(
            Describe.Lean(DescribeId.Create("five-hole-negatives"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.Negatives"), H("The entire finite negative table"),
                StatementSource.FromAuthor(Disp(All("s",Bool,All("H",Hist,All("t",Arr(Call("Fin",D(2)),Source),IffOf(Call("Negatives",V("s"),V("H"),V("t")),All("e",Call("Prod",V("Expr"),V("Expr")),Imp(Mem(V("e"),Call("table",V("s"),V("H"))),NeOf(Call("rankedEval",Call("ranks"),V("t"),Call("fst",V("e"))),Call("rankedEval",Call("ranks"),V("t"),Call("snd",V("e")))))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Expr is RankedExpr with zero ranks and two shared residual names Y,Z. FY and FZ pair the ground alpha with the corresponding residual at exponent one. The false side orders Y,Z,FY,FZ; the true side orders FY,Y,Z,FZ. Six contains comparisons (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). Table then appends every occurrence of IndexedHistory, in its original order, shifting each corresponding hole expression by its supplied epoch. No repeated or redundant comparison is removed.")),
                    Paragraph(Text("Shift transforms ground alpha as well as adding the residual exponent. The existing eval_shift supplies its evaluation law. The true-side conjunction explicitly permutes all six inequalities, reversing the necessary comparisons."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-stratum-compile-iff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.stratum_compile_iff"), H("Exact compilation on the original whole strata"),
                StatementSource.FromAuthor(Disp(All("s",Bool,All("H",Hist,All("u",Source,IffOf(Call("Stratum",V("s"),V("H"),V("u")),Some("t",Arr(Call("Fin",D(2)),Source),AndOf(EqOf(V("u"),Call("source",V("s"),Call("t",D(0)),Call("t",D(1)))),Call("Negatives",V("s"),V("H"),V("t")))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Both directions start with the original Stratum. Raw-source extraction and full-label correspondence precede the compiler. Epoch-hole transport retains both guards, while exact list reconstruction preserves every original negative record."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-hole-separator-exact"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler.separator_exact"), H("One finite structural test decides the entire table"),
                StatementSource.FromAuthor(Disp(All("s",Bool,All("H",Hist,IffOf(Call("Negatives",V("s"),V("H"),Call("uniformSeparator",Call("table",V("s"),V("H")))),Some("t",Arr(Call("Fin",D(2)),Source),Call("Negatives",V("s"),V("H"),V("t")))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Uniform residual reflection makes every equality at the computed separator universal over all residual tuples. A failed comparison therefore excludes the whole stratum; a passing separator is an explicit finite seed for all its negatives. This finite test concerns these exact tables and asserts no general NSF solver."))), DescribeRole.Theorem)
        )));

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Mem(Formula a, Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula AndOf(params Formula[] xs) => xs.Length == 1 ? xs[0] :
        Seq(Par(xs[0]),Sp,Land,Sp,Par(AndOf(xs.Skip(1).ToArray())));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Source => V("Source");
    private static Formula Bool => V("Bool");
    private static Formula Hist => V("History");
}
