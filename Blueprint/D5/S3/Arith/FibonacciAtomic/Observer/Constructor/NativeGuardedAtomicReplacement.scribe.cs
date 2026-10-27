using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeGuardedAtomicReplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeGuardedAtomicReplacement", H("Bounded atomic terminals survive simultaneous free-value replacement"), Blocks(
            Describe.Lean(DescribeId.Create("native-guarded-atomic-replacement"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedAtomicReplacement.atomic_replacement"),
                H("Small finite atomic results depend only on small atomic free values"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Use the actual unrestricted native completion, the distributed expressions and the optional guarded definitions of NativeGuardedFreeExtension. Fix one system S, one natural parameter tuple p and two simultaneous solutions v and w of all of its defining equations. They may differ at finite or arbitrary infinite values. The natural bound B imposes no restriction on either full solution or its state values.")),
                    Paragraph(Text("Assume only that, whenever an undefined state has value atomic(j) in v with j at most B, its value in w is unchanged. Then every expression E whose value in v is atomic(j) with j at most B has that same value in w. This includes reconstruction expressions and repeated occurrences of states. Parameters, finite grounds, Omega, nonnegative decorators and ordered pairs have their actual native meanings in both evaluations.")),
                    Paragraph(Text("An actual power rho(a,X) equal to atomic(j) has a unique finite atomic predecessor atomic(l), with l+a=j. Native finiteness reflection first makes X finite. The invariant gamma of its finite source is zero, so the existing atomic-rank classification identifies the source as atomic. Injectivity and composition of native iterates give the exact index equation. In particular the predecessor rank cannot exceed j.")),
                    Paragraph(Text("A pair equal to atomic(j) has j=n+2 and children atomic(n+1) and atomic(n). Expression induction therefore propagates atomic bounds through the explicit pair skeleton and its decorated state occurrences. To compare states satisfying definitions, strong induction on the terminal rank unfolds their guarded defining right sides. A pair root strictly reduces the rank before any state dependency is compared. Constants are unchanged, and undefined states use the stated hypothesis. Thus an infinite recursive dependency cannot be hidden in a finite atomic terminal.")),
                    Paragraph(Text("For a saturation mode with exceptional atoms through S+1, take B=S+1. A live free value lies outside that finite set, so it cannot occur in a dependency responsible for any accepted image terminal of threshold at most S. Replacing live free values by Omega therefore preserves each such terminal. This theorem supplies terminal preservation; acceptance of infinite recursive image parses requires the separate actual-image coinduction argument."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k=V("k"); var m=V("m"); var s=V("S"); var p=V("p");
        var v=V("v"); var w=V("w"); var b=V("B"); var i=V("i"); var j=V("j"); var e=V("E");
        var tuple=Arr(Call("Fin",m),V("CompletionTree"));
        var free=All("i",Call("Fin",m),Imp(EqOf(Call("at",s,i),V("none")),
            All("j",V("Nat"),Imp(LeOf(j,b),Imp(EqOf(Call("at",v,i),Call("atomic",j)),
                EqOf(Call("at",w,i),Call("at",v,i)))))));
        var conclusion=All("E",Call("Expression",k,m),All("j",V("Nat"),Imp(LeOf(j,b),
            Imp(EqOf(Call("evaluate",p,v,e),Call("atomic",j)),
                EqOf(Call("evaluate",p,w,e),Call("evaluate",p,v,e))))));
        return StatementSource.FromAuthor(Disp(All("k",V("Nat"),All("m",V("Nat"),
            All("S",Call("System",k,m),All("p",Arr(Call("Fin",k),V("Nat")),
                Imp(Call("Guarded",s),All("v",tuple,All("w",tuple,
                    Imp(Call("Satisfies",s,p,v),Imp(Call("Satisfies",s,p,w),
                        All("B",V("Nat"),Imp(free,conclusion))))))))))));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b)=>Seq(a,Sp,Le,Sp,b);
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
