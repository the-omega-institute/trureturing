using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeControlConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeControlConjugacy", H("NativeControlConjugacy"), Blocks(
            Paragraph(Text("The native interpreter carries a complete control, an update epoch, one actual Source, and an appended chronological Event list. A control equivalence changes only the complete control. mapOp preserves localStep, the entire Read literal and reply continuation, applyRho, and the fixed Stop payload. reindex decodes an installed control through the inverse equivalence and applies this instruction map. mapConfig leaves the epoch, actual source and full log untouched.")),
            Paragraph(Text("advance is nativeStep on an optional configuration and keeps none absorbing. Its n-fold iteration counts n chronological actions, including all root Reads. Remaining means that an actual finite Run reaches its first Stop after exactly n actions. The interpreter is deterministic: two terminating runs from the same control, epoch and actual source have the same event list and payload.")),
            Paragraph(Text("CostModel assigns a cost to each complete address, each raw Read response and the constant Update acknowledgement. Its five coordinates are primitive calls, Reads, Updates, address costs and response costs. Each Read contributes one primitive and one Read; each Update contributes one primitive and one Update. localStep contributes zero to these five primitive coordinates while remaining in the event trace. In a program with zero internal actions, remaining actions and remaining primitives agree. No absolute application-specific bill is asserted.")),
            Describe.Lean(DescribeId.Create("native-control-conjugacy"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeControlConjugacy.native_control_conjugacy"),
                H("Exact native conjugacy"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on the actual finite Run preserves every event and the Stop payload. A separate one-step calculation preserves the source successor and appended event. Equal-step iteration gives exact finite prefixes, including empty reachability fibers. The inverse control equivalence supplies both implications. NativeSerialDepth.run_unique compares any two terminating runs from the same control, epoch and source. Applying that result after inverse run transport gives equality of the chronological traces and fixed halt payloads, and hence equality of all five charged coordinates even when the two traces are supplied independently."))), DescribeRole.Theorem))));

    private static Formula Statement() {
        var C=V("C"); var E=V("E"); var O=V("O"); var e=V("e"); var f=V("f");
        var c=V("c"); var j=V("j"); var u=V("u"); var t=V("t"); var s=V("s");
        var o=V("o"); var b=V("b"); var x=V("x"); var y=V("y"); var n=V("n");
        var m=V("m"); var i=V("i"); var g=Call("reindex",e,f);
        Formula Run(Formula prog,Formula control,Formula trace,Formula output) =>
            Call("Run",prog,control,j,u,trace,output);
        Formula Bind(Formula z,bool two=false,bool model=false) {
            if(model) z=All("m",V("CostModel"),z);
            if(two) z=All("b",O,z);
            z=All("o",O,z);
            if(two) z=All("s",V("Trace"),z);
            z=All("t",V("Trace"),z);
            return All("c",C,All("j",V("Nat"),All("u",V("Source"),z)));
        }
        var rows=All("c",C,Eq(Call("reindex",e,f,Call("e",c)),Call("mapOp",e,Call("f",c))));
        var steps=All("x",Call("Config",C),Eq(Call("nativeStep",g,Call("mapConfig",e,x)),
            Call("map",Call("nativeStep",f,x),Call("mapConfig",e))));
        Formula Iter(Formula prog,Formula z) => Call("iterate",Call("advance",prog),n,Call("some",z));
        var prefixes=All("x",Call("Config",C),All("y",Call("Config",C),All("n",V("Nat"),
            IffOf(Eq(Iter(g,Call("mapConfig",e,x)),Call("some",Call("mapConfig",e,y))),
                Eq(Iter(f,x),Call("some",y))))));
        var halt=All("c",C,All("o",O,IffOf(Eq(Call("reindex",e,f,Call("e",c)),Call("stop",o)),Eq(Call("f",c),Call("stop",o)))));
        var remaining=All("c",C,All("j",V("Nat"),All("u",V("Source"),All("n",V("Nat"),All("o",O,
            IffOf(Call("Remaining",g,Call("e",c),j,u,n,o),Call("Remaining",f,c,j,u,n,o)))))));
        var result=And(rows,steps,Bind(IffOf(Run(g,Call("e",c),t,o),Run(f,c,t,o))),prefixes,halt,remaining,
            Bind(Imp(Run(f,c,t,o),Imp(Run(f,c,s,b),And(Eq(t,s),Eq(o,b)))),true),
            Bind(Imp(Run(f,c,t,o),Imp(Run(g,Call("e",c),s,b),And(Eq(t,s),Eq(o,b),
                All("i",Call("Fin",D(5)),Eq(Call("cost",m,t,i),Call("cost",m,s,i)))))),true,true));
        return All("C",V("Type"),All("E",V("Type"),All("O",V("Type"),All("e",Call("Equiv",C,E),
            All("f",Arr(C,Call("Op",C,O)),result)))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] xs) {
        var r = xs[^1];
        for (int i = xs.Length-2; i >= 0; --i) r = Seq(Par(xs[i]), Sp, Land, Sp, Par(r));
        return r;
    }
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
