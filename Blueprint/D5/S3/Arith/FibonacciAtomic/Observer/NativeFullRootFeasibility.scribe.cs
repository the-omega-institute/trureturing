using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFullRootFeasibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete predecessor-row feasibility on every actual origin equals finite root-experiment feasibility with the same payload capacity and fresh-call budget.",
        H("Native Full Root Feasibility"), Blocks(
            Paragraph(Text("Sources are arbitrary finite ordered Boolean trees. The substitution rho is the original alpha-to-beta and beta-to-pair(beta,alpha) map. P is any finite prefix-free cut. Choose one reference origin u0 solely to specify the fixed nonempty current row C=canonicalRow(P,rho(u0)); every nonempty actual current-row fiber admits such a reference. ImageValues(C), OriginFiber(P,C), appearing class names and Chart(C) are the exact full-fiber objects from NativeClassRootImage and NativeClassRootSimulation. Values and origins are coerced to their underlying values in the formulas. Filled(C,v) abbreviates evaluateRow(extend(C,v),C). A type is some(true), some(false), or none for alpha, beta, or branch. Classes are the occurring-label subtype, without a consecutive-label assumption. EmptyAddress denotes the empty address. FourReplyContinuation(A,B,E,D) sends alpha, beta, branch and absent to A, B, E and D respectively. In the theorem formula, let C binds the displayed fixed row.")),
            Entry("Stationary", "Stationary Actual Traces", "Stationarity excludes update events on actual terminating traces. The arbitrary control type, interpreter and all unreachable continuations remain unrestricted. Local steps may be arbitrarily numerous but finite on each reached run.", DescribeRole.Definition),
            Entry("VisibleAlpha", "Visible Alpha Roots", "Only a concrete alpha or a class with alpha root is a literal alpha. Ordered pairs are excluded. At a sibling of a reached cut, prefix freedom ensures this visible-root predicate agrees exactly with the actual current subtree being alpha.", DescribeRole.Definition),
            Entry("oldMask", "Occurrence-Sensitive Old Support", "The mask retains exactly those reached current occurrences that are not children of a parent with an alpha right child. A root cut has no final edge and is retained. Membership is tested per occurrence, so an old occurrence and a newborn occurrence may share one current equality class without either status being lost.", DescribeRole.Definition),
            Entry("target", "Whole Predecessor Target", "Back is the existing occurrence repair and opaque image parser. The target uses its decoded LiteralRow, with an alpha-row fallback. Every admissible type has a successful decoding, so the fallback never contributes on the task domain. The output retains all canonical restricted classes, equalities, disequalities, exterior constructors and predecessor absence guards.", DescribeRole.Definition),
            Entry("InvFeas", "Full Actual Stationary Reader Feasibility", "The ambient complete payload type S and control type K may be infinite. Sigma may depend on all acquired class values. Its actual complete range is explicitly finite and has cardinal at most r; a bare natural cardinal bound would admit infinite ranges and is not this definition. Entry is a function of the complete payload, with fixed common data already installed; it has no extra source-dependent argument. The same actual register rho(u) is used throughout each NativeSerialMachine.Run. Every actual origin and matching image valuation must terminate with the entire canonical predecessor row, with at most q read events. Repeated and absent queries count, local steps do not. Unreachable divergent behavior is permitted. Acquisition, authenticated continuity, complete export, lawful common entry and stationary access are supplied paid premises; this mathematical contract grants none of them.", DescribeRole.Definition),
            Entry("RootFeas", "Finite Joint Root Experiment Feasibility", "There is an inhabited finite alphabet S with at most r installed labels, a coloring of the exact admissible chart, and a finite three-reply experiment tree for each label. Every used tree has installed depth at most q and returns the whole target on all its colored types. Unused labels need no depth condition. Early halts and arbitrary impossible-edge outputs are allowed. At zero classes the tree type permits only stops.", DescribeRole.Definition),
            Entry("install", "Actual Representative-Address Installation", "Each query asks the original row-determined representative from NativeWholeRowPlan. The existing representative_subtree theorem proves that this address reaches its class value for every valuation, without an image or finite-source restriction. Its native reply is the class root. The absent edge immediately halts with common fallback data and is unreachable on every actual filling. Installation preserves the pair consisting of output and actual invocation count, and its native depth equals the root-tree depth.", DescribeRole.Definition),
            Entry("controller", "Common Native Dialogue Controller", "The complete accessible entry is the installed dialogue selected by the exported code. Stop returns its complete row. Read asks the stored address and continues according to the actual one of four replies. This deterministic controller performs no update.", DescribeRole.Definition),
            Entry("native_full_root_feasibility", "Complete Same-Capacity, Same-Budget Equivalence", "The statement contains the entire occurrence mask, successful whole-row factorization, successful decoding on every admissible type, actual representative subtree and reply laws, and the full joint-existence equivalence. For necessity, source-free finite replay to the next boundary supplies each reached local segment. Replay uniqueness makes its boundary independent of the witnessing source. A proof-only boundary selector uses an arbitrary common halt where no finite replay exists. Bounded recursive unrolling inspects Stop even at depth zero; induction on the original actual Run preserves its whole output and counted reads. A separate induction bounds every installed reply path by q, including unreachable paths. The actual used payload values form a finite subtype even if S is infinite. The existing truthful_joint_root_simulation takes the maximum query-word length of these finite dialogues, applies simultaneous actual padding, and compiles each constant or single-class reply. Its coloring uses the truthful full-value-dependent supplement of one fixed padded origin throughout that run. Whole-row factorization converts its predecessor output into the common type target. No supplement constancy on a root-type cell is assumed. For sufficiency, locally inspect the already acquired class roots and export the coloring. Exact chart attainment makes the actual export range equal to the used coloring range. Native installation invokes representatives on every actual source and preserves the counted path and installed depth. Whole-row decoding supplies the required predecessor output. Thus both directions use the same r and q. Empty, root and already-blocked cuts, zero classes and zero calls are included. The equivalence can change encoders within joint existence; it does not preserve an arbitrary fixed encoder. It is an existence proof from promised source-total termination, not extraction from program text. It imposes no source-size, finite-address, uniform-local-runtime, global-termination or total-controller-state bound, and establishes no full-trace or physical acquisition/export/isolation correspondence.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n,string h,string p,DescribeRole r) => Describe.Lean(
        DescribeId.Create("nativefullrootfeasibility-"+n.Replace("_","-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix+n),H(h),StatementSource.FromAuthor(Disp(Statement(n))),
        AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(p))),r);
    private static Formula Statement(string n)
    {
        var C=V("C"); var theta=V("theta"); var P=V("P"); var r=V("r"); var q=V("q");
        var v=V("v"); var u=V("u"); var d=V("d"); var a=V("a");
        var values=Call("ImageValues",C); var origins=Call("OriginFiber",P,C);
        var types=Call("types",C,v); var tree=Call("E",Call("c",theta));
        var sigma=Call("sigma",v);
        var actualRun=Some("t",V("Trace"),And(
            Call("Run",V("delta"),Call("entry",sigma),D(0),Call("rho",u),V("t"),Call("canonicalRow",P,u)),
            Call("Stationary",V("t")),LeOf(Call("length",Call("answers",V("t"))),q)));
        var inv=And(Call("Finite",Call("range",V("sigma"))),
            LeOf(Call("ncard",Call("range",V("sigma"))),r),
            All("v",values,All("u",origins,Imp(EqOf(Call("rho",u),Filled(C,v)),actualRun))));
        inv=Some("delta",Fn(V("K"),Call("Op",V("K"),V("LiteralRow"))),inv);
        inv=Some("entry",Fn(V("S"),V("K")),inv);
        inv=Some("sigma",Fn(values,V("S")),inv);
        inv=Some("S,K",V("Type"),inv);
        var root=And(LeOf(D(1),Call("card",V("S"))),LeOf(Call("card",V("S")),r),
            All("theta",Call("Chart",C),And(
                EqOf(Call("fst",Call("rootRun",theta,tree)),Call("target",C,theta)),
                LeOf(Call("rootDepth",tree),q))));
        root=Some("E",Fn(V("S"),Call("RootTree",C,V("LiteralRow"))),root);
        root=Some("c",Fn(Call("Chart",C),V("S")),root);
        root=Some("S",V("Type"),Seq(OpenBracket,Call("Fintype",V("S")),CloseBracket,Comma,Sp,root));
        var mask=Call("oldMask",C,types);
        var full=All("v",values,All("u",origins,Imp(EqOf(Call("rho",u),Filled(C,v)),And(
            EqOf(mask,Call("H",P,u)),EqOf(Call("back",C,mask),Call("some",Call("canonicalRow",P,u))),
            EqOf(Call("target",C,types),Call("canonicalRow",P,u))))));
        var decode=All("theta",Call("Chart",C),Some("row",V("LiteralRow"),
            EqOf(Call("back",C,Call("oldMask",C,theta)),Call("some",V("row")))));
        var representative=All("v",values,All("d",Call("Classes",C),And(
            EqOf(Call("subtree",Call("representative",C,d),Filled(C,v)),Call("some",Call("v",d))),
            EqOf(Call("readout",Call("representative",C,d),Filled(C,v)),Call("rootReply",Call("types",C,v,d))))));
        var visible=Some("e",V("LiteralRow"),And(
            EqOf(Call("rowAt",a,C),Call("some",V("e"))),
            Call("lit",Call("typeExtend",C,theta),V("true"),V("e"))));
        var newborn=Some("a",V("Address"),Some("d",V("Bool"),And(
            EqOf(V("p"),Call("append",a,Call("singleton",d))),
            Call("VisibleAlpha",C,theta,Call("append",a,Call("singleton",V("true")))))));
        var old=SetOf("p",V("Address"),And(
            Call("member",V("p"),Call("holeAddresses",V("emptyAddress"),C)),NegOf(newborn)));
        var installStop=All("o",V("LiteralRow"),EqOf(
            Call("install",C,V("fallback"),Call("stop",V("o"))),Call("stop",V("o"))));
        var installAsk=EqOf(Call("install",C,V("fallback"),Call("ask",d,V("A"),V("B"),V("E"))),
            Call("read",Call("representative",C,d),Installed(C,"A"),Installed(C,"B"),Installed(C,"E"),Call("stop",V("fallback"))));
        installAsk=All("d",Call("Classes",C),All("A,B,E",Call("RootTree",C,V("LiteralRow")),installAsk));
        var controlStop=All("o",V("LiteralRow"),EqOf(Call("controller",Call("stop",V("o"))),Call("stop",V("o"))));
        var controlRead=EqOf(Call("controller",Call("read",a,V("A"),V("B"),V("E"),V("D"))),
            Call("read",a,Call("fourReplyContinuation",V("A"),V("B"),V("E"),V("D"))));
        controlRead=All("a",V("Address"),All("A,B,E,D",Call("Dialogue",V("LiteralRow")),controlRead));
        var main=And(full,decode,representative,IffOf(Call("InvFeas",P,C,r,q),Call("RootFeas",C,r,q)));
        main=Seq(Operatorname,Grp(V("let")),Sp,C,Sp,Eq,Sp,Call("canonicalRow",P,Call("rho",V("u0"))),Comma,Sp,main);
        main=All("r,q",V("Nat"),Imp(LeOf(D(1),r),main));
        main=All("P",V("CutSet"),Imp(Call("CutPrefixFree",P),All("u0",V("Source"),main)));
        return n switch {
            "Stationary" => All("t",V("Trace"),IffOf(Call("Stationary",V("t")),
                All("n",V("Nat"),NegOf(Call("member",Call("update",V("n")),V("t")))))),
            "VisibleAlpha" => All("C",V("LiteralRow"),All("theta",Assignment(C),All("a",V("Address"),
                IffOf(Call("VisibleAlpha",C,theta,a),visible)))),
            "oldMask" => All("C",V("LiteralRow"),All("theta",Assignment(C),EqOf(Call("oldMask",C,theta),old))),
            "target" => All("C",V("LiteralRow"),All("theta",Assignment(C),EqOf(Call("target",C,theta),
                Call("getD",Call("back",C,Call("oldMask",C,theta)),Call("of",Call("inl",V("true"))))))),
            "InvFeas" => All("P",V("CutSet"),All("C",V("LiteralRow"),All("r,q",V("Nat"),
                IffOf(Call("InvFeas",P,C,r,q),inv)))),
            "RootFeas" => All("C",V("LiteralRow"),All("r,q",V("Nat"),IffOf(Call("RootFeas",C,r,q),root))),
            "install" => All("C",V("LiteralRow"),All("fallback",V("LiteralRow"),And(installStop,installAsk))),
            "controller" => And(controlStop,controlRead),
            "native_full_root_feasibility" => main,
            _ => throw new System.ArgumentOutOfRangeException(nameof(n))
        };
    }
    private static Formula Installed(Formula c,string n) => Call("install",c,V("fallback"),V(n));
    private static Formula Filled(Formula c,Formula v) => Call("evaluateRow",Call("extend",c,v),c);
    private static Formula Assignment(Formula c) => Fn(Call("Classes",c),Call("Option",V("Bool")));
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Fn(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula IffOf(Formula a,Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula NegOf(Formula a) => Seq(Neg,Sp,Par(a));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Names(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,Names(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Names(string n) => Seq(n.Split(',').Select((x,i)=>i==0?V(x):Seq(Comma,Sp,V(x))).ToArray());
    private static Formula SetOf(string n,Formula t,Formula b) => Seq(OpenBrace,V(n),Colon,Sp,t,Sp,Vert,Sp,b,CloseBrace);
}
