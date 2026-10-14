using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeClassRootSimulationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native dialogues compile to legal class-root experiments on truthful fixed actual representatives.",
        H("Native Class Root Simulation"), Blocks(
            Paragraph(Text("Sources are finite ordered Boolean trees and rho is the original substitution. For a finite prefix-free cut P and source T, let C=canonicalRow(P,T). ImageValues(C) contains every injective class valuation whose filled complete row is an actual image; OriginFiber(P,C) contains every finite origin with complete current row C. Types take the values some(true), some(false), and none for alpha, beta, and branch. Chart(C) is the set of admissible assignments. Dialogue is the existing finite four-reply native reader tree with complete row outputs. The notation replies(t) means the function a ↦ readout(a,t); valuations and origins are coerced to their underlying values in formulas.")),
            Entry("RootTree", "Legal Three-Reply Experiment Trees", "A root tree has a complete output at a stop and exactly three continuations at a query of an appearing class. There is no absent root reply and no query constructor when the class set is empty.", DescribeRole.Definition),
            Entry("nativeRun", "Stationary Native Execution", "Execution follows the actual alpha, beta, branch, or absent continuation. The pair records the terminal output and invocation count; increment(o,n)=(o,n+1). The register reply function stays fixed; every visited read counts once, including repeats and absences.", DescribeRole.Definition),
            Entry("rootRun", "Joint Root Execution", "Execution follows the same unchanged joint assignment at every vertex. The function chooseRoot selects the alpha, beta, or branch child for some(true), some(false), or none. Every visited class query counts once. Early stops use no invocation.", DescribeRole.Definition),
            Entry("nativeDepth", "Native Path Budget", "The depth is zero at a stop and one plus the maximum depth of the four children at a read.", DescribeRole.Definition),
            Entry("rootDepth", "Experiment Path Budget", "The depth is zero at a stop and one plus the maximum depth of the three children at a class experiment.", DescribeRole.Definition),
            Entry("wordBound", "Finite Native Word Bound", "The maximum ranges over all installed query words, including unrealized edges. A stop contributes zero. This is a bound on this one finite comparator, not on source size.", DescribeRole.Definition),
            Entry("compileRoot", "Exterior Navigation and Experiment Compilation", "The exterior is traversed to its first class hole, if any. A fixed exterior reply selects one compiled continuation without a class experiment. A hole yields one legal appearing class d and a Boolean b recording whether the remaining suffix is nonempty. When b is false, the class constructor selects the matching native continuation. When b is true, either leaf selects absent and a branch selects branch. Repeated questions remain distinct charged vertices. The symbols firstClass, classReply and choose denote these structural operations; choose(y,A,B,E,D) selects the four-reply child.", DescribeRole.Definition),
            Entry("Chart", "Exactly Attained Joint Types", "Admissibility uses the complete exterior image grammar and the separate multiplicity bounds on the two literal leaf classes. The actual class-root image theorem identifies this chart with exactly the attained types.", DescribeRole.Definition),
            Entry("truthful_joint_root_simulation", "Truthful Joint Simulation on Actual Origins", "Fix an arbitrary finite supplement alphabet S, a supplement sigma depending on the complete acquired valuation, and one finite native dialogue E(s) per value. Assume every installed dialogue has depth at most q and gives the complete predecessor row on every matching actual valuation and origin. There is one fixed actual origin u(theta), one injective image valuation v(theta), and its truthful exported value c(theta)=sigma(v(theta)) for every admissible joint type. The compiled tree returns that origin's entire canonical predecessor row, uses no more calls than its native run, and has depth at most q. To obtain a common finite word bound, take the maximum over all installed dialogues. Apply actual image padding at that bound, then induct through each dialogue using structural exterior navigation. Each vertex is constant or depends on exactly one appearing class, so zero or one class experiment reproduces its native reply on that same padded image. The supplement alphabet is retained unchanged. No assertion says that sigma is constant on all sources of one type. The result covers arbitrary addresses, repeated calls, blocking absences, zero queries, root cuts, empty cuts and zero classes. It is the finite-dialogue simulation needed for the necessity direction of the joint feasibility correspondence. The general source-total reader unrolling, full predecessor factorization through types, reverse native implementation and complete feasibility equivalence are separate obligations. No source reconstruction chart, physical resource equivalence, acquisition permission or controller-state bound follows.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n, string h, string p, DescribeRole r) => Describe.Lean(
        DescribeId.Create("nativeclassrootsimulation-"+n.Replace("_","-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix+n), H(h), StatementSource.FromAuthor(Statement(n)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(p))), r);
    private static Formula Statement(string n)
    {
        var C=V("C"); var O=V("O"); var f=V("f"); var theta=V("theta");
        var a=V("a"); var d=V("d"); var o=V("o");
        var A=V("A"); var B=V("B"); var E=V("E"); var Dd=V("D");
        var stop=Call("stop",o); var read=Call("read",a,A,B,E,Dd); var ask=Call("ask",d,A,B,E);
        Formula Types(Formula body) => All("C",V("LiteralRow"),All("O",V("Type"),body));
        Formula Native(Formula body) => All("O",V("Type"),body);
        Formula Inputs(bool root,Formula body) => root ? All("d",Call("Classes",C),Trees("O",true,body)) : All("a",V("Address"),Trees("O",false,body));
        var rt=RT(C,O);
        var rootTreeFormula=Types(And(Seq(Call("stop"),Colon,Sp,Fn(O,rt)),
            Seq(Call("ask"),Colon,Sp,Fn(Call("Classes",C),Fn(rt,Fn(rt,Fn(rt,rt)))))));
        var nativeRunFormula=Native(All("f",Fn(V("Address"),V("Reply")),And(
            All("o",O,EqOf(Call("nativeRun",f,stop),Pair(o,D(0)))),
            Inputs(false,EqOf(Call("nativeRun",f,read),Call("increment",Call("nativeRun",f,Call("choose",Call("f",a),A,B,E,Dd))))))));
        var rootRunFormula=Types(All("theta",Assignment(C),And(
            All("o",O,EqOf(Call("rootRun",theta,stop),Pair(o,D(0)))),
            Inputs(true,EqOf(Call("rootRun",theta,ask),Call("increment",Call("rootRun",theta,Call("chooseRoot",Call("theta",d),A,B,E))))))));
        var nativeDepthFormula=Native(And(All("o",O,EqOf(Call("nativeDepth",stop),D(0))),
            Inputs(false,EqOf(Call("nativeDepth",read),Add(Call("max",Call("nativeDepth",A),Call("nativeDepth",B),Call("nativeDepth",E),Call("nativeDepth",Dd)),D(1))))));
        var rootDepthFormula=Types(And(All("o",O,EqOf(Call("rootDepth",stop),D(0))),
            Inputs(true,EqOf(Call("rootDepth",ask),Add(Call("max",Call("rootDepth",A),Call("rootDepth",B),Call("rootDepth",E)),D(1))))));
        var wordBoundFormula=Native(And(All("o",O,EqOf(Call("wordBound",stop),D(0))),
            Inputs(false,EqOf(Call("wordBound",read),Call("max",Call("length",a),Call("wordBound",A),Call("wordBound",B),Call("wordBound",E),Call("wordBound",Dd))))));
        var y=V("y"); var b=V("b");
        var constant=All("y",V("Reply"),Imp(EqOf(Call("firstClass",C,a),Call("inl",y)),EqOf(Call("compileRoot",C,read),CompChild(y))));
        var experiment=All("d",Call("Classes",C),All("b",V("Bool"),
            Imp(EqOf(Call("firstClass",C,a),Call("inr",Pair(d,b))),
                EqOf(Call("compileRoot",C,read),Call("ask",d,
                    CompChild(Call("classReply",b,Call("some",V("true")))),
                    CompChild(Call("classReply",b,Call("some",V("false")))),
                    CompChild(Call("classReply",b,V("none"))))))));
        var compileFormula=Types(And(All("o",O,EqOf(Call("compileRoot",C,stop),stop)),Inputs(false,And(constant,experiment))));
        var chartFormula=All("C",V("LiteralRow"),EqOf(Call("Chart",C),Seq(OpenBrace,theta,Colon,Sp,Assignment(C),Sp,Vert,Sp,Call("Admissible",C,theta),CloseBrace)));
        return n switch {
            "RootTree" => rootTreeFormula,
            "nativeRun" => nativeRunFormula,
            "rootRun" => rootRunFormula,
            "nativeDepth" => nativeDepthFormula,
            "rootDepth" => rootDepthFormula,
            "wordBound" => wordBoundFormula,
            "compileRoot" => compileFormula,
            "Chart" => chartFormula,
            "truthful_joint_root_simulation" => JointStatement(),
            _ => throw new System.ArgumentOutOfRangeException(nameof(n))
        };
    }
    private static Formula JointStatement()
    {
        var C=Call("canonicalRow",V("P"),V("T"));
        Formula Img(Formula v) => Call("evaluateRow",Call("extend",C,v),C);
        Formula Run(Formula u,Formula e) => Call("nativeRun",Call("replies",Call("rho",u)),e);
        var chart=Call("Chart",C); var values=Call("ImageValues",C); var origins=Call("OriginFiber",V("P"),C);
        var tree=Call("compileRoot",C,Call("E",Call("c",V("theta"))));
        var result=Some("v",Fn(chart,values),Some("u",Fn(chart,origins),Some("c",Fn(chart,V("S")),All("theta",chart,And(
            EqOf(Call("rho",Call("u",V("theta"))),Img(Call("v",V("theta")))),
            EqOf(Call("types",C,Call("v",V("theta"))),V("theta")),
            EqOf(Call("c",V("theta")),Call("sigma",Call("v",V("theta")))),
            EqOf(Call("fst",Call("rootRun",V("theta"),tree)),Call("canonicalRow",V("P"),Call("u",V("theta")))),
            LeOf(Call("snd",Call("rootRun",V("theta"),tree)),Call("snd",Run(Call("u",V("theta")),Call("E",Call("sigma",Call("v",V("theta"))))))),
            LeOf(Call("rootDepth",tree),V("q")))))));
        var correct=All("w",values,All("z",origins,Imp(EqOf(Call("rho",V("z")),Img(V("w"))),
            EqOf(Call("fst",Run(V("z"),Call("E",Call("sigma",V("w"))))),Call("canonicalRow",V("P"),V("z"))))));
        return All("P",V("CutSet"),Imp(Call("CutPrefixFree",V("P")),All("T",V("Source"),All("S",V("Type"),
            Seq(OpenBracket,Call("Finite",V("S")),CloseBracket,Sp,
                All("sigma",Fn(values,V("S")),All("E",Fn(V("S"),Call("Dialogue",V("LiteralRow"))),All("q",V("Nat"),
                    Imp(And(All("s",V("S"),LeOf(Call("nativeDepth",Call("E",V("s"))),V("q"))),correct),result)))))))));
    }
    private static Formula Trees(string output,bool root,Formula body)
    {
        var type=root?RT(V("C"),V(output)):Call("Dialogue",V(output));
        return All("A",type,All("B",type,All("E",type,root?body:All("D",type,body))));
    }
    private static Formula CompChild(Formula y) => Call("compileRoot",V("C"),Call("choose",y,V("A"),V("B"),V("E"),V("D")));
    private static Formula Assignment(Formula c) => Fn(Call("Classes",c),Call("Option",V("Bool")));
    private static Formula RT(Formula c,Formula o) => Call("RootTree",c,o);
    private static Formula Pair(Formula a,Formula b) => Seq(Open,a,Comma,Sp,b,Close);
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Fn(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Add(Formula a,Formula b) => Seq(a,Sp,Plus,Sp,b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
