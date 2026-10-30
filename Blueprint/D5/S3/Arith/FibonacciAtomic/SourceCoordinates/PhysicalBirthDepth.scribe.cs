using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class PhysicalBirthDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete depths recover physical branch orientations above the terminal two-child boundary.",
        H("Physical Births and Observable Orientations"), Blocks(
            Paragraph(Text("The physical ports persist: false is a and true is b. A label true is alpha, "
                + "and false is beta. Descriptor(born,initial) stores immutable creation data. "
                + "Birth(time,index,bit) stores the branch update, positive global birth index and "
                + "actual stream bit. In the formulas snapshot(z,n) means (orbit z n).1; source "
                + "forgets metadata but retains physical child order and current terminal labels. "
                + "born and initial project a descriptor; bit, time and index project a birth. "
                + "shape(U) means decompose(U).1. select(c,A,B) returns A for true and B for false. "
                + "apply(z,j) is the stream value z(j), and negate is Boolean negation. Natural subtraction is truncated. No descriptor, rank or prefix is an extra observer readout.")),
            Def("Descriptor", "Immutable creation descriptor", "born is the creation update, and initial "
                + "is the label at creation, retained even after an alpha leaf becomes beta."),
            Def("Birth", "Actual branch event", "time is the update when an old beta branches; index "
                + "is its global one-based event index and bit is the consumed stream value."),
            Def("Physical", "Physical finite tree", "A leaf stores its descriptor and current label. "
                + "A branch stores its original descriptor, its birth event and its ordered a and b children."),
            Def("Physical.descriptor", "Persistent root metadata", "Both constructors expose the original "
                + "descriptor of this same physical node."),
            Def("Physical.source", "Existing ordered source", "A physical leaf becomes the existing Source.of "
                + "of its current label. A branch becomes Source.mul of its a and b children in that order."),
            Def("update", "Simultaneous old-leaf update", "The recursion visits only the input tree. "
                + "Old alpha becomes beta without consuming a bit. Old beta consumes z(j+1), increments "
                + "the counter and creates beta at a exactly when that bit is true. Both new descriptors "
                + "have born=time and their actual initial labels. Newborns are returned without further "
                + "recursion. Old branches and their metadata persist. Their a subtree is updated first, "
                + "then b with the returned counter, so beta events follow physical lexicographic order."),
            Def("orbit", "Alpha-origin physical orbit", "At cut zero the tree is a single alpha with "
                + "descriptor (0,true) and counter zero. Cut n+1 applies update z (n+1) to the complete "
                + "previous tree and its global counter. This quantifies every stream, with no law on z."),
            Def("Physical.at", "Literal reached cone", "Lookup follows the original physical Boolean "
                + "address; the empty address returns the whole tree and a nonempty suffix crossing a "
                + "leaf returns none. The returned subtree keeps every descriptor and branch event."),
            Def("rank", "Descriptor rank", "rank(n,T)=n-born(descriptor(T))+indicator(initial(T)=false). "
                + "The theorem derives this rank from the actual old-leaf orbit, rather than assuming "
                + "a desired chronology or identifying physical order with a fixed semantic substitution."),
            Describe.Lean(DescribeId.Create("physical-birth-depth-maximum"),
                DeclarationHandle.Create(Prefix + "DepthMaximum"), H("Complete-function maximum"),
                StatementSource.FromAuthor(Disp(MaximumDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bound on the entire tape cube and an attained value at that same "
                    + "horizon. No descriptors or labels are arguments of the observed tape function."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-birth-depth-beats"),
                DeclarationHandle.Create(Prefix + "Beats"), H("Depth-only comparison"),
                StatementSource.FromAuthor(Disp(BeatsDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is one left tape whose depth exceeds every right-tape depth. "
                    + "At a sufficient horizon this compares the two attained maxima using depth only."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-birth-depth-root-beats"),
                DeclarationHandle.Create(Prefix + "RootBeats"), H("Full-root depth comparison"),
                StatementSource.FromAuthor(Disp(RootBeatsDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This comparison uses only values of the same full-root depth "
                    + "function on tapes with the fixed physical prefix p followed by a or b. "
                    + "cons(c,u) prepends the direction c; append retains the complete root literal."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-birth-depth-cone-law"),
                DeclarationHandle.Create(Prefix + "ConeLaw"), H("Whole reached-cone law"),
                StatementSource.FromAuthor(Disp(ConeDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed law includes every horizon, padding word, reached "
                    + "prefix and branch. Its q is the displayed descriptor-rank abbreviation. The "
                    + "root-offset clause uses H=2n-1 for every n at least two; a tape u has length H-|p| "
                    + "and v has length |p|, hence both root and padded local tapes have length H. "
                    + "The unrestricted prefix identity also gives the local restriction by subtracting |p|.")),
                    Paragraph(Text("At every sufficient local horizon the paid derivation uses the same "
                        + "full root and all operands are absolute literals. Its number of tests is depth+1, "
                        + "including the final absence test with an empty remaining direction list. "
                        + "Run is the existing native serial Run of the source-blind tape controller; its "
                        + "eventTrace consists exactly of these stationary full-root Read events. "
                        + "Using this mathematical presence service requires the original binding, grants, "
                        + "backing, completed serial reads and stationarity premises.")),
                    Paragraph(Text("The comparison source U is any finite ordered labelled tree with the "
                        + "same sufficient tape horizon. Equality of complete depths identifies its ordered "
                        + "unlabelled terminal/branch shape. Labels themselves are not recovered. "
                        + "At rank three the ordered high/low maxima are one and zero; at rank two both "
                        + "children are terminal, every nonempty local tape has depth one and exchanging "
                        + "the two terminal labels preserves every depth. This last statement concerns "
                        + "depth observations only and asserts no equivalence of future observations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-birth-depth-observable-orientations"),
                DeclarationHandle.Create(Prefix + "observable_orientations"),
                H("Observable physical orientations"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A ranked tree is constructed alongside the actual alpha-origin orbit. "
                        + "The construction threads the same global counter in physical a-before-b order; "
                        + "its erasure is proved equal to the original update. Its invariant retains "
                        + "immutable creation times, initial labels and the actual z(index) birth bit. "
                        + "Induction gives ranks n-born+indicator(initial beta), physical child ranks "
                        + "q-1,q-2 and height q-1 with truncated subtraction. Reached-prefix induction "
                        + "pays the remaining-horizon margin at every physical address.")),
                    Paragraph(Text("The complete tape geometry theorem supplies paid walks, padding, "
                        + "attained maxima and prefix offsets. Its label-erased frontier argument uses "
                        + "the existing source_foundation rigidity theorem to recover ordered shape. "
                        + "The derived physical child heights then compare attained maxima and recover "
                        + "the actual stored stream bit for every rank at least three. No reconstruction, "
                        + "child margin or chronology appears as an extra hypothesis."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("physical-birth-depth-" + name.Replace(".", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] x) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. x]);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) =>
        Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] x) => Seq(x.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, RowBreak, Par(f))).ToArray());
    private static Formula Len(Formula u) => Call("length", u);
    private static Formula Src(Formula t) => Call("source", t);
    private static Formula Ht(Formula t) => Call("height", t);
    private static Formula Dp(Formula t, Formula u) => Call("depth", t, u);
    private static Formula App(Formula a, Formula b) => Call("append", a, b);
    private static Formula High(Formula e, Formula a, Formula b) => Call("select",Call("bit",e),a,b);
    private static Formula MaximumDefinition()
    {
        var t=V("T"); var l=V("L"); var m=V("m"); var u=V("u");
        return All("T",V("Source"),All("L",V("Nat"),All("m",V("Nat"),IffOf(
            Call("DepthMaximum",t,l,m),And(
                All("u",V("Address"),Imp(EqOf(Len(u),l),LeOf(Dp(t,u),m))),
                Some("u",V("Address"),And(EqOf(Len(u),l),EqOf(Dp(t,u),m))))))));
    }
    private static Formula BeatsDefinition()
    {
        var a=V("A"); var b=V("B"); var l=V("L"); var u=V("u"); var v=V("v");
        return All("A",V("Source"),All("B",V("Source"),All("L",V("Nat"),IffOf(
            Call("Beats",a,b,l),Some("u",V("Address"),And(EqOf(Len(u),l),
                All("v",V("Address"),Imp(EqOf(Len(v),l),LtOf(Dp(b,v),Dp(a,u))))))))));
    }
    private static Formula RootBeatsDefinition()
    {
        var t=V("T"); var p=V("p"); var l=V("L"); var u=V("u"); var v=V("v");
        var comparison=Some("u",V("Address"),And(EqOf(Len(u),l),
            All("v",V("Address"),Imp(EqOf(Len(v),l),LtOf(
                Dp(t,App(p,Call("cons",V("true"),v))),Dp(t,App(p,Call("cons",V("false"),u))))))));
        return All("T",V("Source"),All("p",V("Address"),All("L",V("Nat"),
            IffOf(Call("RootBeats",t,p,l),comparison))));
    }
    private static Formula ConeDefinition()
    {
        var n=V("n"); var z=V("z"); var p=V("p"); var t=V("T");
        return All("n",V("Nat"),All("z",Seq(V("Nat"),Sp,To,Sp,V("Bool")),
            All("p",V("Address"),All("T",V("Physical"),IffOf(Call("ConeLaw",n,z,p,t),Cone(n,z,p,t))))));
    }
    private static Formula Cone(Formula n, Formula z, Formula p, Formula t)
    {
        var q=Call("rank",n,t); var st=Src(t); var root=Src(Call("snapshot",z,n));
        var u=V("u"); var v=V("v"); var l=V("L"); var a=V("A"); var d=V("d"); var c=V("c");
        var address=V("Address"); var nat=V("Nat"); var qm=Sub(q,D(1));
        var hn=Sub(Seq(D(2),Sp,Times,Sp,n),D(1));
        return And(
            LeOf(Call("born",Call("descriptor",t)),n), LeOf(Add(q,Len(p)),n), EqOf(Ht(st),qm),
            IffOf(LeOf(q,D(1)),Some("d",V("Descriptor"),Some("c",V("Bool"),EqOf(t,Call("leaf",d,c))))),
            All("u",address,LeOf(Dp(st,u),qm)),
            All("L",nat,Imp(LeOf(qm,l),Call("DepthMaximum",st,l,qm))),
            All("u",address,Imp(LeOf(qm,Len(u)),And(
                Call("PaidWalk",root,p,u,Call("probes",st,p,u),Dp(st,u)),
                EqOf(Len(Call("probes",st,p,u)),Add(Dp(st,u),D(1))),
                Call("Run",V("controller"),Call("walk",p,u,D(0)),n,root,
                    Call("eventTrace",n,root,Call("probes",st,p,u)),Dp(st,u))))),
            All("u",address,All("v",address,Imp(LeOf(qm,Len(u)),EqOf(Dp(st,App(u,v)),Dp(st,u))))),
            All("L",nat,Imp(LeOf(Sub(n,D(1)),l),LeOf(qm,Sub(l,Len(p))))),
            All("u",address,EqOf(Dp(root,App(p,u)),Add(Len(p),Dp(st,u)))),
            All("u",address,All("v",address,Imp(LeOf(D(2),n),Imp(EqOf(Len(u),Sub(hn,Len(p))),
                Imp(EqOf(Len(v),Len(p)),And(
                    EqOf(Dp(root,App(p,u)),Add(Len(p),Dp(st,u))),
                    EqOf(Add(Len(p),Dp(st,u)),Add(Len(p),Dp(st,App(u,v)))))))))),
            All("A",V("Source"),All("L",nat,Imp(LeOf(qm,l),Imp(LeOf(Ht(a),l),Imp(
                All("u",address,Imp(EqOf(Len(u),l),EqOf(Dp(root,App(p,u)),Add(Len(p),Dp(a,u))))),
                EqOf(Call("shape",st),Call("shape",a))))))),
            Branch(t,n,z,p,q));
    }
    private static Formula Branch(Formula t, Formula n, Formula z, Formula p, Formula q)
    {
        var d=V("d"); var e=V("e"); var a=V("A"); var b=V("B"); var l=V("L"); var u=V("u");
        var sa=Src(a); var sb=Src(b); var bit=Call("bit",e);
        var high=High(e,sa,sb); var low=High(e,sb,sa);
        var qtwo=Sub(q,D(2)); var qthree=Sub(q,D(3));
        var maxima=All("L",V("Nat"),Imp(LeOf(qtwo,l),And(
            Call("DepthMaximum",high,l,qtwo),Call("DepthMaximum",low,l,qthree),
            Imp(LeOf(D(3),q),IffOf(EqOf(bit,V("true")),Call("Beats",sa,sb,l))))));
        var three=Imp(EqOf(q,D(3)),And(
            EqOf(High(e,Ht(sa),Ht(sb)),D(1)),EqOf(High(e,Ht(sb),Ht(sa)),D(0))));
        var two=Imp(EqOf(q,D(2)),And(
            EqOf(sa,Call("of",Call("negate",bit))),EqOf(sb,Call("of",bit)),
            All("u",V("Address"),Imp(Seq(u,Sp,Neq,Sp,Call("nil")),EqOf(Dp(Src(t),u),D(1)))),
            All("u",V("Address"),EqOf(Dp(Src(t),u),Dp(Call("mul",sb,sa),u)))));
        var horizon=Sub(Seq(D(2),Sp,Times,Sp,n),D(1));
        var suffix=Sub(Sub(horizon,Len(p)),D(1));
        var law=And(
            LeOf(D(2),q),
            EqOf(Call("time",e),Add(Call("born",d),Call("select",Call("initial",d),D(2),D(1)))),
            LeOf(Call("time",e),n),LtOf(D(0),Call("index",e)),
            EqOf(bit,Call("apply",z,Call("index",e))),
            EqOf(Call("born",Call("descriptor",a)),Call("time",e)),
            EqOf(Call("born",Call("descriptor",b)),Call("time",e)),
            EqOf(Call("initial",Call("descriptor",a)),Call("negate",bit)),
            EqOf(Call("initial",Call("descriptor",b)),bit),
            EqOf(High(e,Call("rank",n,a),Call("rank",n,b)),Sub(q,D(1))),
            EqOf(High(e,Call("rank",n,b),Call("rank",n,a)),qtwo),
            EqOf(High(e,Ht(sa),Ht(sb)),qtwo),EqOf(High(e,Ht(sb),Ht(sa)),qthree),
            maxima,
            Imp(LeOf(D(3),q),And(LeOf(qtwo,suffix),EqOf(Add(Add(Len(p),D(1)),Par(suffix)),horizon),
                IffOf(EqOf(bit,V("true")),Call("RootBeats",Src(Call("snapshot",z,n)),p,suffix)))),
            three,two);
        return All("d",V("Descriptor"),All("e",V("Birth"),All("A",V("Physical"),All("B",V("Physical"),
            Imp(EqOf(t,Call("branch",d,e,a,b)),law)))));
    }

    private static Formula Result()
    {
        var n=V("n"); var z=V("z"); var p=V("p"); var t=V("T");
        var snapshot=Call("snapshot",z,n);
        return All("n",V("Nat"),All("z",Seq(V("Nat"),Sp,To,Sp,V("Bool")),And(
            EqOf(Call("descriptor",snapshot),Call("Descriptor",D(0),V("true"))),
            EqOf(Call("rank",n,snapshot),n),
            All("p",V("Address"),All("T",V("Physical"),Imp(
                EqOf(Call("at",p,snapshot),Call("some",t)),Call("ConeLaw",n,z,p,t)))))));
    }
}
