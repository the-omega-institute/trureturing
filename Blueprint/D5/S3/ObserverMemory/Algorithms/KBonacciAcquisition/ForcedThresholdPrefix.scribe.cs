using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class ForcedThresholdPrefixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And,b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Rec(Formula v, Formula p, Formula s) => Call("some", Seq(Langle,Sp,v,Comma,p,Comma,s,Rangle));
    private static Formula Pair(Formula a, Formula b) => Seq(Open,a,Comma,b,Close);
    private static Formula If(Formula c, Formula a, Formula b) => Call("ifThenElse",c,a,b);

    public DocumentDefinition Create()
    {
        var nat=Seq(Mathbb,Grp(F.Id("N"))); var y=F.Id("Y"); var k=F.Id("k");
        var q=F.Id("Q"); var m=F.Id("m"); var a=F.Id("a"); var labels=F.Id("labels");
        var outside=F.Id("outside"); var rejected=F.Id("rejected"); var bottom=F.Id("bottom");
        var v=F.Id("v"); var phase=F.Id("phase"); var s=F.Id("s"); var scalar=Call("ZMod",D(2));
        var boolType=F.Id("Bool"); var j=Call("val",new Formula.Negate(phase));
        var label=All("Y",F.Id("Type"),All("k",nat,All("a",nat,
            All("labels",Arrow(Call("ZMod",Add(k,D(1))),y),All("outside",y,All("rejected",y,All("bottom",y,
                And(Equal(Call("initialLabel",k,a,labels,outside,rejected,bottom,F.Id("none")),bottom),
                    All("v",scalar,All("phase",Call("ZMod",Add(k,D(1))),All("s",nat,
                        Equal(Call("initialLabel",k,a,labels,outside,rejected,bottom,Rec(v,phase,s)),
                            If(Le(Subtract(k,a),s),rejected,
                                If(And(Lt(D(0),j),Lt(j,a)),new Formula.Apply(labels,[new Formula.Negate(phase)]),outside))))))))))))));
        var total=Multiply(q,m); var pi=F.Id("pi"); var alphabet=F.Id("alphabet");
        var B=F.Id("B"); var rest=F.Id("rest"); var history=F.Id("history");
        var w=Call("flattenHistory",history); var c=F.Id("c"); var budget=F.Id("budget");
        var target=Call("initialLabel",total,a,labels,outside,rejected,bottom);
        var correct=All("history",Call("List",Call("AllowedBlock",total,m,alphabet)),
            Imp(Equal(Call("output",total,w),Call("some",v)),
                Ex("budget",nat,Ex("c",nat,Equal(Call("execute",total,pi,budget,w,Call("some",v),F.Id("nil")),
                    Call("some",Pair(new Formula.Apply(target,[Call("OriginalRecord",total,w)]),c)))))));
        var cut=Equal(Call("ofFn",B),Call("append",Call("replicate",a,F.Id("true")),Call("cons",F.Id("false"),rest)));
        var execution=All("phase",Call("ZMod",Add(total,D(1))),All("s",nat,Imp(Lt(s,total),
            Equal(Call("runBits",total,B,Rec(v,phase,s)),If(Lt(s,Subtract(total,a)),
                Rec(Add(v,Call("wordIncrement",total,phase,B)),Add(phase,m),Call("tailAfter",D(0),B)),F.Id("none"))))));
        var result=Ex("B",Arrow(Call("Fin",m),boolType),Ex("rest",Call("List",boolType),And(
            Equal(Call("applySelector",pi,Call("some",v),F.Id("nil")),Call("inr",B)),cut,execution)));
        var theorem=All("Y",F.Id("Type"),All("Q",nat,All("m",nat,All("a",nat,
            Imp(And(Le(D(2),q),Le(D(3),a),Lt(a,m)),All("alphabet",boolType,
                All("labels",Arrow(Call("ZMod",Add(total,D(1))),y),All("outside",y,All("rejected",y,All("bottom",y,
                    Imp(new Formula.Not(Equal(outside,rejected)),All("v",scalar,
                        All("pi",Call("Selector",m,y),Imp(correct,result))))))))))))));
        var t=F.Id("t"); var i=F.Id("i"); var jz=F.Id("j"); var tail=F.Id("tail");
        var p=F.Id("p"); var r=F.Id("q"); var recordType=Call("ZMod",Add(total,D(1)));
        Formula Ar(Formula n) => Call("zeroArchive",pi,v,n);
        Formula Word(Formula n) => Call("zeroWord",pi,v,n);
        Formula At(Formula phaseIndex,Formula n) => Add(new Formula.Negate(phaseIndex),Call("cast",Multiply(n,m)));
        Formula Band(Formula phaseIndex) => And(Lt(D(0),Call("val",phaseIndex)),Lt(Call("val",phaseIndex),a));
        Formula Zero(Formula phaseIndex,Formula n) => Equal(Call("wordIncrement",total,At(phaseIndex,n),Word(n)),D(0));
        var selected=All("t",nat,Imp(Lt(t,q),Equal(Call("applySelector",pi,Call("some",v),Ar(t)),Call("inr",Word(t)))));
        var silent=All("t",nat,All("j",recordType,Imp(And(Lt(t,q),Band(jz)),Zero(jz,t))));
        var zeroBefore=All("i",nat,Imp(Lt(i,t),Zero(jz,i)));
        var initial=Rec(v,new Formula.Negate(jz),s);
        var current=Rec(v,At(jz,t),tail);
        var future=Ex("budget",nat,Ex("c",nat,Equal(Call("NativeExecute",pi,budget,current,Call("some",v),Ar(t)),
            Call("some",Pair(new Formula.Apply(target,[initial]),c)))));
        var actual=All("history",Call("List",Call("AllowedBlock",total,m,alphabet)),
            Imp(Equal(Call("OriginalRecord",total,w),initial),And(
                Call("ActualArchive",total,w,Ar(t)),
                Equal(Call("OriginalRecord",total,Call("append",w,Call("archiveWords",Ar(t)))),current))));
        var survivors=All("t",nat,Imp(And(Le(D(1),t),Le(t,q)),Ex("tail",nat,And(Lt(tail,total),
            All("j",recordType,All("s",nat,Imp(Lt(s,Subtract(total,a)),Imp(zeroBefore,And(future,actual)))))))));
        var varied=Ex("p",recordType,Ex("q",recordType,And(Band(p),Band(r),
            new Formula.Not(Equal(new Formula.Apply(labels,[p]),new Formula.Apply(labels,[r]))))));
        var common=All("Y",F.Id("Type"),All("Q",nat,All("m",nat,All("a",nat,
            Imp(And(Le(D(2),q),Le(D(3),a),Lt(a,m)),All("alphabet",boolType,
                All("labels",Arrow(recordType,y),All("outside",y,All("rejected",y,All("bottom",y,
                    Imp(new Formula.Not(Equal(outside,rejected)),Imp(varied,All("v",scalar,
                        All("pi",Call("Selector",m,y),Imp(correct,And(selected,silent,survivors))))))))))))))));
        var zeroArchiveFormula=All("Y",F.Id("Type"),All("m",nat,All("pi",Call("Selector",m,y),All("v",scalar,And(
            Equal(Ar(D(0)),F.Id("nil")),All("t",nat,Equal(Ar(Add(t,D(1))),
                Call("append",Ar(t),Call("list",Pair(Word(t),Call("some",v)))))))))));
        var zeroWordFormula=All("Y",F.Id("Type"),All("m",nat,All("pi",Call("Selector",m,y),All("v",scalar,
            All("t",nat,Equal(Word(t),Call("selectedWord",Call("applySelector",pi,Call("some",v),Ar(t)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual adaptive selectors preserve one coherent first-tour zero archive for arbitrary blind bands.",
            H("Forced thresholds and actual common branches"),Blocks(
                Describe.Lean(DescribeId.Create("initial-label"),DeclarationHandle.Create(Owner+"initialLabel"),
                    H("Immutable threshold and blind band"),StatementSource.FromAuthor(Disp(label)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("All subtraction is natural subtraction. On a live INITIAL record, the tail test has priority: tails at least k-a receive rejected. Smaller tails receive labels(-phase) when 0<(-phase).val<a and outside otherwise. The separately known INITIAL rejection receives bottom. The total phase map labels extends the source map on the band; its unused values are immaterial. It can repeat labels, and outside can occur in its band image."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("forced-threshold-root"),DeclarationHandle.Create(Owner+"forced_threshold_root"),
                    H("The forced literal root and its exact rejection threshold"),StatementSource.FromAuthor(Disp(theorem)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Let k=Qm, Q>=2 and 3<=a<m. The arbitrary Bool alphabet specifies local complete-block legality. Selector means the original adaptive selector, taking only the remembered free endpoint and the chronological acquired archive. flattenHistory concatenates each complete block's literal bits. The display suppresses positivity proof arguments in output, execute and OriginalRecord. applySelector denotes ordinary function application to its two arguments. Correctness ranges over every actual complete-block history in the selected free-value fibre, every phase, and every legal INITIAL tail. Each history has its own terminating budget; no uniform budget is assumed. It is not correctness only on a chosen initial phase.")),
                        Paragraph(Text("Only outside != rejected is needed for this root clause. At phase zero, choose the two actual INITIAL tails k-a-1 and k-a with the same free value. Their labels differ. Every incorrect first-zero position erases their distinction: an earlier zero clears both tails to the same current record, while a later zero or an all-one root rejects both. Their continuations then have identical archives and records and cannot return different INITIAL labels. Joint actual-history realization supplies both records. The native paid-trace equivalence enlarges their separate terminating horizons to a common maximum without changing either returned INITIAL label or exact paid count. Thus the root must contain exactly a leading ones followed by zero.")),
                        Paragraph(Text("The remaining suffix is unrestricted and the complete block has m<k bits. The first-zero execution law therefore rejects exactly s>=k-a. All lower INITIAL tails have the same terminal tail tailAfter(0,B), while scalar and phase follow the original executor. These are complete endpoint readings; the internal zero grants no intermediate observation. There is no logarithmic guard or restriction on repeated band labels.")),
                        Paragraph(Text("The root law supplies the clearing step in the common-archive theorem below. It applies the first-zero acquisition, actual-history realization and execution laws to the two INITIAL tails on opposite sides of the threshold."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("zero-archive"),DeclarationHandle.Create(Owner+"zeroArchive"),
                    H("The selector's zero-reading branch"),StatementSource.FromAuthor(Disp(zeroArchiveFormula)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The archive starts empty. At each stage append the literal selected word with the successful endpoint some(v). The definition supplies a dummy all-zero word if the selector stops; the theorem proves that this alternative never occurs at any first-tour action. It is a branch definition, not an assumed legal execution."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("zero-word"),DeclarationHandle.Create(Owner+"zeroWord"),
                    H("The literal word on that branch"),StatementSource.FromAuthor(Disp(zeroWordFormula)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("selectedWord is the constructor match: inr(B) returns B, and inl(y) returns the all-false function on Fin(m). Every occurrence refers to the same selector and the same remembered free reading."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("first-tour-common-archive"),DeclarationHandle.Create(Owner+"first_tour_common_archive"),
                    H("The generic actual first-tour common archive"),StatementSource.FromAuthor(Disp(common)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Set k=Qm. Each cast in a phase expression has codomain ZMod(k+1); all subtraction between natural numbers is truncated natural subtraction. The original target initialLabel is evaluated on the immutable INITIAL record. The same actual-history correctness premise as above permits separate terminating horizons for every history. The only band variation premise is the existence of two phases in 0<j.val<a with different labels. Other band labels can repeat and outside can occur among them. Only outside!=rejected is needed from the source's stronger separation of R from all low-tail labels. Both control alphabets and every legal inherited INITIAL tail remain included. There is no logarithmic guard.")),
                        Paragraph(Text("The first conjunct proves that each of the Q words really is chosen on this one archive. The second proves zero literal response at every band phase for each such word. The third quantifies one controller-dependent current tail at each paid time 1<=t<=Q. Every low INITIAL tail at every phase whose first t literal responses are zero has its own eventually correct continuation from that same current value, phase and tail. For every actual history realizing that INITIAL record, ActualArchive and the exact OriginalRecord equation hold on that very history after appending archiveWords. Outside sources are covered by this conditional statement even when their label equals a band label. Phases remain separate coordinates and are never identified.")),
                        Paragraph(Text("The root law clears all low INITIAL tails, with its arbitrary suffix determining the common terminal tail. Later first-tour windows miss the blind band. Induction transports the actual prefix equations and each source's separate eventual continuation. Two distinct band labels exclude stopping on the common archive. Phase-independent legality at a common tail excludes a uniformly rejecting selected block: its two eventual continuations would then start from the identical absorbing state and could not return distinct INITIAL labels. The remaining action is therefore actually legal for every zero-response source and advances the same archive. The native paid-trace law compares separate finite horizons without imposing one global budget.")),
                        Paragraph(Text("This proves the coherent-zero-branch clause of the source theorem. The parity equivalence, actual outside survivor, attaining scan, exact support and total costs require further arguments and are not asserted here. In the even-width odd-threshold obstruction any eventual outside survivor may depend on the policy; phase m is reserved for the canonical scan's claim."))),DescribeRole.Theorem))));
    }
}
