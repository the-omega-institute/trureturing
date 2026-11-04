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
    private static Formula Rec(Formula v, Formula p, Formula s) => Call("some", Seq(Langle,v,Comma,p,Comma,s,Rangle));
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
        return DocumentDefinition.Create(ScribeNode.Create(
            "An immutable INITIAL tail threshold forces the first zero of every correct literal root.",
            H("Forced arbitrary tail thresholds"),Blocks(
                Describe.Lean(DescribeId.Create("initial-label"),DeclarationHandle.Create(Owner+"initialLabel"),
                    H("Immutable threshold and blind band"),StatementSource.FromAuthor(Disp(label)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("All subtraction is natural subtraction. On a live INITIAL record, the tail test has priority: tails at least k-a receive rejected. Smaller tails receive labels(-phase) when 0<(-phase).val<a and outside otherwise. The separately known INITIAL rejection receives bottom. The total phase map labels extends the source map on the band; its unused values are immaterial. It can repeat labels, and outside can occur in its band image."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("forced-threshold-root"),DeclarationHandle.Create(Owner+"forced_threshold_root"),
                    H("The forced literal root and its exact rejection threshold"),StatementSource.FromAuthor(Disp(theorem)),AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Let k=Qm, Q>=2 and 3<=a<m. The arbitrary Bool alphabet specifies local complete-block legality. Selector means the original adaptive selector, taking only the remembered free endpoint and the chronological acquired archive. flattenHistory concatenates each complete block's literal bits. The display suppresses positivity proof arguments in output, execute and OriginalRecord. applySelector denotes ordinary function application to its two arguments. Correctness ranges over every actual complete-block history in the selected free-value fibre, every phase, and every legal INITIAL tail. Each history has its own terminating budget; no uniform budget is assumed. It is not correctness only on a chosen initial phase.")),
                        Paragraph(Text("Only outside != rejected is needed for this root clause. At phase zero, choose the two actual INITIAL tails k-a-1 and k-a with the same free value. Their labels differ. Every incorrect first-zero position erases their distinction: an earlier zero clears both tails to the same current record, while a later zero or an all-one root rejects both. Their continuations then have identical archives and records and cannot return different INITIAL labels. Joint actual-history realization supplies both records. The native paid-trace equivalence enlarges their separate terminating horizons to a common maximum without changing either returned INITIAL label or exact paid count. Thus the root must contain exactly a leading ones followed by zero.")),
                        Paragraph(Text("The remaining suffix is unrestricted and the complete block has m<k bits. The first-zero execution law therefore rejects exactly s>=k-a. All lower INITIAL tails have the same terminal tail tailAfter(0,B), while scalar and phase follow the original executor. These are complete endpoint readings; the internal zero grants no intermediate observation. There is no logarithmic guard or restriction on repeated band labels.")),
                        Paragraph(Text("This statement establishes the root clause of the forced-prefix theorem. It does not assert the common first-tour archive, the parity obstruction, an attaining scan, exact surviving phase support, or any total cost formula."))),DescribeRole.Theorem))));
    }
}
