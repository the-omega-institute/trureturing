using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FiveLabelSeamCostDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five initial phase labels have exact paid seam cost h plus two.",
        H("Five labels across an actual terminal seam"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-five-label-seam-cost"),
            DeclarationHandle.Create(Owner + "original_five_label_seam_cost"),
            H("Exact acquisition cost of five initial phase labels"),
            StatementSource.FromAuthor(Disp(CostFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let g be at least two and h be at least one. Set p=5h+1, T=gp, k=T-1 and m=5g. The five entries of labels are distinct. Phase -jg modulo T has label j for j=1,2,3,4 and label zero for every other j. In the fixed initial value fiber v, this prescription holds at every legal initial tail s<k. The function f is arbitrary elsewhere, including its label at rejection. The parameter a selects either the complete Boolean block alphabet or its locally admissible subalphabet.")),
                Paragraph(Text("The cost is the least uniform bound for a single archive-only selector on all actual finite initial block histories. Empty and rejected histories remain included. The initial output is free, every issued complete block is paid, and labels always refer to the initial joint record. The symbol positivek is the proof of positivity following from the parameter bounds. The function index returns its natural argument as an element of Fin 5 when it is below five, and zero otherwise.")),
                Paragraph(Text("For the upper bound issue pulses at positions 2g-1 and 3g-1, then h-1 all-zero blocks, then pulses at 2g-1, 4g-1 and 5g-1, and finally a leading one followed by m-1 zeros. The middle pulse combines two possible second queries; the additional pulses vanish on the opposite initial class. The three differences for the five label classes are 000, 010, 100, 110 and 011. The middle word ends in one and the final word begins in one. Their crossing run has length two, strictly below k, and the remainder of the final word clears the tail. All h+2 complete blocks are charged, including every waiting block.")),
                Paragraph(Text("For the lower bound the five initial phases with indices zero through four have five distinct labels at tail zero. Their actual joint histories are covered by the original first-window waiting and binary-discrimination lower bound. Since the first window has width five and the first revisit occurs after h blocks, this gives h+clog(2,5)-1=h+2. The case h=1 has no waiting blocks and still uses three paid blocks."))),
            DescribeRole.Theorem))));

    private static Formula CostFormula()
    {
        var Y=F.Id("Y"); var g=F.Id("g"); var h=F.Id("h"); var p=F.Id("p");
        var k=F.Id("k"); var m=F.Id("m"); var labels=F.Id("labels"); var f=F.Id("f");
        var v=F.Id("v"); var a=F.Id("a"); var j=F.Id("j"); var s=F.Id("s");
        var record=Call("some",Triple(v,Seq(Minus,Call("cast",Multiply(Call("val",j),g),Call("ZMod",Add(k,D(1))))),s));
        var restriction=All(j,Call("Fin",p),All(s,NatType(),Imp(Rel(s,Lt,k),Equal(App(f,record),App(labels,Call("index",Call("val",j)))))));
        var result=Equal(Call("OriginalFiberCost",k,m,Op("positivek"),a,f,v),Call("cast",Add(h,D(2)),Op("ENat")));
        return All(Y,Op("Type"),All(g,NatType(),All(h,NatType(),
            Imp(And(Rel(D(2),Leq,g),Rel(D(1),Leq,h)),
                Let(p,Add(Multiply(D(5),h),D(1)),Let(k,Call("natSub",Multiply(g,p),D(1)),
                    Let(m,Multiply(D(5),g),All(labels,Rel(Call("Fin",D(5)),To,Y),
                        Imp(Call("Injective",labels),All(f,Rel(Call("Option",Call("LiveRecord",k)),To,Y),
                            All(v,Call("ZMod",D(2)),All(a,Op("Bool"),Imp(restriction,result)))))))))))));
    }
    private static Formula NatType()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Op(string name)=>Seq(Operatorname,Grp(F.Id(name)));
    private static Formula App(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula Triple(Formula a,Formula b,Formula c)=>Seq(Open,a,Comma,b,Comma,c,Close);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula All(Formula w, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, Open, w, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Let(Formula w, Formula value, Formula body) =>
        Seq(Op("let"), Sp, w, Eq, value, Sp, Op("in"), Sp, Par(body));
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
}
