using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class AsymmetricThreeLabelCostDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Asymmetric three-label phase sets have exact native paid cost.",
        H("Two queries separated by paid waiting"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-asymmetric-three-label-cost"),
            DeclarationHandle.Create(Owner + "original_asymmetric_three_label_cost"),
            H("Exact cost for arbitrary asymmetric phase sets"),
            StatementSource.FromAuthor(Disp(CostFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let g be at least two, let 3 <= u < p with u and p coprime, and write p=hu+r with 1 <= r < u. Put T=gp, k=T-1 and m=gu. The nonempty disjoint finite sets HB and HC satisfy HB contained in [1,u-r] and HC contained in [1,u-1]. The labels A, B and C are pairwise distinct elements of an arbitrary type Y.")),
                Paragraph(Text("In the free initial value fiber v, every legal initial tail s<k at phase -jg modulo T has label B when j belongs to HB, label C when j belongs to HC, and A otherwise. The target f is unrestricted on the other value fiber and at rejection. The parameter a selects either all Boolean complete blocks or only internally admissible complete blocks. OriginalFiberCost ranges over every actual finite joint history in that alphabet, including the empty history. An initially rejected source returns f(none) for free.")),
                Paragraph(Text("The reader uses the original low-first kbonacci weights and their fixed mod-two output. Its archive contains only the free initial output, issued complete blocks and their own endpoint readings. The selector issues a fixed script and decodes only after its last endpoint. It has no reset, copy, intermediate observation or access to an unexecuted branch. Every issued complete block costs one.")),
                Paragraph(Text("For a set H, the pulse word has a one exactly at local positions jg-1 for j in H and zeros elsewhere. First issue the pulse word for HC, then exactly h-1 zero words, then the pulse word for r+HB. The first word starts and ends in zero. The final word starts in zero, and its pulse for j in HB has absolute position hm+(r+j)g-1=T+jg-1. Hence the first endpoint difference is the indicator of HC, and the last difference is the indicator of HB. The decoder returns C if the first difference is one, B if only the last difference is one, and A otherwise. The phase sets are disjoint, so this recovers the INITIAL label.")),
                Paragraph(Text("Every word has length m<k. The first zero clears any inherited legal tail, and each following word starts in zero, so the complete same-history execution is safe across every seam. The final pulse may occupy the last bit; the script stops there without a clearing fee. The uniform fee is h+1, including all waiting words. When h=1 there are no waiting words. The bounds also allow r=u-1 and all endpoints of both supports.")),
                Paragraph(Text("At tail zero the first window contains a source of each label: phase index zero gives A, any member of HB gives B, and any member of HC gives C. Its label image therefore has cardinality three. The original first-window waiting lower bound gives h+clog(2,3)-1=h+1 for either alphabet. Together with the literal script this proves the exact native cost. Since p=hu+r with 0<r<u, the natural quotient (p+u-1)/u equals h+1 and is the ceiling of p/u. The symbol positivek denotes the positivity proof supplied by the parameter inequalities."))),
            DescribeRole.Theorem))));

    private static Formula CostFormula()
    {
        var Y=F.Id("Y"); var g=F.Id("g"); var u=F.Id("u"); var p=F.Id("p");
        var h=F.Id("h"); var r=F.Id("r"); var HB=F.Id("HB"); var HC=F.Id("HC");
        var A=F.Id("A"); var B=F.Id("B"); var C=F.Id("C"); var k=F.Id("k");
        var m=F.Id("m"); var f=F.Id("f"); var v=F.Id("v"); var a=F.Id("a");
        var j=F.Id("j"); var s=F.Id("s"); var index=Call("val",j);
        var parameters=And(Rel(D(2),Leq,g),And(Rel(D(3),Leq,u),And(Rel(u,Lt,p),
            And(Call("Coprime",u,p),And(Equal(p,Add(Multiply(h,u),r)),
                And(Rel(D(1),Leq,r),Rel(r,Lt,u)))))));
        var supports=And(Call("Nonempty",HB),And(Call("Nonempty",HC),
            And(Call("Disjoint",HB,HC),And(
                Rel(HB,Subseteq,Call("Icc",D(1),Call("natSub",u,r))),
                Rel(HC,Subseteq,Call("Icc",D(1),Call("natSub",u,D(1))))))));
        var distinct=And(Rel(A,Neq,B),And(Rel(A,Neq,C),Rel(B,Neq,C)));
        var phase=Seq(Minus,Call("cast",Multiply(index,g),Call("ZMod",Add(k,D(1)))));
        var record=Call("some",Triple(v,phase,s));
        var value=Call("if",Rel(index,InMacro,HB),B,Call("if",Rel(index,InMacro,HC),C,A));
        var restriction=All(j,Call("Fin",p),All(s,NatType(),Imp(Rel(s,Lt,k),Equal(App(f,record),value))));
        var result=And(Equal(Call("OriginalFiberCost",k,m,Op("positivek"),a,f,v),
                Call("cast",Add(h,D(1)),Op("ENat"))),
            Equal(Add(h,D(1)),Call("natDiv",Call("natSub",Add(p,u),D(1)),u)));
        Formula body=Imp(restriction,result);
        body=All(a,Op("Bool"),body);
        body=All(v,Call("ZMod",D(2)),body);
        body=All(f,Rel(Call("Option",Call("LiveRecord",k)),To,Y),body);
        body=Let(m,Multiply(g,u),body);
        body=Let(k,Call("natSub",Multiply(g,p),D(1)),body);
        body=Imp(distinct,body);
        body=All(A,Y,All(B,Y,All(C,Y,body)));
        body=Imp(supports,body);
        body=All(HB,Call("Finset",NatType()),All(HC,Call("Finset",NatType()),body));
        body=Imp(parameters,body);
        body=All(g,NatType(),All(u,NatType(),All(p,NatType(),All(h,NatType(),All(r,NatType(),body)))));
        return All(Y,Op("Type"),body);
    }

    private static Formula NatType()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Op(string name)=>Seq(Operatorname,Grp(F.Id(name)));
    private static Formula App(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula Triple(Formula a,Formula b,Formula c)=>Seq(Open,a,Comma,b,Comma,c,Close);
    private static Formula Rel(Formula a,Formula relation,Formula b)=>Seq(a,Sp,relation,Sp,b);
    private static Formula Par(Formula body)=>Seq(Open,body,Close);
    private static Formula Imp(Formula a,Formula b)=>Par(Rel(Par(a),Implies,Par(b)));
    private static Formula All(Formula w,Formula type,Formula body)=>
        Par(Seq(Forall,Sp,Open,w,Colon,type,Close,Comma,Sp,Par(body)));
    private static Formula Let(Formula w,Formula value,Formula body)=>
        Seq(Op("let"),Sp,w,Eq,value,Sp,Op("in"),Sp,Par(body));
    private static Formula And(Formula a,Formula b)=>Par(Seq(a,Sp,Land,Sp,b));
}
