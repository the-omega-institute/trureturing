using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class TwoAdjacentLowTailLabelsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The threshold-three target and the policy-uniform even-width first-tour obstruction.",
        H("Two adjacent low-tail labels"), Blocks(
            Describe.Lean(DescribeId.Create("initial-label"), DeclarationHandle.Create(Owner+"initialLabel"),
                H("The immutable initial target"), StatementSource.FromAuthor(Disp(LabelFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For k=Qm, the four entries of labels are A, B, C and R. Bottom is an arbitrary separately known label, without a distinctness condition. A legal INITIAL record with tail at least k-3 receives R. At smaller INITIAL tails its phase j=(-phase).val receives B at one, C at two and A elsewhere. The free scalar value is immaterial to this label map. The target of the updated record is never substituted for this INITIAL target."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-adaptive-lower"), DeclarationHandle.Create(Owner+"even_adaptive_lower"),
                H("The extra block at every even width"), StatementSource.FromAuthor(Disp(LowerFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume Q is at least two, m is at least four and even, and labels is injective. Every feasible original adaptive budget d is at least Q+2. OriginalAdaptiveFeasible quantifies one lawful selector over all actual complete-block histories, both free values and every legal INITIAL tail. The alphabet parameter includes both original Bool control alphabets. Early stopping and absorbing rejection remain part of the original execute recursion.")),
                    Paragraph(Text("Compare actual INITIAL tails k-4 and k-3 with the same phase and value. Their targets differ. A first zero before position three merges them; a first zero after position three, or an all-one root, rejects both. Correctness therefore forces exactly three leading ones followed by zero. The remaining root suffix is unrestricted. Joint original-history realization supplies these complete records.")),
                    Paragraph(Text("Follow the single chronological archive with zero endpoint differences. Phases one and two have zero root response. Before index Q all later windows miss both phases. They retain a common scalar and current tail. Different labels B and C exclude stopping and uniform rejection at every earlier node. Thus this archive is traversed by actual sources under the controller's own chosen actions.")),
                    Paragraph(Text("If all outside INITIAL phases were screened during these Q blocks, every strictly interior outside vertex of each window would have response one. At the root, the three forced leading bits and the zero at position three, followed by those required interior differences, force its last bit to zero at even width. To screen the shared boundary the next block must start with one. Its required alternating interior differences force its last bit to zero again. Induction leaves the final phase k unqueried, contradicting complete screening. Consequently some outside INITIAL source survives. Its phase can depend on the policy and need not be m.")),
                    Paragraph(Text("That survivor, B and C traverse the same acquired archive, with the same scalar and current tail. They have three distinct immutable labels. A remaining budget of at most one block admits at most two different successful endpoint differences; rejection is uniform for their common tail and cannot separate them. The original own-charge separation theorem therefore rules out every total budget at most Q+1.")),
                    Paragraph(Text("This lower bound is one part of the four-label exact-cost problem. Exact odd-width and even-width attaining scans, their complete same-history paid traces and the matching price equalities require their own literal execution and decoding argument."))), DescribeRole.Theorem))));

    private static Formula LabelFormula()
    {
        var y=F.Id("Y"); var q=F.Id("Q"); var m=F.Id("m"); var l=F.Id("labels"); var b=F.Id("bottom");
        var v=F.Id("v"); var p=F.Id("p"); var s=F.Id("s"); var j=F.Id("j"); var k=Multiply(q,m);
        var low=Call("ifThenElse",Equal(j,D(1)),App(l,D(1)),Call("ifThenElse",Equal(j,D(2)),App(l,D(2)),App(l,D(0))));
        var live=Let(j,Call("val",Seq(Minus,p)),Equal(Call("initialLabel",q,m,l,b,Call("some",Triple(v,p,s))),
            Call("ifThenElse",Rel(Call("natSub",k,D(3)),Leq,s),App(l,D(3)),low)));
        return All(y,Op("Type"),All(q,NatType(),All(m,NatType(),All(l,Rel(Call("Fin",D(4)),To,y),All(b,y,
            And(Equal(Call("initialLabel",q,m,l,b,Op("none")),b),
                All(v,Call("ZMod",D(2)),All(p,Call("ZMod",Add(k,D(1))),All(s,NatType(),live)))))))));
    }
    private static Formula LowerFormula()
    {
        var y=F.Id("Y"); var q=F.Id("Q"); var m=F.Id("m"); var l=F.Id("labels");
        var b=F.Id("bottom"); var a=F.Id("alphabet"); var d=F.Id("d");
        var feasible=Call("OriginalAdaptiveFeasible",Multiply(q,m),m,Op("positivek"),a,Call("initialLabel",q,m,l,b),d);
        return All(y,Op("Type"),All(q,NatType(),All(m,NatType(),
            Imp(And(Rel(D(2),Leq,q),And(Rel(D(4),Leq,m),Call("Even",m))),
                All(l,Rel(Call("Fin",D(4)),To,y),Imp(Call("Injective",l),
                    All(b,y,All(a,Op("Bool"),All(d,NatType(),Imp(feasible,Rel(Add(q,D(2)),Leq,d)))))))))));
    }
    private static Formula NatType()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Op(string n)=>Seq(Operatorname,Grp(F.Id(n)));
    private static Formula App(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula Triple(Formula a,Formula b,Formula c)=>Seq(Open,a,Comma,b,Comma,c,Close);
    private static Formula Rel(Formula a,Formula r,Formula b)=>Seq(a,Sp,r,Sp,b);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Imp(Formula a,Formula b)=>Par(Rel(Par(a),Implies,Par(b)));
    private static Formula And(Formula a,Formula b)=>Par(Seq(a,Sp,Land,Sp,b));
    private static Formula All(Formula n,Formula t,Formula b)=>Par(Seq(Forall,Sp,Open,n,Colon,t,Close,Comma,Sp,Par(b)));
    private static Formula Let(Formula n,Formula v,Formula b)=>Seq(Op("let"),Sp,n,Eq,v,Sp,Op("in"),Sp,Par(b));
}
