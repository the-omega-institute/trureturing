using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class TwoAdjacentLowTailLabelsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The threshold-three immutable target has original adaptive and preset price Q+1 at odd width and Q+2 at even width.",
        H("Two adjacent low-tail labels"), Blocks(
            Describe.Lean(DescribeId.Create("first-zero-form"), DeclarationHandle.Create(Owner+"first_zero_form"),
                H("The first zero of a literal list"), StatementSource.FromAuthor(Disp(FirstZeroFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every finite Boolean list is either all ones, or is a run of a leading ones followed by its first zero and a remaining literal suffix. The list can be empty, in which case the all-one alternative holds with length zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("response-off"), DeclarationHandle.Create(Owner+"response_off"),
                H("A first-tour window misses an INITIAL phase"), StatementSource.FromAuthor(Disp(ResponseOffFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For an arbitrary literal m-bit block B, first-tour index t<Q, and INITIAL index j<=Qm, the response is zero if j<tm or (t+1)m<j. The phase expression is evaluated in ZMod(Qm+1). This applies to every controller's own block and requires no assumption about its root, labels or acquired tail."))), DescribeRole.Theorem),
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
                    Paragraph(Text("The policy-dependent survivor is used on the actual lower-bound path; no fixed outside phase is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("query-word"), DeclarationHandle.Create(Owner+"queryWord"),
                H("The first final query"), StatementSource.FromAuthor(Disp(SingleWordFormula("queryWord",1))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The one is at local index one; all other bits are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("final-word"), DeclarationHandle.Create(Owner+"finalWord"),
                H("The even-width final query"), StatementSource.FromAuthor(Disp(SingleWordFormula("finalWord",0))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The one is at local index zero; all other bits are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("attaining-words"), DeclarationHandle.Create(Owner+"attainingWords"),
                H("The literal attaining stream"), StatementSource.FromAuthor(Disp(WordsFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a local index i<m, rootWord is true exactly when i<3 or i is even. The middleWord bit is true exactly when i has parity one at even m and parity zero at odd m. The queryWord has its only one at index one; finalWord has its only one at index zero. Thus at odd m the stream is 111(01)^((m-3)/2), Q-1 copies of (10)^((m-1)/2)1, and 01 followed by m-2 zeros. At even m it is 1110(10)^((m-4)/2), Q-1 copies of (01)^(m/2), 01 followed by m-2 zeros, and 1 followed by m-1 zeros. Repetition exponents count literal pairs. Every displayed block is paid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("archive-decoder"), DeclarationHandle.Create(Owner+"archiveDecoder"),
                H("Decode the acquired original archive"), StatementSource.FromAuthor(Disp(DecoderFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Compatibility means that some original phase and tail s<Qm, with the given free value, produce exactly this scriptArchive. chosenRecord selects one such record. The decoder returns its INITIAL target; if no compatible record exists it returns bottom. Archive separation proves that all compatible records have the same INITIAL target. The choices use only the acquired chronological archive and the remembered free scalar."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-threshold-three"), DeclarationHandle.Create(Owner+"original_threshold_three"),
                H("Exact prices and the same-history paid trace"), StatementSource.FromAuthor(Disp(PriceFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let Q be at least two, m at least four and labels injective into an arbitrary universe-polymorphic type Y. The arbitrary bottom label need not differ from any entry. The alphabet parameter includes both original Bool alphabets. Set fee=Q+1 at odd m and fee=Q+2 at even m. Both global prices equal fee. The original complete-block prior includes all phases, both scalar values, all legal INITIAL tails, the empty history and rejected histories.")),
                    Paragraph(Text("In the trace formula flattenHistory concatenates the literal bits of the given initial history. The policy stops with bottom on a free rejected observation; otherwise it follows finalSelector for the displayed stream and then applies archiveDecoder at the remembered free value. Its issued archive is empty on initial rejection and the actual scriptArchive on every legal record. The PaidTrace, exact issued word list, paid length and execute equality all refer to this same history. The returned value is the immutable initial label. positivek denotes the positivity proof supplied by the displayed hypotheses.")),
                    Paragraph(Text("The root rejects precisely INITIAL tails at least k-3. Its acquired charge and all later legal charges are differences of consecutive actual endpoint readings. The first Q blocks have zero support exactly {1,2} at odd width and {1,2,m} at even width. Any earlier positive scan difference belongs to A; root rejection belongs to R. At index Q, queryWord has the actual INITIAL mask {0,1}, so it identifies B. At odd width the remaining zero identifies C. At even width the remaining pair is C at phase two and A at phase m. The finalWord at index Q+1 has INITIAL mask {m-1,m} and separates these two sources. No root suffix or intermediate support is substituted for INITIAL phases.")),
                    Paragraph(Text("The root contains zero at position three and leaves tail at most m-4. Every following word contains zero at local position zero or one. The internal-zero execution theorem proves all actual seams legal for k=Qm; absorbing rejection and the exact literal tail are retained. QueryWord and finalWord end in zero. Their trailing zeros are literal paid symbols. There is no unpaid clearing, reset or time displacement.")),
                    Paragraph(Text("For the baseline lower bound the existing original_cost_lower theorem is applied to the three distinct tail-zero labels A, B and C, with gcd(m,Qm+1)=1. Its first-window wait is Q and its binary depth is two, giving Q+1. The even-width actual-policy survivor theorem supplies the extra block. The original script-preset construction supplies the upper bound; preset inclusion and the adaptive lower bound yield both exact global prices. For Q=2,m=4 the literal list is 1110|0101|0100|1000 and fee four. For Q=2,m=5 it is 11101|10101|01000 and fee three."))), DescribeRole.Theorem))));

    private static Formula ResponseOffFormula()
    {
        var q=F.Id("Q"); var m=F.Id("m"); var t=F.Id("t"); var j=F.Id("j"); var b=F.Id("B");
        var left=Rel(j,Lt,Multiply(t,m)); var right=Rel(Multiply(Add(t,D(1)),m),Lt,j);
        var off=Seq(Open,new Formula.Logic(left,FormulaLogicOperator.Or,right),Close);
        var phase=Add(Seq(Minus,Call("cast",j)),Call("cast",Multiply(t,m)));
        return All(q,NatType(),All(m,NatType(),All(t,NatType(),All(j,NatType(),
            Imp(And(Rel(D(2),Leq,q),And(Rel(D(4),Leq,m),And(Rel(t,Lt,q),And(Rel(j,Leq,Multiply(q,m)),off)))),
                All(b,Rel(Call("Fin",m),To,Op("Bool")),Equal(Call("wordIncrement",Multiply(q,m),phase,b),D(0))))))));
    }
    private static Formula FirstZeroFormula()
    {
        var bits=F.Id("bits"); var a=F.Id("a"); var rest=F.Id("rest"); var list=Call("List",Op("Bool"));
        var cut=Equal(bits,Call("append",Call("replicate",a,Op("true")),Call("cons",Op("false"),rest)));
        var suffix=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("rest"),list,cut);
        var first=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("a"),NatType(),suffix);
        return All(bits,list,new Formula.Logic(Equal(bits,Call("replicate",Call("length",bits),Op("true"))),FormulaLogicOperator.Or,first));
    }
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
    private static Formula SingleWordFormula(string name,byte index)
    {
        var m=F.Id("m"); var i=F.Id("i");
        return All(m,NatType(),All(i,Call("Fin",m),Equal(Call(name,m,i),Call("decide",Equal(Call("val",i),D(index))))));
    }
    private static Formula WordsFormula()
    {
        var q=F.Id("Q"); var m=F.Id("m");
        var suffix=Call("append",Call("replicate",Call("natSub",q,D(1)),Call("middleWord",m)),
            Call("cons",Call("queryWord",m),Call("ifThenElse",Equal(Call("mod",m,D(2)),D(0)),Call("list",Call("finalWord",m)),Op("nil"))));
        return All(q,NatType(),All(m,NatType(),Equal(Call("attainingWords",q,m),Call("cons",Call("rootWord",m),suffix))));
    }
    private static Formula DecoderFormula()
    {
        var q=F.Id("Q"); var m=F.Id("m"); var l=F.Id("labels"); var b=F.Id("bottom");
        var v=F.Id("v"); var ar=F.Id("ar"); var y=F.Id("Y");
        return All(y,Op("Type"),All(q,NatType(),All(m,NatType(),All(l,Rel(Call("Fin",D(4)),To,y),All(b,y,
            All(v,Call("ZMod",D(2)),All(ar,Call("Archive",m),
                Equal(Call("archiveDecoder",q,m,l,b,v,ar),
                    Call("ifThenElse",Call("compatible",q,m,v,ar),
                        Call("initialLabel",q,m,l,b,Call("chosenRecord",q,m,v,ar)),b)))))))));
    }
    private static Formula PriceFormula()
    {
        var y=F.Id("Y"); var q=F.Id("Q"); var m=F.Id("m"); var l=F.Id("labels"); var b=F.Id("bottom"); var a=F.Id("alphabet");
        var h=F.Id("history"); var w=F.Id("w"); var r=F.Id("q"); var f=F.Id("f"); var pi=F.Id("pi"); var ar=F.Id("issued");
        var k=Multiply(q,m); var fee=Add(Add(q,D(1)),Call("ifThenElse",Equal(Call("mod",m,D(2)),D(0)),D(1),D(0))); var words=Call("attainingWords",q,m);
        var free=Call("output",k,Op("positivek"),w); var none=Equal(r,Op("none"));
        var trace=And(Call("PaidTrace",pi,free,r,Op("nil"),ar,App(f,r)),
            And(Equal(Call("map",Op("fst"),ar),Call("ifThenElse",none,Op("nil"),words)),
                And(Equal(Call("length",ar),Call("ifThenElse",none,D(0),fee)),
                    Equal(Call("execute",k,Op("positivek"),pi,fee,w,free,Op("nil")),Call("some",Pair(App(f,r),Call("length",ar)))))));
        var histories=All(h,Call("List",Call("AllowedBlock",k,m,a)),Let(w,Call("flattenHistory",h),
            Let(f,Call("initialLabel",q,m,l,b),Let(pi,Call("policy",q,m,l,b),Let(r,Call("OriginalRecord",k,Op("positivek"),w),
                Let(ar,Call("ifThenElse",none,Op("nil"),Call("scriptArchive",words,r)),trace))))));
        var result=And(Equal(Call("GlobalAdaptivePrice",k,m,Op("positivek"),a,Call("initialLabel",q,m,l,b)),Call("cast",fee,Op("ENat"))),
            And(Equal(Call("GlobalPresetPrice",k,m,Op("positivek"),a,Call("initialLabel",q,m,l,b)),Call("cast",fee,Op("ENat"))),
                And(Equal(Call("length",words),fee),And(SeamFormula(m),And(BoundaryFormula(),histories)))));
        return All(y,Op("Type"),All(q,NatType(),All(m,NatType(),Imp(And(Rel(D(2),Leq,q),Rel(D(4),Leq,m)),All(l,Rel(Call("Fin",D(4)),To,y),
            Imp(Call("Injective",l),All(b,y,All(a,Op("Bool"),result))))))));
    }
    private static Formula SeamFormula(Formula m)
    {
        var s=F.Id("s");
        return All(s,NatType(),And(Equal(Call("tailAfter",s,Call("queryWord",m)),D(0)),Equal(Call("tailAfter",s,Call("finalWord",m)),D(0))));
    }
    private static Formula BoundaryFormula()
    {
        var even=Call("list",Call("bits",D(1,1,1,0)),Call("bits",D(0,1,0,1)),Call("bits",D(0,1,0,0)),Call("bits",D(1,0,0,0)));
        var odd=Call("list",Call("bits",D(1,1,1,0,1)),Call("bits",D(1,0,1,0,1)),Call("bits",D(0,1,0,0,0)));
        return And(Equal(Call("map",Op("ofFn"),Call("attainingWords",D(2),D(4))),even),Equal(Call("map",Op("ofFn"),Call("attainingWords",D(2),D(5))),odd));
    }
    private static Formula Pair(Formula a,Formula b)=>Seq(Open,a,Comma,b,Close);
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
