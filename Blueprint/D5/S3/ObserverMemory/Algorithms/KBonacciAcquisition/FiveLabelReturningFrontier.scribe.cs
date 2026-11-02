using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FiveLabelReturningFrontierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five distinct threshold-band labels at width seven have original adaptive and preset paid-block price 2Q+2.",
        H("Five labels and a returning width-seven frontier"),
        Blocks(
            Describe.Lean(DescribeId.Create("initial-label"), DeclarationHandle.Create(Owner+"initialLabel"),
                H("Immutable initial threshold labels"), StatementSource.FromAuthor(Disp(LabelFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let Q be a natural number and k=7Q. The entries zero through six of labels are respectively A, B1, B2, B3, B4, B5 and R. The value bottom is the separately known label of the initially rejected source. For a legal record q, put j=(-q.phase).val. Initial tails at least k-6 receive R; smaller initial tails receive Bj at phases 1 through 5 and A elsewhere. The initial value does not change this prescription. The expression ifThenElse denotes its ordinary conditional branches."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("attaining-words"), DeclarationHandle.Create(Owner+"attainingWords"),
                H("The fixed literal stream"), StatementSource.FromAuthor(Disp(WordsFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The function word reads the displayed seven binary digits in their literal left-to-right order, preserving leading zeros. Concatenate 1111110, Q-1 copies of 1010101, 0000100, Q-1 copies of 0000000, 0000110 and 1000000. Each member is a function from Fin 7 to Bool. The repetitions contain complete paid blocks; no time displacement is free."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("archive-decoder"), DeclarationHandle.Create(Owner+"archiveDecoder"),
                H("Decode the acquired archive"), StatementSource.FromAuthor(Disp(DecoderFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For fixed Q, labels, bottom and free value v, compatible(Q,v,ar) is the proposition that there are a phase p modulo 7Q+1 and a tail s<7Q with scriptArchive(attainingWords Q,some(v,p,s))=ar. When this proposition holds, chosenRecord is the legal record obtained by choosing such a phase and then such a tail. The decoder returns initialLabel of that record; when the proposition fails it returns bottom. These choices use only the observed archive, the free value and the known parameters. For Q≥2 the archive-separation argument below proves that every compatible record has the same initial label."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-five-label-returning-frontier"),
                DeclarationHandle.Create(Owner+"original_five_label_returning_frontier"),
                H("Both global prices and the actual named-stream trace"),
                StatementSource.FromAuthor(Disp(PriceFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume Q is at least two and labels is injective. Thus the five band labels are pairwise different and differ from A, and R differs from every low-tail label. The parameter alphabet selects either all seven-bit words or the internally legal seven-bit words. Since 7<7Q, these alphabets coincide, while every actual seam still uses the original absorbing-rejection transition.")),
                    Paragraph(Text("GlobalAdaptivePrice and GlobalPresetPrice use the original complete-block reader and the full prior of actual finite block histories. The free initial observation is the legal value or rejection. Every later choice uses only that remembered observation and the chronological archive of its own issued words and endpoint replies. Empty histories, rejected histories, both legal free values, every initial phase and every legal initial tail remain included. The conclusion concerns the immutable initial label, even after a zero clears its tail.")),
                    Paragraph(Text("For the trace formula, flattenHistory concatenates the seven bits of every initial history block. The record q is OriginalRecord of that actual word w. The policy pi stops with bottom on initial rejection; on free legal value v it follows finalSelector for attainingWords Q, then applies archiveDecoder Q labels bottom v. This decoder selects the initial label of any legal initial record producing that same archive and free value. Archive separation proves this selection independent of the representative. The decoder uses no initial phase, hidden clock, intermediate reading, reset or second execution.")),
                    Paragraph(Text("The issued archive is empty exactly on initial rejection and is scriptArchive of the displayed literal list on every legal initial record. PaidTrace retains its actual endpoint replies, map(fst,issued) retains exactly the displayed words, and execute returns the immutable label together with the archive length. This length is zero on initial rejection and 2Q+2 otherwise. The positivity argument positivek is the proof that k>0 supplied by Q≥2. All four trace assertions belong to the same original history.")),
                    Paragraph(Text("For the lower bound compare actual initial tails k-7 and k-6 at one common phase and legal value. Their labels differ. A root whose first zero occurs before six leading ones merges them irreversibly. A root with seven leading ones rejects both. Therefore every correct root is 1111110. It clears all low tails and has zero response on phases 1 through 5. The joint actual-source theorem supplies these records as complete-block histories; it does not combine marginal reachability witnesses.")),
                    Paragraph(Text("Before a total fee of 2Q+2, after the root the only potentially informative band endpoints have indices Q and 2Q. At every other index through 2Q the relative band phase lies beyond the full window. The common-tail compression theorem removes only these silent nodes, preserving early stops and uniform rejection. A binary protocol with at most two informative endpoints has at most four distinct label leaves. It cannot return the five different initial band labels. This rules out every smaller lawful adaptive budget.")),
                    Paragraph(Text("The first Q displayed blocks reject precisely the high initial tails and screen all outside phases. The root has full charge support {0,6}. Each later scan word has charge one on all eight ordered window vertices, including its endpoints. Every outside phase not screened by the root is covered by a later scan window. The continuing zero-difference archive therefore contains exactly initial phases 1 through 5.")),
                    Paragraph(Text("The remaining query words are issued at indices Q, 2Q and 2Q+1. Their actual full-window masks are {3,4}, {2,4} and {5,6}. The five initial band phases consequently have distinct acquired difference codes 000, 010, 100, 110 and 001 in increasing phase order. Phase six is absent from this same continuing scan archive. Phase five returns at the left endpoint of the last window and uses this excluded donor; the stream does not wait until 3Q.")),
                    Paragraph(Text("The root ends in zero. Every suffix word has a zero at local position one; the internal-zero execution theorem bounds all inherited seams, including consecutive 1010101 blocks. Its marked-zero spacing is seven and k is at least fourteen. Charge inversion recovers exactly the displayed literal words and their actual tails. The Q-1 all-zero words between the first two queries remain in the archive and are paid. The complete length is 1+(Q-1)+1+(Q-1)+2=2Q+2. The preset construction supplies the upper bound; preset inclusion and the adaptive lower bound give both equal prices.")),
                    Paragraph(Text("These conclusions apply for every Q≥2, including Q=2. They use neither a calendar guard with three common visits nor an unrestricted subset-query alphabet. The reader, joint record realization, inversion, common-tail compression and paid-trace interfaces are the cited original mathematical suppliers. The source-specific combination gives this threshold target and its named literal stream; it asserts no general arbitrary-target optimum or literature priority."))), DescribeRole.Theorem))));

    private static Formula LabelFormula()
    {
        var y=F.Id("Y"); var q=F.Id("Q"); var l=F.Id("labels"); var b=F.Id("bottom");
        var v=F.Id("v"); var p=F.Id("p"); var s=F.Id("s"); var j=F.Id("j");
        var k=Multiply(D(7),q);
        var low=Call("ifThenElse",And(Rel(D(1),Leq,j),Rel(j,Leq,D(5))),App(l,j),App(l,D(0)));
        var live=Let(j,Call("val",Seq(Minus,p)),Equal(Call("initialLabel",q,l,b,Call("some",Triple(v,p,s))),
            Call("ifThenElse",Rel(Call("natSub",k,D(6)),Leq,s),App(l,D(6)),low)));
        return All(y,Op("Type"),All(q,NatType(),All(l,Rel(Call("Fin",D(7)),To,y),All(b,y,
            And(Equal(Call("initialLabel",q,l,b,Op("none")),b),
                All(v,Call("ZMod",D(2)),All(p,Call("ZMod",Add(k,D(1))),All(s,NatType(),live))))))));
    }
    private static Formula WordsFormula()
    {
        var q=F.Id("Q"); var n=Call("natSub",q,D(1));
        var suffix=Call("append",Call("replicate",n,Call("word",D(1,0,1,0,1,0,1))),
            Call("cons",Call("word",D(0,0,0,0,1,0,0)),Call("append",Call("replicate",n,Call("word",D(0,0,0,0,0,0,0))),
                Call("list",Call("word",D(0,0,0,0,1,1,0)),Call("word",D(1,0,0,0,0,0,0))))));
        return All(q,NatType(),Equal(Call("attainingWords",q),Call("cons",Call("word",D(1,1,1,1,1,1,0)),suffix)));
    }
    private static Formula DecoderFormula()
    {
        var q=F.Id("Q"); var l=F.Id("labels"); var b=F.Id("bottom");
        var v=F.Id("v"); var ar=F.Id("ar"); var y=F.Id("Y");
        return All(y,Op("Type"),All(q,NatType(),All(l,Rel(Call("Fin",D(7)),To,y),All(b,y,
            All(v,Call("ZMod",D(2)),All(ar,Call("Archive",D(7)),
                Equal(Call("archiveDecoder",q,l,b,v,ar),
                    Call("ifThenElse",Call("compatible",q,v,ar),
                        Call("initialLabel",q,l,b,Call("chosenRecord",q,v,ar)),b))))))));
    }
    private static Formula PriceFormula()
    {
        var y=F.Id("Y"); var q=F.Id("Q"); var l=F.Id("labels"); var b=F.Id("bottom"); var a=F.Id("alphabet");
        var h=F.Id("history"); var w=F.Id("w"); var r=F.Id("q"); var f=F.Id("f"); var pi=F.Id("pi"); var ar=F.Id("issued");
        var k=Multiply(D(7),q); var fee=Add(Multiply(D(2),q),D(2)); var words=Call("attainingWords",q);
        var free=Call("output",k,Op("positivek"),w); var none=Equal(r,Op("none"));
        var trace=And(Call("PaidTrace",pi,free,r,Op("nil"),ar,App(f,r)),
            And(Equal(Call("map",Op("fst"),ar),Call("ifThenElse",none,Op("nil"),words)),
                And(Equal(Call("length",ar),Call("ifThenElse",none,D(0),fee)),
                    Equal(Call("execute",k,Op("positivek"),pi,fee,w,free,Op("nil")),Call("some",Pair(App(f,r),Call("length",ar)))))));
        var histories=All(h,Call("List",Call("AllowedBlock",k,D(7),a)),Let(w,Call("flattenHistory",h),
            Let(f,Call("initialLabel",q,l,b),Let(pi,Call("policy",q,l,b),Let(r,Call("OriginalRecord",k,Op("positivek"),w),
                Let(ar,Call("ifThenElse",none,Op("nil"),Call("scriptArchive",words,r)),trace))))));
        var result=And(Equal(Call("GlobalAdaptivePrice",k,D(7),Op("positivek"),a,Call("initialLabel",q,l,b)),Call("cast",fee,Op("ENat"))),
            And(Equal(Call("GlobalPresetPrice",k,D(7),Op("positivek"),a,Call("initialLabel",q,l,b)),Call("cast",fee,Op("ENat"))),
                And(Equal(Call("length",words),fee),histories)));
        return All(y,Op("Type"),All(q,NatType(),Imp(Rel(D(2),Leq,q),All(l,Rel(Call("Fin",D(7)),To,y),
            Imp(Call("Injective",l),All(b,y,All(a,Op("Bool"),result)))))));
    }
    private static Formula NatType()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Op(string n)=>Seq(Operatorname,Grp(F.Id(n)));
    private static Formula App(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula Pair(Formula a,Formula b)=>Seq(Open,a,Comma,b,Close);
    private static Formula Triple(Formula a,Formula b,Formula c)=>Seq(Open,a,Comma,b,Comma,c,Close);
    private static Formula Rel(Formula a,Formula r,Formula b)=>Seq(a,Sp,r,Sp,b);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Imp(Formula a,Formula b)=>Par(Rel(Par(a),Implies,Par(b)));
    private static Formula And(Formula a,Formula b)=>Par(Seq(a,Sp,Land,Sp,b));
    private static Formula All(Formula n,Formula t,Formula b)=>Par(Seq(Forall,Sp,Open,n,Colon,t,Close,Comma,Sp,Par(b)));
    private static Formula Let(Formula n,Formula v,Formula b)=>Seq(Op("let"),Sp,n,Eq,v,Sp,Op("in"),Sp,Par(b));
}
