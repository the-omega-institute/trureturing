using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class JJFiveFailureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed 64 complete targets realize one simultaneous JJ history tree and defeat five further readings on its unrestricted whole fiber.",
        H("The second-J five-level obstruction"), Blocks(
            Paragraph(Text("The domain is exactly Definition 1.1 of SelfCalibrating Relation Mathematics V: every strictly entrywise positive real 2 by 2 source P with determinant zero and trace one, every nonzero entire real polynomial g of degree at most three, and every real constant drift. The native World 3 representation is bidirectionally equivalent to this domain by CompleteFailure.whole_domain. Lower degrees, either gain sign, sampled or repeated roots, asymmetric sources and all drifts remain in the ambient fiber. No witness choice restricts the decoder's domain.")),
            Paragraph(Text("False means M=[[0,1],[1,1]], true means J=[[0,1],[1,0]]. Words are chronological. The empty acquisition is I, and appending E left-multiplies by E. Every atom is immediately read on the same complete world at its original clock; there are no resets, copies, skipped reads or additional ports. For a suffix u of length five write w=JJ++u, A(w)=acquisition(w), and W(u,e)=world(u,e). The 32 terminal words and their two Boolean slots give 64 labels, even when complete worlds repeat across different words.")),
            Paragraph(Math(Disp(Seq(I("H"), Caret, Grp(I("JJ")), Eq, Sp,
                Tup(N(0), I("J"), N(24), I("J"), Q(192,5)))))),
            Paragraph(Text("For each word beginning JJJ the source map qSource uses the following two unit-J-signature lines. All parameters satisfy absolute value less than one half. These are positive rank-one trace-one sources, and their J trace is one. The equal-column and equal-row lines meet only at Pstar.")),
            Paragraph(Math(Disp(Seq(I("Pstar"), Eq, Sp, Q(1,2), Mat(N(1),N(1),N(1),N(1)),
                Comma, Sp, I("Rzero"), Eq, Sp, Mat(N(-1),N(-1),N(1),N(1)),
                Comma, Sp, I("Lzero"), Eq, Sp, Mat(N(-1),N(1),N(-1),N(1)))))),
            Paragraph(Math(Disp(Seq(Sub(I("alpha"),I("w")), Eq, Sp, Tr(Seq(C("A",I("w")),I("Rzero"))),
                Comma, Sp, Sub(I("beta"),I("w")), Eq, Sp, Tr(Seq(C("A",I("w")),I("Lzero"))),
                Comma, Sp, Sub(I("c"),I("w")), Eq, Sp, N(4),
                Tup(Seq(N(1),Plus,Abs(Sub(I("alpha"),I("w"))),Plus,Abs(Sub(I("beta"),I("w"))))))))),
            Paragraph(Text("The ordered pair (Q(w,0),Q(w,1)) is fixed by these exact exhaustive cases, with the alpha-zero case taking precedence:")),
            Paragraph(Math(Disp(Seq(Tup(Sub(I("Q"),Seq(I("w"),Comma,N(0))), Sub(I("Q"),Seq(I("w"),Comma,N(1)))), Eq, Sp,
                Tup(Seq(I("Pstar"),Minus,Q(1,4),I("Rzero")), Seq(I("Pstar"),Plus,Q(1,4),I("Rzero"))),
                Quad, Sp, Sub(I("alpha"),I("w")),Eq,N(0))))),
            Paragraph(Math(Disp(Seq(Tup(Sub(I("Q"),Seq(I("w"),Comma,N(0))), Sub(I("Q"),Seq(I("w"),Comma,N(1)))), Eq, Sp,
                Tup(Seq(I("Pstar"),Minus,Q(1,4),I("Lzero")), Seq(I("Pstar"),Plus,Q(1,4),I("Lzero"))),
                Quad, Sp, Sub(I("alpha"),I("w")),Neq,Sp,N(0),Comma,Sub(I("beta"),I("w")),Eq,N(0))))),
            Paragraph(Math(Disp(Seq(Tup(Sub(I("Q"),Seq(I("w"),Comma,N(0))), Sub(I("Q"),Seq(I("w"),Comma,N(1)))), Eq, Sp,
                Tup(Seq(I("Pstar"),Plus,Frac,Grp(Sub(I("beta"),I("w"))),Grp(Sub(I("c"),I("w"))),I("Rzero")),
                    Seq(I("Pstar"),Plus,Frac,Grp(Sub(I("alpha"),I("w"))),Grp(Sub(I("c"),I("w"))),I("Lzero"))),
                Quad, Sp, Sub(I("alpha"),I("w")),Sub(I("beta"),I("w")),Neq,Sp,N(0))))),
            Paragraph(Text("The last parameters are nonzero and have absolute value less than one quarter. In the first two cases opposite nonzero parameters give different sources. Trace linearity gives tr(A(w)Q(w,0))=tr(A(w)Q(w,1)): in the last case both increments from tr(A(w)Pstar) equal alpha(w)beta(w)/c(w), and in the first two cases both increments vanish.")),
            Paragraph(Math(Disp(Seq(Sub(I("P"),Seq(I("A"),Comma,N(0))), Eq, Sp, Q(1,768),
                Mat(N(607),Seq(N(372),Plus,Root(40657)),Seq(N(372),Minus,Root(40657)),N(161)),
                Comma, Sp, Sub(I("P"),Seq(I("A"),Comma,N(1))),Eq,Sp,
                Sub(I("P"),Seq(I("A"),Comma,N(0))),Caret,Grp(I("T")))))),
            Paragraph(Math(Disp(Seq(Sub(I("P"),Seq(I("B"),Comma,N(0))), Eq, Sp,
                Mat(Q(9,10),Div(Seq(N(44),Plus,Root(1207)),N(90)),
                    Div(Seq(N(44),Minus,Root(1207)),N(90)),Q(1,10)),
                Comma, Sp, Sub(I("P"),Seq(I("B"),Comma,N(1))),Eq,Sp,
                Sub(I("P"),Seq(I("B"),Comma,N(0))),Caret,Grp(I("T")))))),
            Paragraph(Text("The A determinant identity is 372 squared minus 40657 = 97727 = 607 times 161, and 607+161=768. The B identity is 44 squared minus 1207 = 729, with 729/90 squared=9/100. Both square roots are positive and smaller than their off-diagonal centers. Thus both transpose pairs consist of distinct legal sources. These are the exact prescribed matrices, without symmetry assumptions.")),
            Paragraph(Math(Disp(Seq(C("hC",I("t")),Eq,Sp,Gain(2,5,4,5,6),Comma,Sp,I("dC"),Eq,N(48),
                Semi,Sp,C("hA",I("t")),Eq,Sp,Gain(32,125,5,6,7),Comma,Sp,I("dA"),Eq,Q(1344,25),
                Semi,Sp,C("hB",I("t")),Eq,Sp,Gain(3,10,4,6,7),Comma,Sp,I("dB"),Eq,Q(252,5))))),
            Paragraph(Text("Each displayed gain is the same entire nonzero cubic throughout its world. All seven-action words beginning JJ are assigned simultaneously: JJJ uses (Q(w,e),hC,dC); JJMM uses (PA(e),hA,dA); JJMJ uses (PB(e),hB,dB). The three cases exhaust the labels and contain respectively 32,16,16 slots. The pair at every word has different sources. Sources and coefficients are fixed by world before any response is specified.")),
            Paragraph(Text("The polynomial coefficients, ordered from constant to cubic, are (-48,148/5,-6,2/5), (-1344/25,3424/125,-576/125,32/125), and (-252/5,141/5,-51/10,3/10). The following three vectors list every sample at clocks 0,1,2,3,4,5,6,7 of those entire gains:")),
            Paragraph(Math(Disp(Seq(C("samplesC",Seq()),Eq,Sp,
                Tup(N(-48),N(-24),Q(-48,5),Q(-12,5),N(0),N(0),N(0),Q(12,5)))))),
            Paragraph(Math(Disp(Seq(C("samplesA",Seq()),Eq,Sp,
                Tup(Q(-1344,25),Q(-768,25),Q(-384,25),Q(-768,125),Q(-192,125),N(0),N(0),N(0)))))),
            Paragraph(Math(Disp(Seq(C("samplesB",Seq()),Eq,Sp,
                Tup(Q(-252,5),N(-27),N(-12),Q(-18,5),N(0),Q(3,5),N(0),N(0)))))),
            Paragraph(Text("Every source has trace one. Its J trace is respectively 1,31/32,44/45 in the C,A,B cases. Since the first JJ has cumulative matrices J,I, all 64 targets have readings (0,24,192/5) at clocks 0,1,2. At JJJ the next reading is 228/5; every descendant clock four, five and six reads 48. The terminal pair agrees at clock seven by the terminal trace equality.")),
            Paragraph(Text("For the A and B arms tr(MPA)=31/32+161/768=905/768 and tr(MPB)=44/45+1/10=97/90. The actual third-M responses coincide: 1344/25-(768/125)(905/768)=1163/25=252/5-(18/5)(97/90). This joins both fourth-action arms at the same entire JJM history. At JJMM, M squared=I+M has A trace 1673/768, giving 1344/25-(192/125)(1673/768)=25207/500. All subsequent A samples vanish.")),
            Paragraph(Text("At JJMJ the clock-four matrix is JM and the B gain vanishes. Fifth J gives J(JM)=M with trace 97/90; fifth M gives MJM=[[0,1],[1,2]] with trace 44/45+2/10=53/45. The responses are 252/5+(3/5)(97/90)=7657/150 and 252/5+(3/5)(53/45)=3833/75. The last two B gain samples vanish. Zero-gain positions still execute and immediately read each chosen atom.")),
            Paragraph(Text("The single shared-ancestor response table is: clock 3 JJJ:228/5; clocks 4,5,6 below JJJ:48; clock 7 w below JJJ:48+(12/5)tr(A(w)Q(w,0)); clock 3 JJM:1163/25; clock 4 JJMM:25207/500; clocks 5,6,7 below JJMM:1344/25; clock 4 JJMJ:252/5; clock 5 JJMJJ:7657/150; clock 5 JJMJM:3833/75; clocks 6,7 below JJMJ:252/5. Together with clocks 0,1,2 this defines the common full response Z(v). The public response function uses suffixes below JJ; fullResponse additionally gives the initial 0 and first-J 24.")),
            Describe.Lean(DescribeId.Create("prescribed-jj-five-failure"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/JJFiveFailure.jj_five_failure"),
                H("One labelled assignment, finite failure and whole-fiber failure"),
                StatementSource.FromAuthor(MainStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here U is the finite set of all Boolean lists of length five, D=U times {0,1} is labels, DC consists of labels with first letter J, DA of first two letters MM, and DB of first two letters MJ. W(u,e) is world(u,e), and K is family, the image of D under W. The quantified domain equivalence is the complete unrestricted source/gain/drift equivalence displayed in CompleteFailure.whole_domain at d=3. Z is exactly the preceding complete response table, including original clocks zero through seven. Thus every shared ancestor is checked on the same fixed complete worlds.")),
                    Paragraph(Text("For a suffix-prefix v and n with length(v)+n=5, support(v,n) is the union of both slots over every n-letter descendant. Its distinct-pair guard follows from a descendant pair. For either atomic action E, support(v++[E],n) lies in support(v,n+1) and has next response response(v++[E]) on the actual clock length(JJ++v)+1. Backward induction and same-word inclusion give the losing recursion with both actions. Taking v empty gives finite L5 at JJ, and inclusion in the whole unrestricted history fiber gives whole-fiber L5. The nontriviality guard is retained at every node."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-five-read-unrestricted-recovery"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/JJFiveFailure.result"),
                H("No complete-target recovery in five further readings"),
                StatementSource.FromAuthor(Refutation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed claim is that some arbitrary deterministic Policy 3 identifies every world in the whole compatible JJ fiber within five further original-clock readings. Its result is the literal negation of that claim. A policy may choose either atom or return a complete world at any node. CompleteFailure.loses_excludes_policy applies to the actual whole-fiber L5, so all early stopping decisions are included. This result does not assert original-root impossibility, the affine action consequence of 25.2, a result on the other 192 terminal slots, or a nine-read upper bound.")),
                    Paragraph(Text("The construction is the repository-derived joint realization of SelfCalV Theorem 25.1. It consumes the existing native chronological products, source chart and finite failure recursion; the supplied mathematical domain is unchanged. Affine response transport of Lemma 9.2 is context for 25.2 and is not needed to prove this fixed normalized JJ assertion. The inclusion argument is the unrestricted same-history principle of Lemma 9.3. No external identifiability, automaton or width theorem is invoked, and no novelty claim is made."))), DescribeRole.Theorem)
        )));

    private static Formula I(string n) => F.Id(n);
    private static Formula N(long n) => n < 0 ? Seq(Minus, Num(-n)) : Num(n);
    private static Formula Q(long a,long b) => Div(N(a),N(b));
    private static Formula Div(Formula a, Formula b) => Seq(Frac,Grp(a),Grp(b));
    private static Formula C(string n, Formula x) => Seq(Operatorname,Grp(I(n)),Open,x,Close);
    private static Formula Sub(Formula x,Formula y) => Seq(x,Underscore,Grp(y));
    private static Formula Abs(Formula x) => Seq(Lvert,Sp,x,Rvert);
    private static Formula Tr(Formula x) => C("tr",x);
    private static Formula Root(long n) => Seq(Sqrt,Grp(N(n)));
    private static Formula Tup(params Formula[] xs) => Seq(Open,Join(xs),Close);
    private static Formula Join(Formula[] xs) => Seq(xs.SelectMany((x,k) => k==0 ? new[]{x} : new[]{Comma,Sp,x}).ToArray());
    private static Formula Mat(Formula a, Formula b, Formula c, Formula d) =>
        Seq(Begin,Grp(I("pmatrix")),a,Amp,b,RowBreak,c,Amp,d,End,Grp(I("pmatrix")));
    private static Formula Gain(long a,long b,long r,long s,long t) => Seq(Q(a,b),Tup(Seq(I("t"),Minus,N(r))),Tup(Seq(I("t"),Minus,N(s))),Tup(Seq(I("t"),Minus,N(t))));
    private static Formula Card(string x) => Seq(Lvert,Sp,I(x),Rvert);
    private static Formula L(Formula k) => C("L",Seq(N(5),Comma,k,Comma,I("JJ")));
    private static Formula Fiber => C("wholeSet",Seq(I("JJ"),Comma,I("H"),Caret,Grp(I("JJ"))));
    private static Formula MainStatement() => Disp(Seq(
        Card("D"),Eq,N(64),Land,Sp,Card("U"),Eq,N(32),Land,Sp,
        Card("DC"),Eq,N(32),Land,Sp,Card("DA"),Eq,N(16),Land,Sp,Card("DB"),Eq,N(16),Land,Sp,
        I("K"),Eq,C("image",Seq(I("W"),Comma,I("D"))),Land,Sp,
        C("OriginalDomainCorrespondence",N(3)),Land,Sp,
        Open,Forall,Sp,I("u"),InMacro,Sp,I("U"),Comma,Sp,
        C("W",Seq(I("u"),Comma,N(0))),Neq,Sp,C("W",Seq(I("u"),Comma,N(1))),Land,Sp,
        Open,Forall,Sp,I("e"),InMacro,Sp,OpenBrace,N(0),Comma,N(1),CloseBrace,Comma,Sp,
        C("natDegree",C("gain",C("W",Seq(I("u"),Comma,I("e"))))),Eq,N(3),Close,Land,Sp,
        Open,Forall,Sp,I("e"),InMacro,Sp,OpenBrace,N(0),Comma,N(1),CloseBrace,Comma,
        I("i"),InMacro,Sp,OpenBrace,N(0),Comma,N(1),Comma,N(2),Comma,N(3),Comma,N(4),Comma,N(5),Comma,N(6),Comma,N(7),CloseBrace,Comma,Sp,
        C("readAt",Seq(C("W",Seq(I("u"),Comma,I("e"))),Comma, I("JJ"),Plus,Plus,I("u"),Comma,I("i"))),Eq,Sp,
        C("Z",C("take",Seq(I("JJ"),Plus,Plus,I("u"),Comma,I("i")))),Close,Close,Land,Sp,
        I("K"),Subseteq,Sp,Fiber,Land,Sp,C("FiniteLosing",Seq(N(5),Comma,I("K"),Comma,I("JJ"))),Land,Sp,L(Fiber)));
    private static Formula Refutation() => Disp(Seq(Neg,Sp,Open,Exists,Sp,I("P"),InMacro,Sp,C("Policy",N(3)),Comma,Sp,
        Forall,Sp,I("W"),InMacro,Sp,Fiber,Comma,Sp,
        C("Identifies",Seq(I("P"),Comma,N(5),Comma,I("JJ"),Comma,I("W"))),Close));
}
