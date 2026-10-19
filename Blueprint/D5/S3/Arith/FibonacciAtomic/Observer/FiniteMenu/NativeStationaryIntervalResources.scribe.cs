using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu;
internal sealed class NativeStationaryIntervalResourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeStationaryIntervalResources.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(s))),[..a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Leftrightarrow,Sp,Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula RecodeStatement() => All("U",V("Nat"),Imp(LeOf(D(1),V("U")),
        All("p",V("Address"),Some("q",V("Address"),Some("phi",Call("Function",V("Reply"),V("Reply")),
        And(LeOf(Call("length",V("q")),Call("min",Call("length",V("p")),Call("div",Seq(V("U"),Minus,D(1)),D(2)))),
        All("n",V("Nat"),Imp(LeOf(V("n"),V("U")),EqOf(Call("readout",V("p"),Call("T",V("n"))),
            Call("phi",Call("readout",V("q"),Call("T",V("n")))))))))))));
    private static Formula CapacityStatement() => All("L",V("Nat"),All("U",V("Nat"),
        Imp(LeOf(V("L"),V("U")),All("k",V("Nat"),IffOf(
            Some("d",Call("Dialogue",V("Nat")),Call("Identifies",V("d"),V("L"),V("U"),V("k"))),
            LeOf(V("kmin"),V("k")))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp call capacity for a stationary actual Fibonacci source and bounded literal recoding.",
        H("Stationary interval resources"),Blocks(
            Paragraph(Text("The unknown input is one fixed actual source T(n), obtained by applying substitution n times to alpha. The public endpoints satisfy 0 <= L <= U, and the target is the integer n. A reader begins at one common source-blind control state. It may perform silent local computation and paid literal reads, including a paid empty-word read. It performs no substitution or reset. Every answer is the actual four-valued readout of the same source; an address, a numeric age, a clock and a prior transcript are not supplied for free.")),
            Paragraph(Text("A nonempty address ending in R has an absent tail, one alpha age, one beta age and a branch tail. A final L removes the alpha age. At the root, ages zero and one return alpha and beta and every later age returns branch. The public guarded source geometry supplies these facts. The capacities are C(k)=3*2^k-2 and A(0)=1, A(k)=3*2^k-3 for positive k. A finite candidate set separated within k calls has at most C(k) elements. If it contains both zero and one it has at most A(k) elements. The latter pair remains in the absent child of every nonempty query, while the root has only three actual successors.")),
            Paragraph(Text("The capacity proof partitions a candidate set by the first actual reply. Each leaf-reply cell contains at most one age. Induction applies to the other two cells, retaining each original source in every continuation. At a zero-origin cell the zero-call and one-call cases are handled separately. An arbitrary stationary serial reader that terminates within a uniform read budget on the finite interval can be unrolled into a finite literal dialogue. This removes silent steps without changing its output, complete reply word or call count.")),
            Describe.Lean(DescribeId.Create("native-stationary-interval-capacity"),
                DeclarationHandle.Create(Prefix+"native_interval_capacity"),H("Exact calls and fixed-source failure"),
                StatementSource.FromAuthor(Disp(CapacityStatement())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Here kmin is minimumCalls(L,U). It is zero for a singleton. Otherwise it is the ceiling of log base two of (N+2)/3 when L is positive and of (N+3)/3 when L is zero, where N=U-L+1. Equivalently feasibility is N <= C(k), or N <= A(k) at zero. The theorem gives both the arbitrary stationary serial interface and the finite-dialogue interface, together with a finite attaining dialogue. For any source-total stationary reader with a smaller call budget there are two different admitted fixed ages producing one common complete chronological trace and one common terminal output, so the reader cannot identify both.")),
                    Paragraph(Text("The positive attaining family is indexed by r and covers [l,l+3r]. Splitting r-1 as evenly as possible gives two recursive tails and two numeric halts. The zero-origin family covers [0,3r-1]; its final zero branch uses a paid root query. If r < 2^k these balanced trees take at most k calls on every admitted age. Restriction to a public interval and the real logarithm ceiling equivalence give the exact minimum, including all singleton boundaries."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-stationary-bounded-query-recode"),
                DeclarationHandle.Create(Prefix+"bounded_query_recode"),H("One paid bounded replacement"),
                StatementSource.FromAuthor(Disp(RecodeStatement())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("For every public U >= 1 and every literal p, one fixed replacement q and one total reply decoder work on all actual ages from zero through U. The replacement length is at most both length(p) and floor((U-1)/2). Empty q is still one paid actual read. Short words are retained. Other words first reduce to a shortest right-ending threshold. If that threshold is too long, the final public right spine separates the last three possible ages individually and merges only ages on which the old query is absent. For U <= 2 a root read supplies those individual ages directly."))),DescribeRole.Theorem)
            ,Describe.Lean(DescribeId.Create("native-stationary-joint-optimum"),
                DeclarationHandle.Create(Prefix+"native_interval_joint_optimum"),H("Joint call and peak feasibility"),
                StatementSource.FromAuthor(Disp(JointStatement())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("SerialBudgets means that every admitted actual source terminates at its correct numeric output with at most k reads and every actually submitted literal has length at most d. The model permits arbitrary source-blind silent computation. Feasibility is exactly minimumCalls(L,U) <= k together with either a singleton interval or U <= 2*d+2. One finite dialogue identifies the interval at minimumCalls and has every installed literal bounded by zero for a singleton, or floor((U-1)/2) otherwise.")),
                    Paragraph(Text("For the lower bound, if U > 2*d+2, both actual sources with ages U-1 and U return branch to every allowed literal. Stationarity transports the complete first run to the second fixed source, giving the same output at two different required ages. For attainment, replace every query of a minimum-call dialogue by its bounded literal and decode the reply before choosing the old successor. The actual result and number of paid calls are unchanged. A replacement by the empty word still contributes one read. This gives one reader attaining both minima; their worst cases need not use the same age."))),DescribeRole.Theorem)
        )));
    private static Formula JointStatement() => All("L",V("Nat"),All("U",V("Nat"),
        Imp(LeOf(V("L"),V("U")),All("k",V("Nat"),All("d",V("Nat"),IffOf(
            Call("StationaryBudgetFeasible",V("L"),V("U"),V("k"),V("d")),
            And(LeOf(Call("minimumCalls",V("L"),V("U")),V("k")),
                Call("SingletonOrPeak",V("L"),V("U"),V("d")))))))));
}
