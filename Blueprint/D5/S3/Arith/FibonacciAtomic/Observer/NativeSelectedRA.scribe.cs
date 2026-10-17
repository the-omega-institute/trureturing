using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSelectedRADocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSelectedRA", H("Selected-cut cell machine and root-source support"), Blocks(
            Def("Cell", "Four-bit cells", "The sequence alphabet is Fin 16. Addresses are Boolean words, with false denoting L and true denoting R."),
            Def("rootBytes", "Constant complete root row", "The four cells 0,3,4,5 denote H, semicolon, exterior end and row end. The hole address is empty and its single partition class needs no off-diagonal bit."),
            Def("forkPrefix", "Two-hole exterior", "The eight cells 6,0,1,3,0,2,3,4 denote B, H L semicolon, H R semicolon and exterior end. The next cell is the sole off-diagonal partition bit and the last is row end."),
            Def("leafBytes", "Literal blocking exterior", "The cell for alpha is 7 and that for beta is 8. A literal leaf exterior is followed by exterior end and row end. Its empty hole partition needs no pair bit."),
            Def("Work", "Private cell configuration", "Work contains finite control in Fin 100, the guard address, the comparison operand, the candidate row and three reply latches. All address strings and row cells are explicit finite sequences."),
            Def("emptyWork", "Common private entry configuration", "The guard and operand are empty, the candidate has no cells and each reply latch is absent. Control starts at the root guard Read."),
            Def("State", "Entry, active work and ready boundary", "The common entry contains no source information. Active stores the selected cut bit and Work. Ready stores the cut bit and row alone; it contains no Work, initial reply, attempt count or execution archive."),
            Def("cut", "The selected cut", "True denotes the singleton root address. False denotes the two addresses L and R. The cut bit retained at Ready is the output cut itself."),
            Def("pop", "One-cell retraction", "pop removes the last cell of a finite region, leaving an empty region empty."),
            Def("lastBit", "The last address letter", "lastBit reads the last letter and returns false for an empty word."),
            Def("switch", "Changing the operand base", "switch changes the first operand letter and leaves its relative suffix unchanged. The first letter selects L or R and is protected from relative traversal retraction."),
            Def("go", "Finite control change", "go replaces the finite program counter and preserves every sequence and reply latch."),
            Def("put", "Candidate append", "put appends one row cell and installs the indicated finite control."),
            Def("PrivateInstruction", "Four concrete Read continuations", "Private instruction data contain a literal address and four Work successors, one local Work successor, or private completion. Private completion is not outer Return."),
            Def("localInstruction", "Private local instruction", "This constructor records one local successor."),
            Def("receipt", "Literal Read instruction", "receipt materializes its address and the alpha, beta, branch and absent continuation configurations."),
            Def("privateStep", "Selected rereading acquisition", "The guard follows L after each branch until a leaf. The root cut writes its constant row. The two-child cut writes a literal root leaf or its two marked holes, then compares both hidden subtrees by relative preorder. Equal branches descend; equal leaves advance past completed subtrees; a mismatch appends false. The guard is reread at control 25. A changed reply clears the candidate and private data before retry. Acceptance retracts operand and guard cells, clears every reply latch and hands off the row."),
            Def("follow", "Reply continuation selection", "follow chooses the corresponding one of the four stored Work configurations."),
            Def("lift", "Private continuation and outer control", "Reads and local instructions preserve the selected output cut. Private completion produces a local transition to Ready with the existing row region."),
            Def("step", "One fixed source-blind transition", "Entry Reads the root and selects the root cut exactly for an alpha reply. Active executes privateStep and Ready emits the sole outer Return. No source, epoch, update bound or schedule is an argument of step."),
            Def("selected", "Cut observation for the control invariant", "The proof-side observation is none at Entry and the selected cut bit at Active and Ready."),
            Def("cleanupTiming", "Independent writer bursts during cleanup", "cleanupTiming n sigma contains n local events followed by one Return. Its event at index i has sigma i updates immediately before it. Sigma is a mathematical schedule annotation and is not a producer input."),
            Theorem("cleanup_every_schedule", "Every scheduled cleanup returns the whole ready state", Cleanup(),
                "Cleanup has operand length plus guard length plus six local events. Induction on the two lengths accounts for every cell retraction. Four final events reset the reply latches and hand off the row; two further events leave the exhausted retraction phases. Independent updates change only the source register, so arbitrary finite bursts may precede each local event and the separate Return. The entire terminal cell configuration is Ready q row."),
            Def("World", "Proof-side execution world", "World pairs the observer configuration with the independently updated authentic source register and the external Return flag. Neither the source nor this flag is an argument of step or privateStep."),
            Def("worldEvent", "One actual event", "A writer event applies substitution only to the authentic source. An observer event executes exactly step: a local successor, the authentic reply at its materialized address, or the separate Return. The returned execution world is absorbing."),
            Def("trajectory", "An active execution schedule", "The natural index enumerates actual writer or observer events. Each event acts on the preceding complete world; idle waiting is excluded."),
            Theorem("trajectory_add", "The actual continuation of an event prefix", TrajectoryAdd(),
                "For every event schedule, whole initial world and natural m and k, the prefix of length m plus k is the shifted schedule's prefix of length k from the actual world at m. In the formula shift s m maps i to s applied to m plus i."),
            Def("Progressing", "Every pending observer step executes", "At every active index n where Return has not occurred, some observer event occurs at an index m at least n. No progress is required after Return."),
            Theorem("cleanup_progressing", "Cleanup returns on every progressing schedule", ProgressCleanup(),
                "A progressing pending call has a first observer event after each of its finite prefixes. Before that event only writer updates occur and the private configuration is unchanged. Each local cleanup step therefore executes after a finite writer prefix. Induction on the counted cleanup sequence reaches Ready and its separate Return on every such schedule. No bound on interference, final source or schedule is supplied to the producer; this cleanup conclusion needs no finite-interference premise."),
            Def("rootCandidate", "The root candidate phase", "The root phase appends H, semicolon, exterior end and row end in four successive cell events, after one control event. It preserves its guard and private reply latches."),
            Describe.Lean(DescribeId.Create("selected-ra-post-selection-witness"),
                DeclarationHandle.Create(Prefix+"PostSelectionWitness"), H("Actual post-selection witnesses"),
                StatementSource.FromAuthor(Disp(PostWitness())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The first Read is alpha at invocation alpha. Exactly j independent updates then occur before the quiescent acquisition prefix a. The final guard Read has its authentic leaf reply at the jth iterate of alpha. The displayed cleanup has zero bursts and ends in a separate Return. No guard or prefix is retained in the ready configuration. In the displayed formula zeroSchedule is the constant function with value zero."))), DescribeRole.Definition),
            Theorem("selected_root_support", "Exact root support and the blocked beta witness", Support(),
                "The cut choice persists through every local step, Read and independent update. A root-selected return therefore requires an alpha first reply. No substitution image is alpha, so no update preceded that Read and the invocation source was alpha. The raw history starts with that alpha Read itself, with no preceding update. Conversely, a left-spine induction constructs the guard search on every finite source. Appending the constant root candidate, its validation and cleanup gives a witness after any supplied number j of post-selection updates. A quiescent beta invocation takes the two-address branch and returns the literal beta exterior with no holes. Its root beta leaf blocks both L and R. The same code cannot return any root-selected state from beta, although the semantic root row agrees for every finite source at every epoch."),
            Def("Continues", "A finite stationary prefix", "Continues U c d means that every returning execution from d on U can be preceded by a finite update-free word to give an execution from c on that same source. The prefix is proof-side data and is not retained by the machine."),
            Theorem("guard_search", "A stationary guard reaches an actual leaf", GuardSearch(),
                "The actual read map at p is the complete finite tree T. In the formula guardEntry p is emptyWork with guardPath p, and guardExit g ell is emptyWork with control three, guardPath g and guardReply ell. Left-spine induction produces an alpha or beta reply at its actual materialized address g. A finite update-free prefix reaches control three with this guard address and reply, empty row and operand, and absent comparison latches."),
            Def("pairStart", "Relative comparison entry", "Control is twenty and the operand is L followed by the relative cursor z. All other Work fields are preserved."),
            Def("pairDone", "Relative comparison exit", "Control is twenty seven and the operand is R followed by z. Both comparison latches contain the supplied leaf reply; all other regions are preserved."),
            Def("rightLeafReply", "Rightmost leaf label", "Follow right children in a finite subtree until a leaf, and return its alpha or beta label."),
            Theorem("pair_equal_scan", "An equal stationary subtree scan", EqualScan(),
                "At every relative offset the two materialized base positions read the same supplied finite subtree T. The actual comparison from pairStart finishes at pairDone with the rightmost leaf label of T. Its finite stationary prefix composes with every later legal execution."),
            Theorem("pair_unequal_scan", "An unequal stationary subtree scan", UnequalScan(),
                "The two actual read maps supply different finite subtrees. The comparison reaches control twenty nine while preserving the candidate row, guard address and guard reply. The equality test follows ordered children and reaches the first mismatch after any equal preceding subtree."),
            Theorem("pair_complete", "Completion of a root comparison", CompleteScan(),
                "Starting with the relative cursor empty, the comparison reaches control eight and appends ten exactly when the two supplied actual subtrees are equal, and nine otherwise. The guard address and saved guard reply are preserved."),
            Def("forkRecord", "Complete two-hole row meaning", "The exterior has holes L and R with their full native addresses. The partition contains both diagonal pairs; its bit specifies both off-diagonal memberships, so false retains both disequalities."),
            Theorem("quiescent_two_hole", "Quiescent acquisition of both partition signs", TwoHole(),
                "A structural induction follows the actual relative preorder comparison. Equal branches descend into their left children, advance to the right children and retract completed paths. Equal leaves finish their subtrees. Unequal constructors reach the mismatch phase immediately; equal left subtrees followed by unequal right subtrees do so after the left traversal. The candidate contains exactly the two marked holes and the resulting equality or disequality bit. The same invocation searches its root guard, writes every exterior cell, performs the comparison, validates the saved guard, clears the private regions and Returns from Ready."),
            Paragraph(Text("These statements concern the explicit cell-transition model. They establish root support, actual quiescent acquisition for both cuts and scheduled cleanup. They do not establish all-return correctness of the two-hole comparison, universal finite-interference liveness of acquisition, or a finite-bit realization accounting for binary heads, extents, capacities and permissions. A realization with additional accessible state must include that state and its paid cleanup."))
        )));
    private static DocumentBlock Def(string n,string title,string prose) => Describe.Lean(
        DescribeId.Create("selected-ra-"+n.ToLowerInvariant()),DeclarationHandle.Create(Prefix+n),
        H(title),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),DescribeRole.Definition);
    private static DocumentBlock Theorem(string n,string title,Formula f,string prose) => Describe.Lean(
        DescribeId.Create("selected-ra-"+n.Replace('_','-')),DeclarationHandle.Create(Prefix+n),
        H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    private static Formula TrajectoryAdd() => All("s",Arr(V("Nat"),V("Bool")),All("w",V("World"),
        All("m",V("Nat"),All("k",V("Nat"),EqOf(Call("trajectory",V("s"),V("w"),Add(V("m"),V("k"))),
            Call("trajectory",Call("shift",V("s"),V("m")),Call("trajectory",V("s"),V("w"),V("m")),V("k")))))));
    private static Formula Cleanup()
    {
        Formula count=Add(Add(Length(Call("operand",V("w"))),Length(Call("guardPath",V("w")))),D(6));
        Formula word=Call("expand",Call("cleanupTiming",count,V("sigma")));
        Formula body=Run(Call("active",V("q"),Call("go",D(4,0),V("w"))),V("U"),word,
            Call("ready",V("q"),Call("row",V("w"))));
        return All("q",V("Bool"),All("w",V("Work"),All("sigma",Arr(V("Nat"),V("Nat")),All("U",V("Source"),body))));
    }
    private static Formula ProgressCleanup()
    {
        Formula world=Call("World",Call("active",V("q"),Call("go",D(4,0),V("w"))),V("U"),Call("false"));
        Formula at=Call("trajectory",V("schedule"),world,V("m"));
        Formula body=Imp(Call("Progressing",V("schedule"),world),Some("m",V("Nat"),AndOf(
            EqOf(Call("returned",at),Call("true")),
            EqOf(Call("config",at),Call("ready",V("q"),Call("row",V("w")))))));
        return All("q",V("Bool"),All("w",V("Work"),All("schedule",Arr(V("Nat"),V("Bool")),All("U",V("Source"),body))));
    }
    private static Formula PostWitness()
    {
        Formula validation=Call("observer",Call("read",V("g"),V("ell")));
        Formula cleanup=Call("expand",Call("cleanupTiming",Add(Length(V("g")),D(6)),Call("zeroSchedule")));
        Formula tail=Append(V("a"),Cons(validation,cleanup));
        Formula word=Cons(Call("observer",Call("read",Call("nil"),Call("alpha"))),
            Append(Call("replicate",V("j"),Call("update")),tail));
        Formula clauses=AndOf(NotIn(Call("update"),V("a")),
            OrOf(EqOf(V("ell"),Call("alpha")),EqOf(V("ell"),Call("beta"))),
            EqOf(Call("readout",V("g"),Rho(V("j"),Alpha)),V("ell")),
            Run(Call("entry"),Alpha,word,Ready));
        Formula witness=Some("g",V("Address"),Some("ell",V("Reply"),Some("a",V("Word"),clauses)));
        return All("j",V("Nat"),IffOf(Call("PostSelectionWitness",V("j")),witness));
    }
    private static Formula Support()
    {
        Formula origin=All("u",V("Source"),IffOf(Some("h",V("Word"),Run(Call("entry"),V("u"),V("h"),Ready)),EqOf(V("u"),Alpha)));
        Formula witnesses=All("j",V("Nat"),Call("PostSelectionWitness",V("j")));
        Formula blocker=All("p",V("Address"),Imp(Member(V("p"),Call("cut",Call("false"))),AndOf(
            Call("IsPrefix",Call("nil"),V("p")),NeOf(V("p"),Call("nil")),
            EqOf(Call("subtree",V("p"),Beta),Call("none")))));
        Formula beta=Some("h",V("Word"),AndOf(NotIn(Call("update"),V("h")),
            Run(Call("entry"),Beta,V("h"),Call("ready",Call("false"),Call("leafBytes",Call("false")))),
            EqOf(Call("literalRecord",Call("cut",Call("false")),Beta),
                Call("pair",Call("of",Call("inl",Call("false"))),Call("emptyset"))),blocker));
        Formula excluded=All("h",V("Word"),All("row",Call("List",V("Cell")),
            Not(Run(Call("entry"),Beta,V("h"),Call("ready",Call("true"),V("row"))))));
        Formula compatible=All("u",V("Source"),All("j",V("Nat"),EqOf(
            Call("literalRecord",Call("singleton",Call("nil")),Rho(V("j"),V("u"))),Call("rootLabel"))));
        Formula firstRead=All("u",V("Source"),All("h",V("Word"),All("row",Call("List",V("Cell")),
            Imp(Run(Call("entry"),V("u"),V("h"),Call("ready",Call("true"),V("row"))),
                Some("tail",V("Word"),EqOf(V("h"),Cons(
                    Call("observer",Call("read",Call("nil"),Call("alpha"))),V("tail"))))))));
        return AndOf(origin,witnesses,beta,excluded,compatible,firstRead);
    }
    private static Formula TwoHole()
    {
        Formula bit=Call("ite",EqOf(V("A"),V("B")),D(1,0),D(9));
        Formula row=Append(Call("forkPrefix"),Cons(bit,Cons(D(5),Call("nil"))));
        Formula body=Some("h",V("Word"),AndOf(NotIn(Call("update"),V("h")),
            Run(Call("entry"),Call("mul",V("A"),V("B")),V("h"),Call("ready",Call("false"),row)),
            EqOf(Call("literalRecord",Call("cut",Call("false")),Call("mul",V("A"),V("B"))),
                Call("forkRecord",Call("decide",EqOf(V("A"),V("B")))))));
        return All("A",V("Source"),All("B",V("Source"),body));
    }
    private static Formula ScanRead(bool right, Formula tree) => All("a",V("Address"),EqOf(
        Call("readout",Cons(Call(right?"true":"false"),Append(V("z"),V("a"))),V("U")),
        Call("readout",V("a"),tree)));
    private static Formula Active(Formula w) => Call("active",Call("false"),w);
    private static Formula EqualScan()
    {
        Formula end=Active(Call("pairDone",V("w"),V("z"),Call("rightLeafReply",V("T"))));
        Formula body=Imp(ScanRead(false,V("T")),Imp(ScanRead(true,V("T")),
            Call("Continues",V("U"),Active(Call("pairStart",V("w"),V("z"))),end)));
        return All("U",V("Source"),All("T",V("Source"),All("w",V("Work"),All("z",V("Address"),body))));
    }
    private static Formula GuardSearch()
    {
        Formula observed=All("z",V("Address"),EqOf(Call("readout",Append(V("p"),V("z")),V("U")),Call("readout",V("z"),V("T"))));
        Formula start=Call("active",V("q"),Call("guardEntry",V("p")));
        Formula end=Call("active",V("q"),Call("guardExit",V("g"),V("ell")));
        Formula leaf=OrOf(EqOf(V("ell"),Call("alpha")),EqOf(V("ell"),Call("beta")));
        Formula body=Imp(observed,Some("g",V("Address"),Some("ell",V("Reply"),AndOf(leaf,
            EqOf(Call("readout",V("g"),V("U")),V("ell")),Call("Continues",V("U"),start,end)))));
        return All("U",V("Source"),All("T",V("Source"),All("q",V("Bool"),All("p",V("Address"),body))));
    }
    private static Formula ScanOutput(Formula control, Formula row, Formula start) => Some("v",V("Work"),AndOf(
        EqOf(Call("pc",V("v")),control),EqOf(Call("row",V("v")),row),
        EqOf(Call("guardPath",V("v")),Call("guardPath",V("w"))),
        EqOf(Call("guardReply",V("v")),Call("guardReply",V("w"))),
        Call("Continues",V("U"),Active(start),Active(V("v")))));
    private static Formula UnequalScan()
    {
        Formula body=Imp(ScanRead(false,V("A")),Imp(ScanRead(true,V("B")),Imp(NeOf(V("A"),V("B")),
            ScanOutput(D(2,9),Call("row",V("w")),Call("pairStart",V("w"),V("z"))))));
        return All("U",V("Source"),All("A",V("Source"),All("B",V("Source"),
            All("w",V("Work"),All("z",V("Address"),body)))));
    }
    private static Formula CompleteScan()
    {
        Formula left=All("a",V("Address"),EqOf(Call("readout",Cons(Call("false"),V("a")),V("U")),Call("readout",V("a"),V("A"))));
        Formula right=All("a",V("Address"),EqOf(Call("readout",Cons(Call("true"),V("a")),V("U")),Call("readout",V("a"),V("B"))));
        Formula bit=Call("ite",EqOf(V("A"),V("B")),D(1,0),D(9));
        Formula body=Imp(left,Imp(right,ScanOutput(D(8),Append(Call("row",V("w")),Cons(bit,Call("nil"))),
            Call("pairStart",V("w"),Call("nil")))));
        return All("U",V("Source"),All("A",V("Source"),All("B",V("Source"),All("w",V("Work"),body))));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Call(string n,params Formula[] a)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula NeOf(Formula a,Formula b)=>Seq(a,Sp,Neq,Sp,b);
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula Not(Formula a)=>Seq(Neg,Sp,Par(a));
    private static Formula Member(Formula a,Formula b)=>Seq(a,Sp,InMacro,Sp,b);
    private static Formula NotIn(Formula a,Formula b)=>Not(Member(a,b));
    private static Formula OrOf(Formula a,Formula b)=>Seq(Par(a),Sp,Lor,Sp,Par(b));
    private static Formula AndOf(params Formula[] a)=>a.Length==1?a[0]:Seq(Par(a[0]),Sp,Land,Sp,Par(AndOf(a.Skip(1).ToArray())));
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula Add(Formula a,Formula b)=>Seq(a,Sp,Plus,Sp,b);
    private static Formula Length(Formula a)=>Call("length",a);
    private static Formula Append(Formula a,Formula b)=>Call("append",a,b);
    private static Formula Cons(Formula a,Formula b)=>Call("cons",a,b);
    private static Formula Rho(Formula n,Formula u)=>Call("iterate",Call("substitution"),n,u);
    private static Formula Run(Formula c,Formula u,Formula w,Formula b)=>Call("Run",Call("step"),c,u,w,b);
    private static Formula Alpha=>Call("of",Call("true"));
    private static Formula Beta=>Call("of",Call("false"));
    private static Formula Ready=>Call("ready",Call("true"),Call("rootBytes"));
}
